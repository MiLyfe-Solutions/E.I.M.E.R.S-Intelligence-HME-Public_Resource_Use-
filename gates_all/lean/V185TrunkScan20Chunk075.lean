import V185TrunkScan20Chunk074

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental

namespace V185TrunkScan20Incremental

def tailWord_457267 : List Nat := [1, 1, 1, 2, 4, 2, 2, 4, 3]
def baseStart_457267 : Nat := 118140960795 + 457267 * 2 ^ 59
def prefixEnd_457267 : Nat := 4983230072969 + 3 ^ 40 * 457267 * 2
def baseEnd_457267 : Nat := 208709118612949043964065

theorem tailTrace_457267 : CollatzResearch.WordTrace tailWord_457267 prefixEnd_457267 208709118612949043964065 := by
  unfold tailWord_457267
  simp only [CollatzResearch.WordTrace]
  refine ⟨16677897634407228831250055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11118598422938152554166703 16677897634407228831250055)
  ·
    refine ⟨25016846451610843246875083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16677897634407228831250055 25016846451610843246875083)
    ·
      refine ⟨37525269677416264870312625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25016846451610843246875083 37525269677416264870312625)
      ·
        refine ⟨28143952258062198652734469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37525269677416264870312625 28143952258062198652734469)
        ·
          refine ⟨5276991048386662247387713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28143952258062198652734469 5276991048386662247387713)
          ·
            refine ⟨3957743286289996685540785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5276991048386662247387713 3957743286289996685540785)
            ·
              refine ⟨2968307464717497514155589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3957743286289996685540785 2968307464717497514155589)
              ·
                refine ⟨556557649634530783904173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2968307464717497514155589 556557649634530783904173)
                ·
                  refine ⟨208709118612949043964065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 556557649634530783904173 208709118612949043964065)
                  ·
                    rfl

theorem cell20_457267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 2, 4, 3].length) (baseStart_457267 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_457267 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_457267 prefixEnd_457267 := by exact prefixLift 457267
  have htrace : WordTrace (prefixWord ++ tailWord_457267) baseStart_457267 baseEnd_457267 := by
    simpa [prefixWord, tailWord_457267, baseEnd_457267] using wordTrace_append hprefix tailTrace_457267
  have hstable : (prefixWord ++ tailWord_457267).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_457267).length < 2 ^ (prefixWord ++ tailWord_457267).sum := by decide
  have hdescent : baseEnd_457267 < baseStart_457267 := by decide
  rcases family_descends (prefixWord ++ tailWord_457267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_457270 : List Nat := [5, 1, 2, 1, 2, 1, 3, 1, 4]
def baseStart_457270 : Nat := 118140960795 + 457270 * 2 ^ 59
def prefixEnd_457270 : Nat := 4983230072969 + 3 ^ 40 * 457270 * 2
def baseEnd_457270 : Nat := 208710487894694366864053

theorem tailTrace_457270 : CollatzResearch.WordTrace tailWord_457270 prefixEnd_457270 208710487894694366864053 := by
  unfold tailWord_457270
  simp only [CollatzResearch.WordTrace]
  refine ⟨1042375440837272521475579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 11118671368930906895739509 1042375440837272521475579)
  ·
    refine ⟨1563563161255908782213369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1042375440837272521475579 1563563161255908782213369)
    ·
      refine ⟨1172672370941931586660027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1563563161255908782213369 1172672370941931586660027)
      ·
        refine ⟨1759008556412897379990041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1172672370941931586660027 1759008556412897379990041)
        ·
          refine ⟨1319256417309673034992531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1759008556412897379990041 1319256417309673034992531)
          ·
            refine ⟨1978884625964509552488797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1319256417309673034992531 1978884625964509552488797)
            ·
              refine ⟨742081734736691082183299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1978884625964509552488797 742081734736691082183299)
              ·
                refine ⟨1113122602105036623274949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 742081734736691082183299 1113122602105036623274949)
                ·
                  refine ⟨208710487894694366864053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1113122602105036623274949 208710487894694366864053)
                  ·
                    rfl

theorem cell20_457270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 3, 1, 4].length) (baseStart_457270 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_457270 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_457270 prefixEnd_457270 := by exact prefixLift 457270
  have htrace : WordTrace (prefixWord ++ tailWord_457270) baseStart_457270 baseEnd_457270 := by
    simpa [prefixWord, tailWord_457270, baseEnd_457270] using wordTrace_append hprefix tailTrace_457270
  have hstable : (prefixWord ++ tailWord_457270).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_457270).length < 2 ^ (prefixWord ++ tailWord_457270).sum := by decide
  have hdescent : baseEnd_457270 < baseStart_457270 := by decide
  rcases family_descends (prefixWord ++ tailWord_457270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_457322 : List Nat := [3, 1, 3, 2, 1, 1, 4, 2, 3]
def baseStart_457322 : Nat := 118140960795 + 457322 * 2 ^ 59
def prefixEnd_457322 : Nat := 4983230072969 + 3 ^ 40 * 457322 * 2
def baseEnd_457322 : Nat := 208734222111613297130507

theorem tailTrace_457322 : CollatzResearch.WordTrace tailWord_457322 prefixEnd_457322 208734222111613297130507 := by
  unfold tailWord_457322
  simp only [CollatzResearch.WordTrace]
  refine ⟨4169975912301993306125555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11119935766138648816334813 4169975912301993306125555)
  ·
    refine ⟨6254963868452989959188333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4169975912301993306125555 6254963868452989959188333)
    ·
      refine ⟨2345611450669871234695625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6254963868452989959188333 2345611450669871234695625)
      ·
        refine ⟨1759208588002403426021719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2345611450669871234695625 1759208588002403426021719)
        ·
          refine ⟨2638812882003605139032579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1759208588002403426021719 2638812882003605139032579)
          ·
            refine ⟨3958219323005407708548869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2638812882003605139032579 3958219323005407708548869)
            ·
              refine ⟨742166123063513945352913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3958219323005407708548869 742166123063513945352913)
              ·
                refine ⟨556624592297635459014685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 742166123063513945352913 556624592297635459014685)
                ·
                  refine ⟨208734222111613297130507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 556624592297635459014685 208734222111613297130507)
                  ·
                    rfl

theorem cell20_457322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 4, 2, 3].length) (baseStart_457322 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_457322 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_457322 prefixEnd_457322 := by exact prefixLift 457322
  have htrace : WordTrace (prefixWord ++ tailWord_457322) baseStart_457322 baseEnd_457322 := by
    simpa [prefixWord, tailWord_457322, baseEnd_457322] using wordTrace_append hprefix tailTrace_457322
  have hstable : (prefixWord ++ tailWord_457322).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_457322).length < 2 ^ (prefixWord ++ tailWord_457322).sum := by decide
  have hdescent : baseEnd_457322 < baseStart_457322 := by decide
  rcases family_descends (prefixWord ++ tailWord_457322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_457325 : List Nat := [1, 5, 1, 1, 3, 1, 4, 2, 2]
def baseStart_457325 : Nat := 118140960795 + 457325 * 2 ^ 59
def prefixEnd_457325 : Nat := 4983230072969 + 3 ^ 40 * 457325 * 2
def baseEnd_457325 : Nat := 208735591393358620030495

theorem tailTrace_457325 : CollatzResearch.WordTrace tailWord_457325 prefixEnd_457325 208735591393358620030495 := by
  unfold tailWord_457325
  simp only [CollatzResearch.WordTrace]
  refine ⟨16680013068197104736861429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11120008712131403157907619 16680013068197104736861429)
  ·
    refine ⟨1563751225143478569080759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 16680013068197104736861429 1563751225143478569080759)
    ·
      refine ⟨2345626837715217853621139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1563751225143478569080759 2345626837715217853621139)
      ·
        refine ⟨3518440256572826780431709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2345626837715217853621139 3518440256572826780431709)
        ·
          refine ⟨1319415096214810042661891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3518440256572826780431709 1319415096214810042661891)
          ·
            refine ⟨1979122644322215063992837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1319415096214810042661891 1979122644322215063992837)
            ·
              refine ⟨371085495810415324498657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1979122644322215063992837 371085495810415324498657)
              ·
                refine ⟨278314121857811493373993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 371085495810415324498657 278314121857811493373993)
                ·
                  refine ⟨208735591393358620030495, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 278314121857811493373993 208735591393358620030495)
                  ·
                    rfl

theorem cell20_457325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 4, 2, 2].length) (baseStart_457325 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_457325 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_457325 prefixEnd_457325 := by exact prefixLift 457325
  have htrace : WordTrace (prefixWord ++ tailWord_457325) baseStart_457325 baseEnd_457325 := by
    simpa [prefixWord, tailWord_457325, baseEnd_457325] using wordTrace_append hprefix tailTrace_457325
  have hstable : (prefixWord ++ tailWord_457325).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_457325).length < 2 ^ (prefixWord ++ tailWord_457325).sum := by decide
  have hdescent : baseEnd_457325 < baseStart_457325 := by decide
  rcases family_descends (prefixWord ++ tailWord_457325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_457374 : List Nat := [4, 3, 1, 1, 1, 1, 9]
def baseStart_457374 : Nat := 118140960795 + 457374 * 2 ^ 59
def prefixEnd_457374 : Nat := 4983230072969 + 3 ^ 40 * 457374 * 2
def baseEnd_457374 : Nat := 23195328480948025266329

theorem tailTrace_457374 : CollatzResearch.WordTrace tailWord_457374 prefixEnd_457374 23195328480948025266329 := by
  unfold tailWord_457374
  simp only [CollatzResearch.WordTrace]
  refine ⟨2085225030627448263174397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11121200163346390736930117 2085225030627448263174397)
  ·
    refine ⟨781959386485293098690399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2085225030627448263174397 781959386485293098690399)
    ·
      refine ⟨1172939079727939648035599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 781959386485293098690399 1172939079727939648035599)
      ·
        refine ⟨1759408619591909472053399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1172939079727939648035599 1759408619591909472053399)
        ·
          refine ⟨2639112929387864208080099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1759408619591909472053399 2639112929387864208080099)
          ·
            refine ⟨3958669394081796312120149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2639112929387864208080099 3958669394081796312120149)
            ·
              refine ⟨23195328480948025266329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 3958669394081796312120149 23195328480948025266329)
              ·
                rfl

theorem cell20_457374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 9].length) (baseStart_457374 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_457374 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_457374 prefixEnd_457374 := by exact prefixLift 457374
  have htrace : WordTrace (prefixWord ++ tailWord_457374) baseStart_457374 baseEnd_457374 := by
    simpa [prefixWord, tailWord_457374, baseEnd_457374] using wordTrace_append hprefix tailTrace_457374
  have hstable : (prefixWord ++ tailWord_457374).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_457374).length < 2 ^ (prefixWord ++ tailWord_457374).sum := by decide
  have hdescent : baseEnd_457374 < baseStart_457374 := by decide
  rcases family_descends (prefixWord ++ tailWord_457374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_457377 : List Nat := [1, 2, 3, 3, 3, 2, 1, 2, 3]
def baseStart_457377 : Nat := 118140960795 + 457377 * 2 ^ 59
def prefixEnd_457377 : Nat := 4983230072969 + 3 ^ 40 * 457377 * 2
def baseEnd_457377 : Nat := 208759325610277550296949

theorem tailTrace_457377 : CollatzResearch.WordTrace tailWord_457377 prefixEnd_457377 208759325610277550296949 := by
  unfold tailWord_457377
  simp only [CollatzResearch.WordTrace]
  refine ⟨16681909664008717617754385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11121273109339145078502923 16681909664008717617754385)
  ·
    refine ⟨12511432248006538213315789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16681909664008717617754385 12511432248006538213315789)
    ·
      refine ⟨4691787093002451829993421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12511432248006538213315789 4691787093002451829993421)
      ·
        refine ⟨1759420159875919436247533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4691787093002451829993421 1759420159875919436247533)
        ·
          refine ⟨659782559953469788592825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1759420159875919436247533 659782559953469788592825)
          ·
            refine ⟨494836919965102341444619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 659782559953469788592825 494836919965102341444619)
            ·
              refine ⟨742255379947653512166929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 494836919965102341444619 742255379947653512166929)
              ·
                refine ⟨556691534960740134125197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 742255379947653512166929 556691534960740134125197)
                ·
                  refine ⟨208759325610277550296949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 556691534960740134125197 208759325610277550296949)
                  ·
                    rfl

theorem cell20_457377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 2, 1, 2, 3].length) (baseStart_457377 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_457377 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_457377 prefixEnd_457377 := by exact prefixLift 457377
  have htrace : WordTrace (prefixWord ++ tailWord_457377) baseStart_457377 baseEnd_457377 := by
    simpa [prefixWord, tailWord_457377, baseEnd_457377] using wordTrace_append hprefix tailTrace_457377
  have hstable : (prefixWord ++ tailWord_457377).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_457377).length < 2 ^ (prefixWord ++ tailWord_457377).sum := by decide
  have hdescent : baseEnd_457377 < baseStart_457377 := by decide
  rcases family_descends (prefixWord ++ tailWord_457377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_457412 : List Nat := [2, 3, 3, 1, 1, 3, 1, 6]
def baseStart_457412 : Nat := 118140960795 + 457412 * 2 ^ 59
def prefixEnd_457412 : Nat := 4983230072969 + 3 ^ 40 * 457412 * 2
def baseEnd_457412 : Nat := 69591766854657661376713

theorem tailTrace_457412 : CollatzResearch.WordTrace tailWord_457412 prefixEnd_457412 69591766854657661376713 := by
  unfold tailWord_457412
  simp only [CollatzResearch.WordTrace]
  refine ⟨8341593109440959297639245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11122124145921279063518993 8341593109440959297639245)
  ·
    refine ⟨3128097416040359736614717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8341593109440959297639245 3128097416040359736614717)
    ·
      refine ⟨1173036531015134901230519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3128097416040359736614717 1173036531015134901230519)
      ·
        refine ⟨1759554796522702351845779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1173036531015134901230519 1759554796522702351845779)
        ·
          refine ⟨2639332194784053527768669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1759554796522702351845779 2639332194784053527768669)
          ·
            refine ⟨989749573044020072913251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2639332194784053527768669 989749573044020072913251)
            ·
              refine ⟨1484624359566030109369877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 989749573044020072913251 1484624359566030109369877)
              ·
                refine ⟨69591766854657661376713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1484624359566030109369877 69591766854657661376713)
                ·
                  rfl

theorem cell20_457412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 3, 1, 6].length) (baseStart_457412 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_457412 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_457412 prefixEnd_457412 := by exact prefixLift 457412
  have htrace : WordTrace (prefixWord ++ tailWord_457412) baseStart_457412 baseEnd_457412 := by
    simpa [prefixWord, tailWord_457412, baseEnd_457412] using wordTrace_append hprefix tailTrace_457412
  have hstable : (prefixWord ++ tailWord_457412).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_457412).length < 2 ^ (prefixWord ++ tailWord_457412).sum := by decide
  have hdescent : baseEnd_457412 < baseStart_457412 := by decide
  rcases family_descends (prefixWord ++ tailWord_457412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_457414 : List Nat := [6, 1, 2, 1, 3, 1, 1, 3, 2]
def baseStart_457414 : Nat := 118140960795 + 457414 * 2 ^ 59
def prefixEnd_457414 : Nat := 4983230072969 + 3 ^ 40 * 457414 * 2
def baseEnd_457414 : Nat := 208776213418469866063465

theorem tailTrace_457414 : CollatzResearch.WordTrace tailWord_457414 prefixEnd_457414 208776213418469866063465 := by
  unfold tailWord_457414
  simp only [CollatzResearch.WordTrace]
  refine ⟨521351848902333529276603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 11122172776583115291234197 521351848902333529276603)
  ·
    refine ⟨782027773353500293914905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 521351848902333529276603 782027773353500293914905)
    ·
      refine ⟨586520830015125220436179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 782027773353500293914905 586520830015125220436179)
      ·
        refine ⟨879781245022687830654269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 586520830015125220436179 879781245022687830654269)
        ·
          refine ⟨329917966883507936495351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 879781245022687830654269 329917966883507936495351)
          ·
            refine ⟨494876950325261904743027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 329917966883507936495351 494876950325261904743027)
            ·
              refine ⟨742315425487892857114541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 494876950325261904743027 742315425487892857114541)
              ·
                refine ⟨278368284557959821417953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 742315425487892857114541 278368284557959821417953)
                ·
                  refine ⟨208776213418469866063465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 278368284557959821417953 208776213418469866063465)
                  ·
                    rfl

theorem cell20_457414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 3, 1, 1, 3, 2].length) (baseStart_457414 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_457414 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_457414 prefixEnd_457414 := by exact prefixLift 457414
  have htrace : WordTrace (prefixWord ++ tailWord_457414) baseStart_457414 baseEnd_457414 := by
    simpa [prefixWord, tailWord_457414, baseEnd_457414] using wordTrace_append hprefix tailTrace_457414
  have hstable : (prefixWord ++ tailWord_457414).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_457414).length < 2 ^ (prefixWord ++ tailWord_457414).sum := by decide
  have hdescent : baseEnd_457414 < baseStart_457414 := by decide
  rcases family_descends (prefixWord ++ tailWord_457414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_457422 : List Nat := [4, 1, 1, 1, 3, 2, 3, 3, 2]
def baseStart_457422 : Nat := 118140960795 + 457422 * 2 ^ 59
def prefixEnd_457422 : Nat := 4983230072969 + 3 ^ 40 * 457422 * 2
def baseEnd_457422 : Nat := 208779864836457393796765

theorem tailTrace_457422 : CollatzResearch.WordTrace tailWord_457422 prefixEnd_457422 208779864836457393796765 := by
  unfold tailWord_457422
  simp only [CollatzResearch.WordTrace]
  refine ⟨2085443868605711287892815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11122367299230460202095013 2085443868605711287892815)
  ·
    refine ⟨3128165802908566931839223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2085443868605711287892815 3128165802908566931839223)
    ·
      refine ⟨4692248704362850397758835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3128165802908566931839223 4692248704362850397758835)
      ·
        refine ⟨7038373056544275596638253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4692248704362850397758835 7038373056544275596638253)
        ·
          refine ⟨2639389896204103348739345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7038373056544275596638253 2639389896204103348739345)
          ·
            refine ⟨1979542422153077511554509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2639389896204103348739345 1979542422153077511554509)
            ·
              refine ⟨742328408307404066832941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1979542422153077511554509 742328408307404066832941)
              ·
                refine ⟨278373153115276525062353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 742328408307404066832941 278373153115276525062353)
                ·
                  refine ⟨208779864836457393796765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 278373153115276525062353 208779864836457393796765)
                  ·
                    rfl

theorem cell20_457422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 3, 3, 2].length) (baseStart_457422 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_457422 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_457422 prefixEnd_457422 := by exact prefixLift 457422
  have htrace : WordTrace (prefixWord ++ tailWord_457422) baseStart_457422 baseEnd_457422 := by
    simpa [prefixWord, tailWord_457422, baseEnd_457422] using wordTrace_append hprefix tailTrace_457422
  have hstable : (prefixWord ++ tailWord_457422).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_457422).length < 2 ^ (prefixWord ++ tailWord_457422).sum := by decide
  have hdescent : baseEnd_457422 < baseStart_457422 := by decide
  rcases family_descends (prefixWord ++ tailWord_457422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_457429 : List Nat := [1, 3, 2, 5, 1, 2, 6]
def baseStart_457429 : Nat := 118140960795 + 457429 * 2 ^ 59
def prefixEnd_457429 : Nat := 4983230072969 + 3 ^ 40 * 457429 * 2
def baseEnd_457429 : Nat := 23198117758577386729267

theorem tailTrace_457429 : CollatzResearch.WordTrace tailWord_457429 prefixEnd_457429 23198117758577386729267 := by
  unfold tailWord_457429
  simp only [CollatzResearch.WordTrace]
  refine ⟨16683806259820330498647341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11122537506546886999098227 16683806259820330498647341)
  ·
    refine ⟨6256427347432623936992753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16683806259820330498647341 6256427347432623936992753)
    ·
      refine ⟨4692320510574467952744565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6256427347432623936992753 4692320510574467952744565)
      ·
        refine ⟨439905047866356370569803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 4692320510574467952744565 439905047866356370569803)
        ·
          refine ⟨659857571799534555854705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 439905047866356370569803 659857571799534555854705)
          ·
            refine ⟨494893178849650916891029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 659857571799534555854705 494893178849650916891029)
            ·
              refine ⟨23198117758577386729267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 494893178849650916891029 23198117758577386729267)
              ·
                rfl

theorem cell20_457429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 2, 6].length) (baseStart_457429 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_457429 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_457429 prefixEnd_457429 := by exact prefixLift 457429
  have htrace : WordTrace (prefixWord ++ tailWord_457429) baseStart_457429 baseEnd_457429 := by
    simpa [prefixWord, tailWord_457429, baseEnd_457429] using wordTrace_append hprefix tailTrace_457429
  have hstable : (prefixWord ++ tailWord_457429).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_457429).length < 2 ^ (prefixWord ++ tailWord_457429).sum := by decide
  have hdescent : baseEnd_457429 < baseStart_457429 := by decide
  rcases family_descends (prefixWord ++ tailWord_457429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_457436 : List Nat := [2, 2, 5, 1, 1, 1, 2, 1, 5]
def baseStart_457436 : Nat := 118140960795 + 457436 * 2 ^ 59
def prefixEnd_457436 : Nat := 4983230072969 + 3 ^ 40 * 457436 * 2
def baseEnd_457436 : Nat := 208786254817935567330041

theorem tailTrace_457436 : CollatzResearch.WordTrace tailWord_457436 prefixEnd_457436 208786254817935567330041 := by
  unfold tailWord_457436
  simp only [CollatzResearch.WordTrace]
  refine ⟨8342030785397485347076081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11122707713863313796101441 8342030785397485347076081)
  ·
    refine ⟨6256523089048114010307061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8342030785397485347076081 6256523089048114010307061)
    ·
      refine ⟨586549039598260688466287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 6256523089048114010307061 586549039598260688466287)
      ·
        refine ⟨879823559397391032699431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 586549039598260688466287 879823559397391032699431)
        ·
          refine ⟨1319735339096086549049147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 879823559397391032699431 1319735339096086549049147)
          ·
            refine ⟨1979603008644129823573721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1319735339096086549049147 1979603008644129823573721)
            ·
              refine ⟨1484702256483097367680291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1979603008644129823573721 1484702256483097367680291)
              ·
                refine ⟨2227053384724646051520437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1484702256483097367680291 2227053384724646051520437)
                ·
                  refine ⟨208786254817935567330041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2227053384724646051520437 208786254817935567330041)
                  ·
                    rfl

theorem cell20_457436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 2, 1, 5].length) (baseStart_457436 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_457436 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_457436 prefixEnd_457436 := by exact prefixLift 457436
  have htrace : WordTrace (prefixWord ++ tailWord_457436) baseStart_457436 baseEnd_457436 := by
    simpa [prefixWord, tailWord_457436, baseEnd_457436] using wordTrace_append hprefix tailTrace_457436
  have hstable : (prefixWord ++ tailWord_457436).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_457436).length < 2 ^ (prefixWord ++ tailWord_457436).sum := by decide
  have hdescent : baseEnd_457436 < baseStart_457436 := by decide
  rcases family_descends (prefixWord ++ tailWord_457436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_457443 : List Nat := [1, 1, 1, 7, 1, 1, 3, 1, 4]
def baseStart_457443 : Nat := 118140960795 + 457443 * 2 ^ 59
def prefixEnd_457443 : Nat := 4983230072969 + 3 ^ 40 * 457443 * 2
def baseEnd_457443 : Nat := 208789449808674654096679

theorem tailTrace_457443 : CollatzResearch.WordTrace tailWord_457443 prefixEnd_457443 208789449808674654096679 := by
  unfold tailWord_457443
  simp only [CollatzResearch.WordTrace]
  refine ⟨16684316881769610889656983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11122877921179740593104655 16684316881769610889656983)
  ·
    refine ⟨25026475322654416334485475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16684316881769610889656983 25026475322654416334485475)
    ·
      refine ⟨37539712983981624501728213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25026475322654416334485475 37539712983981624501728213)
      ·
        refine ⟨879837023062069324259255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 37539712983981624501728213 879837023062069324259255)
        ·
          refine ⟨1319755534593103986388883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 879837023062069324259255 1319755534593103986388883)
          ·
            refine ⟨1979633301889655979583325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1319755534593103986388883 1979633301889655979583325)
            ·
              refine ⟨742362488208620992343747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1979633301889655979583325 742362488208620992343747)
              ·
                refine ⟨1113543732312931488515621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 742362488208620992343747 1113543732312931488515621)
                ·
                  refine ⟨208789449808674654096679, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1113543732312931488515621 208789449808674654096679)
                  ·
                    rfl

theorem cell20_457443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 3, 1, 4].length) (baseStart_457443 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_457443 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_457443 prefixEnd_457443 := by exact prefixLift 457443
  have htrace : WordTrace (prefixWord ++ tailWord_457443) baseStart_457443 baseEnd_457443 := by
    simpa [prefixWord, tailWord_457443, baseEnd_457443] using wordTrace_append hprefix tailTrace_457443
  have hstable : (prefixWord ++ tailWord_457443).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_457443).length < 2 ^ (prefixWord ++ tailWord_457443).sum := by decide
  have hdescent : baseEnd_457443 < baseStart_457443 := by decide
  rcases family_descends (prefixWord ++ tailWord_457443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_457457 : List Nat := [1, 2, 2, 2, 2, 2, 3, 3, 3]
def baseStart_457457 : Nat := 118140960795 + 457457 * 2 ^ 59
def prefixEnd_457457 : Nat := 4983230072969 + 3 ^ 40 * 457457 * 2
def baseEnd_457457 : Nat := 208795839790152827629955

theorem tailTrace_457457 : CollatzResearch.WordTrace tailWord_457457 prefixEnd_457457 208795839790152827629955 := by
  unfold tailWord_457457
  simp only [CollatzResearch.WordTrace]
  refine ⟨16684827503718891280666625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11123218335812594187111083 16684827503718891280666625)
  ·
    refine ⟨12513620627789168460499969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16684827503718891280666625 12513620627789168460499969)
    ·
      refine ⟨9385215470841876345374977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12513620627789168460499969 9385215470841876345374977)
      ·
        refine ⟨7038911603131407259031233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9385215470841876345374977 7038911603131407259031233)
        ·
          refine ⟨5279183702348555444273425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7038911603131407259031233 5279183702348555444273425)
          ·
            refine ⟨3959387776761416583205069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5279183702348555444273425 3959387776761416583205069)
            ·
              refine ⟨1484770416285531218701901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3959387776761416583205069 1484770416285531218701901)
              ·
                refine ⟨556788906107074207013213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1484770416285531218701901 556788906107074207013213)
                ·
                  refine ⟨208795839790152827629955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 556788906107074207013213 208795839790152827629955)
                  ·
                    rfl

theorem cell20_457457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 3, 3, 3].length) (baseStart_457457 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_457457 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_457457 prefixEnd_457457 := by exact prefixLift 457457
  have htrace : WordTrace (prefixWord ++ tailWord_457457) baseStart_457457 baseEnd_457457 := by
    simpa [prefixWord, tailWord_457457, baseEnd_457457] using wordTrace_append hprefix tailTrace_457457
  have hstable : (prefixWord ++ tailWord_457457).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_457457).length < 2 ^ (prefixWord ++ tailWord_457457).sum := by decide
  have hdescent : baseEnd_457457 < baseStart_457457 := by decide
  rcases family_descends (prefixWord ++ tailWord_457457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_457557 : List Nat := [1, 3, 2, 2, 2, 1, 1, 6, 2]
def baseStart_457557 : Nat := 118140960795 + 457557 * 2 ^ 59
def prefixEnd_457557 : Nat := 4983230072969 + 3 ^ 40 * 457557 * 2
def baseEnd_457557 : Nat := 208841482514996924296213

theorem tailTrace_457557 : CollatzResearch.WordTrace tailWord_457557 prefixEnd_457557 208841482514996924296213 := by
  unfold tailWord_457557
  simp only [CollatzResearch.WordTrace]
  refine ⟨16688474803356608359306925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11125649868904405572871283 16688474803356608359306925)
  ·
    refine ⟨6258178051258728134740097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16688474803356608359306925 6258178051258728134740097)
    ·
      refine ⟨4693633538444046101055073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6258178051258728134740097 4693633538444046101055073)
      ·
        refine ⟨3520225153833034575791305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4693633538444046101055073 3520225153833034575791305)
        ·
          refine ⟨2640168865374775931843479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3520225153833034575791305 2640168865374775931843479)
          ·
            refine ⟨3960253298062163897765219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2640168865374775931843479 3960253298062163897765219)
            ·
              refine ⟨5940379947093245846647829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3960253298062163897765219 5940379947093245846647829)
              ·
                refine ⟨278455310019995899061617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 5940379947093245846647829 278455310019995899061617)
                ·
                  refine ⟨208841482514996924296213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 278455310019995899061617 208841482514996924296213)
                  ·
                    rfl

theorem cell20_457557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 1, 6, 2].length) (baseStart_457557 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_457557 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_457557 prefixEnd_457557 := by exact prefixLift 457557
  have htrace : WordTrace (prefixWord ++ tailWord_457557) baseStart_457557 baseEnd_457557 := by
    simpa [prefixWord, tailWord_457557, baseEnd_457557] using wordTrace_append hprefix tailTrace_457557
  have hstable : (prefixWord ++ tailWord_457557).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_457557).length < 2 ^ (prefixWord ++ tailWord_457557).sum := by decide
  have hdescent : baseEnd_457557 < baseStart_457557 := by decide
  rcases family_descends (prefixWord ++ tailWord_457557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_457585 : List Nat := [1, 2, 2, 2, 1, 5, 1, 6]
def baseStart_457585 : Nat := 118140960795 + 457585 * 2 ^ 59
def prefixEnd_457585 : Nat := 4983230072969 + 3 ^ 40 * 457585 * 2
def baseEnd_457585 : Nat := 69618087492651090454255

theorem tailTrace_457585 : CollatzResearch.WordTrace tailWord_457585 prefixEnd_457585 69618087492651090454255 := by
  unfold tailWord_457585
  simp only [CollatzResearch.WordTrace]
  refine ⟨16689496047255169141326209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11126330698170112760884139 16689496047255169141326209)
  ·
    refine ⟨12517122035441376855994657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16689496047255169141326209 12517122035441376855994657)
    ·
      refine ⟨9387841526581032641995993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12517122035441376855994657 9387841526581032641995993)
      ·
        refine ⟨7040881144935774481496995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9387841526581032641995993 7040881144935774481496995)
        ·
          refine ⟨10561321717403661722245493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7040881144935774481496995 10561321717403661722245493)
          ·
            refine ⟨990123911006593286460515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 10561321717403661722245493 990123911006593286460515)
            ·
              refine ⟨1485185866509889929690773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 990123911006593286460515 1485185866509889929690773)
              ·
                refine ⟨69618087492651090454255, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1485185866509889929690773 69618087492651090454255)
                ·
                  rfl

theorem cell20_457585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 5, 1, 6].length) (baseStart_457585 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_457585 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_457585 prefixEnd_457585 := by exact prefixLift 457585
  have htrace : WordTrace (prefixWord ++ tailWord_457585) baseStart_457585 baseEnd_457585 := by
    simpa [prefixWord, tailWord_457585, baseEnd_457585] using wordTrace_append hprefix tailTrace_457585
  have hstable : (prefixWord ++ tailWord_457585).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_457585).length < 2 ^ (prefixWord ++ tailWord_457585).sum := by decide
  have hdescent : baseEnd_457585 < baseStart_457585 := by decide
  rcases family_descends (prefixWord ++ tailWord_457585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_457595 : List Nat := [1, 1, 1, 1, 1, 5, 5, 3, 2]
def baseStart_457595 : Nat := 118140960795 + 457595 * 2 ^ 59
def prefixEnd_457595 : Nat := 4983230072969 + 3 ^ 40 * 457595 * 2
def baseEnd_457595 : Nat := 208858826750437681029391

theorem tailTrace_457595 : CollatzResearch.WordTrace tailWord_457595 prefixEnd_457595 208858826750437681029391 := by
  unfold tailWord_457595
  simp only [CollatzResearch.WordTrace]
  refine ⟨16689860777218940849190239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11126573851479293899460159 16689860777218940849190239)
  ·
    refine ⟨25034791165828411273785359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16689860777218940849190239 25034791165828411273785359)
    ·
      refine ⟨37552186748742616910678039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25034791165828411273785359 37552186748742616910678039)
      ·
        refine ⟨56328280123113925366017059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37552186748742616910678039 56328280123113925366017059)
        ·
          refine ⟨84492420184670888049025589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56328280123113925366017059 84492420184670888049025589)
          ·
            refine ⟨7921164392312895754596149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 84492420184670888049025589 7921164392312895754596149)
            ·
              refine ⟨742609161779333976993389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 7921164392312895754596149 742609161779333976993389)
              ·
                refine ⟨278478435667250241372521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 742609161779333976993389 278478435667250241372521)
                ·
                  refine ⟨208858826750437681029391, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 278478435667250241372521 208858826750437681029391)
                  ·
                    rfl

theorem cell20_457595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 5, 3, 2].length) (baseStart_457595 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_457595 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_457595 prefixEnd_457595 := by exact prefixLift 457595
  have htrace : WordTrace (prefixWord ++ tailWord_457595) baseStart_457595 baseEnd_457595 := by
    simpa [prefixWord, tailWord_457595, baseEnd_457595] using wordTrace_append hprefix tailTrace_457595
  have hstable : (prefixWord ++ tailWord_457595).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_457595).length < 2 ^ (prefixWord ++ tailWord_457595).sum := by decide
  have hdescent : baseEnd_457595 < baseStart_457595 := by decide
  rcases family_descends (prefixWord ++ tailWord_457595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_457598 : List Nat := [4, 2, 3, 1, 3, 1, 6]
def baseStart_457598 : Nat := 118140960795 + 457598 * 2 ^ 59
def prefixEnd_457598 : Nat := 4983230072969 + 3 ^ 40 * 457598 * 2
def baseEnd_457598 : Nat := 23206688448020333769931

theorem tailTrace_457598 : CollatzResearch.WordTrace tailWord_457598 prefixEnd_457598 23206688448020333769931 := by
  unfold tailWord_457598
  simp only [CollatzResearch.WordTrace]
  refine ⟨2086246274526009045193681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11126646797472048241032965 2086246274526009045193681)
  ·
    refine ⟨1564684705894506783895261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2086246274526009045193681 1564684705894506783895261)
    ·
      refine ⟨586756764710440043960723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1564684705894506783895261 586756764710440043960723)
      ·
        refine ⟨880135147065660065941085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 586756764710440043960723 880135147065660065941085)
        ·
          refine ⟨330050680149622524727907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 880135147065660065941085 330050680149622524727907)
          ·
            refine ⟨495076020224433787091861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 330050680149622524727907 495076020224433787091861)
            ·
              refine ⟨23206688448020333769931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 495076020224433787091861 23206688448020333769931)
              ·
                rfl

theorem cell20_457598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 3, 1, 6].length) (baseStart_457598 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_457598 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_457598 prefixEnd_457598 := by exact prefixLift 457598
  have htrace : WordTrace (prefixWord ++ tailWord_457598) baseStart_457598 baseEnd_457598 := by
    simpa [prefixWord, tailWord_457598, baseEnd_457598] using wordTrace_append hprefix tailTrace_457598
  have hstable : (prefixWord ++ tailWord_457598).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_457598).length < 2 ^ (prefixWord ++ tailWord_457598).sum := by decide
  have hdescent : baseEnd_457598 < baseStart_457598 := by decide
  rcases family_descends (prefixWord ++ tailWord_457598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_457599 : List Nat := [1, 1, 2, 2, 1, 1, 4, 2, 6]
def baseStart_457599 : Nat := 118140960795 + 457599 * 2 ^ 59
def prefixEnd_457599 : Nat := 4983230072969 + 3 ^ 40 * 457599 * 2
def baseEnd_457599 : Nat := 208860652459431444896041

theorem tailTrace_457599 : CollatzResearch.WordTrace tailWord_457599 prefixEnd_457599 208860652459431444896041 := by
  unfold tailWord_457599
  simp only [CollatzResearch.WordTrace]
  refine ⟨16690006669204449532335851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11126671112802966354890567 16690006669204449532335851)
  ·
    refine ⟨25035010003806674298503777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16690006669204449532335851 25035010003806674298503777)
    ·
      refine ⟨18776257502855005723877833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25035010003806674298503777 18776257502855005723877833)
      ·
        refine ⟨14082193127141254292908375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18776257502855005723877833 14082193127141254292908375)
        ·
          refine ⟨21123289690711881439362563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14082193127141254292908375 21123289690711881439362563)
          ·
            refine ⟨31684934536067822159043845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21123289690711881439362563 31684934536067822159043845)
            ·
              refine ⟨5940925225512716654820721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31684934536067822159043845 5940925225512716654820721)
              ·
                refine ⟨4455693919134537491115541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5940925225512716654820721 4455693919134537491115541)
                ·
                  refine ⟨208860652459431444896041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4455693919134537491115541 208860652459431444896041)
                  ·
                    rfl

theorem cell20_457599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 4, 2, 6].length) (baseStart_457599 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_457599 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_457599 prefixEnd_457599 := by exact prefixLift 457599
  have htrace : WordTrace (prefixWord ++ tailWord_457599) baseStart_457599 baseEnd_457599 := by
    simpa [prefixWord, tailWord_457599, baseEnd_457599] using wordTrace_append hprefix tailTrace_457599
  have hstable : (prefixWord ++ tailWord_457599).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_457599).length < 2 ^ (prefixWord ++ tailWord_457599).sum := by decide
  have hdescent : baseEnd_457599 < baseStart_457599 := by decide
  rcases family_descends (prefixWord ++ tailWord_457599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_457622 : List Nat := [5, 3, 1, 1, 1, 2, 1, 3, 3]
def baseStart_457622 : Nat := 118140960795 + 457622 * 2 ^ 59
def prefixEnd_457622 : Nat := 4983230072969 + 3 ^ 40 * 457622 * 2
def baseEnd_457622 : Nat := 208871150286145587129281

theorem tailTrace_457622 : CollatzResearch.WordTrace tailWord_457622 prefixEnd_457622 208871150286145587129281 := by
  unfold tailWord_457622
  simp only [CollatzResearch.WordTrace]
  refine ⟨1043177846757570278776445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 11127230365414082973615413 1043177846757570278776445)
  ·
    refine ⟨391191692534088854541167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1043177846757570278776445 391191692534088854541167)
    ·
      refine ⟨586787538801133281811751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 391191692534088854541167 586787538801133281811751)
      ·
        refine ⟨880181308201699922717627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 586787538801133281811751 880181308201699922717627)
        ·
          refine ⟨1320271962302549884076441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 880181308201699922717627 1320271962302549884076441)
          ·
            refine ⟨990203971726912413057331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1320271962302549884076441 990203971726912413057331)
            ·
              refine ⟨1485305957590368619585997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 990203971726912413057331 1485305957590368619585997)
              ·
                refine ⟨556989734096388232344749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1485305957590368619585997 556989734096388232344749)
                ·
                  refine ⟨208871150286145587129281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 556989734096388232344749 208871150286145587129281)
                  ·
                    rfl

theorem cell20_457622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 2, 1, 3, 3].length) (baseStart_457622 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_457622 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_457622 prefixEnd_457622 := by exact prefixLift 457622
  have htrace : WordTrace (prefixWord ++ tailWord_457622) baseStart_457622 baseEnd_457622 := by
    simpa [prefixWord, tailWord_457622, baseEnd_457622] using wordTrace_append hprefix tailTrace_457622
  have hstable : (prefixWord ++ tailWord_457622).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_457622).length < 2 ^ (prefixWord ++ tailWord_457622).sum := by decide
  have hdescent : baseEnd_457622 < baseStart_457622 := by decide
  rcases family_descends (prefixWord ++ tailWord_457622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_457623 : List Nat := [1, 1, 3, 3, 1, 2, 4, 5]
def baseStart_457623 : Nat := 118140960795 + 457623 * 2 ^ 59
def prefixEnd_457623 : Nat := 4983230072969 + 3 ^ 40 * 457623 * 2
def baseEnd_457623 : Nat := 69623868904464676031981

theorem tailTrace_457623 : CollatzResearch.WordTrace tailWord_457623 prefixEnd_457623 69623868904464676031981 := by
  unfold tailWord_457623
  simp only [CollatzResearch.WordTrace]
  refine ⟨16690882021117501631209523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11127254680745001087473015 16690882021117501631209523)
  ·
    refine ⟨25036323031676252446814285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16690882021117501631209523 25036323031676252446814285)
    ·
      refine ⟨9388621136878594667555357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25036323031676252446814285 9388621136878594667555357)
      ·
        refine ⟨3520732926329473000333259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9388621136878594667555357 3520732926329473000333259)
        ·
          refine ⟨5281099389494209500499889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3520732926329473000333259 5281099389494209500499889)
          ·
            refine ⟨3960824542120657125374917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5281099389494209500499889 3960824542120657125374917)
            ·
              refine ⟨742654601647623211007797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3960824542120657125374917 742654601647623211007797)
              ·
                refine ⟨69623868904464676031981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 742654601647623211007797 69623868904464676031981)
                ·
                  rfl

theorem cell20_457623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 4, 5].length) (baseStart_457623 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_457623 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_457623 prefixEnd_457623 := by exact prefixLift 457623
  have htrace : WordTrace (prefixWord ++ tailWord_457623) baseStart_457623 baseEnd_457623 := by
    simpa [prefixWord, tailWord_457623, baseEnd_457623] using wordTrace_append hprefix tailTrace_457623
  have hstable : (prefixWord ++ tailWord_457623).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_457623).length < 2 ^ (prefixWord ++ tailWord_457623).sum := by decide
  have hdescent : baseEnd_457623 < baseStart_457623 := by decide
  rcases family_descends (prefixWord ++ tailWord_457623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_457626 : List Nat := [3, 1, 1, 4, 3, 1, 1, 3, 3]
def baseStart_457626 : Nat := 118140960795 + 457626 * 2 ^ 59
def prefixEnd_457626 : Nat := 4983230072969 + 3 ^ 40 * 457626 * 2
def baseEnd_457626 : Nat := 208872975995139350995931

theorem tailTrace_457626 : CollatzResearch.WordTrace tailWord_457626 prefixEnd_457626 208872975995139350995931 := by
  unfold tailWord_457626
  simp only [CollatzResearch.WordTrace]
  refine ⟨4172747860026658285892183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11127327626737755429045821 4172747860026658285892183)
  ·
    refine ⟨6259121790039987428838275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4172747860026658285892183 6259121790039987428838275)
    ·
      refine ⟨9388682685059981143257413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6259121790039987428838275 9388682685059981143257413)
      ·
        refine ⟨1760378003448746464360765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9388682685059981143257413 1760378003448746464360765)
        ·
          refine ⟨660141751293279924135287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1760378003448746464360765 660141751293279924135287)
          ·
            refine ⟨990212626939919886202931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 660141751293279924135287 990212626939919886202931)
            ·
              refine ⟨1485318940409879829304397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 990212626939919886202931 1485318940409879829304397)
              ·
                refine ⟨556994602653704935989149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1485318940409879829304397 556994602653704935989149)
                ·
                  refine ⟨208872975995139350995931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 556994602653704935989149 208872975995139350995931)
                  ·
                    rfl

theorem cell20_457626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 1, 1, 3, 3].length) (baseStart_457626 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_457626 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_457626 prefixEnd_457626 := by exact prefixLift 457626
  have htrace : WordTrace (prefixWord ++ tailWord_457626) baseStart_457626 baseEnd_457626 := by
    simpa [prefixWord, tailWord_457626, baseEnd_457626] using wordTrace_append hprefix tailTrace_457626
  have hstable : (prefixWord ++ tailWord_457626).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_457626).length < 2 ^ (prefixWord ++ tailWord_457626).sum := by decide
  have hdescent : baseEnd_457626 < baseStart_457626 := by decide
  rcases family_descends (prefixWord ++ tailWord_457626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_457661 : List Nat := [1, 4, 1, 2, 4, 8]
def baseStart_457661 : Nat := 118140960795 + 457661 * 2 ^ 59
def prefixEnd_457661 : Nat := 4983230072969 + 3 ^ 40 * 457661 * 2
def baseEnd_457661 : Nat := 7736627812919806845523

theorem tailTrace_457661 : CollatzResearch.WordTrace tailWord_457661 prefixEnd_457661 7736627812919806845523 := by
  unfold tailWord_457661
  simp only [CollatzResearch.WordTrace]
  refine ⟨16692267994979834121092837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11128178663319889414061891 16692267994979834121092837)
  ·
    refine ⟨3129800249058718897704907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16692267994979834121092837 3129800249058718897704907)
    ·
      refine ⟨4694700373588078346557361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3129800249058718897704907 4694700373588078346557361)
      ·
        refine ⟨3521025280191058759918021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4694700373588078346557361 3521025280191058759918021)
        ·
          refine ⟨660192240035823517484629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3521025280191058759918021 660192240035823517484629)
          ·
            refine ⟨7736627812919806845523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 660192240035823517484629 7736627812919806845523)
            ·
              rfl

theorem cell20_457661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 8].length) (baseStart_457661 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_457661 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_457661 prefixEnd_457661 := by exact prefixLift 457661
  have htrace : WordTrace (prefixWord ++ tailWord_457661) baseStart_457661 baseEnd_457661 := by
    simpa [prefixWord, tailWord_457661, baseEnd_457661] using wordTrace_append hprefix tailTrace_457661
  have hstable : (prefixWord ++ tailWord_457661).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_457661).length < 2 ^ (prefixWord ++ tailWord_457661).sum := by decide
  have hdescent : baseEnd_457661 < baseStart_457661 := by decide
  rcases family_descends (prefixWord ++ tailWord_457661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_457670 : List Nat := [6, 1, 3, 1, 1, 2, 1, 5]
def baseStart_457670 : Nat := 118140960795 + 457670 * 2 ^ 59
def prefixEnd_457670 : Nat := 4983230072969 + 3 ^ 40 * 457670 * 2
def baseEnd_457670 : Nat := 69631019598023584509695

theorem tailTrace_457670 : CollatzResearch.WordTrace tailWord_457670 prefixEnd_457670 69631019598023584509695 := by
  unfold tailWord_457670
  simp only [CollatzResearch.WordTrace]
  refine ⟨521643632873350895567827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 11128397501298152438780309 521643632873350895567827)
  ·
    refine ⟨782465449310026343351741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 521643632873350895567827 782465449310026343351741)
    ·
      refine ⟨293424543491259878756903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 782465449310026343351741 293424543491259878756903)
      ·
        refine ⟨440136815236889818135355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 293424543491259878756903 440136815236889818135355)
        ·
          refine ⟨660205222855334727203033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 440136815236889818135355 660205222855334727203033)
          ·
            refine ⟨495153917141501045402275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 660205222855334727203033 495153917141501045402275)
            ·
              refine ⟨742730875712251568103413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 495153917141501045402275 742730875712251568103413)
              ·
                refine ⟨69631019598023584509695, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 742730875712251568103413 69631019598023584509695)
                ·
                  rfl

theorem cell20_457670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 2, 1, 5].length) (baseStart_457670 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_457670 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_457670 prefixEnd_457670 := by exact prefixLift 457670
  have htrace : WordTrace (prefixWord ++ tailWord_457670) baseStart_457670 baseEnd_457670 := by
    simpa [prefixWord, tailWord_457670, baseEnd_457670] using wordTrace_append hprefix tailTrace_457670
  have hstable : (prefixWord ++ tailWord_457670).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_457670).length < 2 ^ (prefixWord ++ tailWord_457670).sum := by decide
  have hdescent : baseEnd_457670 < baseStart_457670 := by decide
  rcases family_descends (prefixWord ++ tailWord_457670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_457678 : List Nat := [4, 1, 1, 1, 2, 5, 1, 5]
def baseStart_457678 : Nat := 118140960795 + 457678 * 2 ^ 59
def prefixEnd_457678 : Nat := 4983230072969 + 3 ^ 40 * 457678 * 2
def baseEnd_457678 : Nat := 69632236737352760420795

theorem tailTrace_457678 : CollatzResearch.WordTrace tailWord_457678 prefixEnd_457678 69632236737352760420795 := by
  unfold tailWord_457678
  simp only [CollatzResearch.WordTrace]
  refine ⟨2086611004489780753057711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11128592023945497349641125 2086611004489780753057711)
  ·
    refine ⟨3129916506734671129586567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2086611004489780753057711 3129916506734671129586567)
    ·
      refine ⟨4694874760102006694379851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3129916506734671129586567 4694874760102006694379851)
      ·
        refine ⟨7042312140153010041569777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4694874760102006694379851 7042312140153010041569777)
        ·
          refine ⟨5281734105114757531177333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7042312140153010041569777 5281734105114757531177333)
          ·
            refine ⟨495162572354508518547875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 5281734105114757531177333 495162572354508518547875)
            ·
              refine ⟨742743858531762777821813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 495162572354508518547875 742743858531762777821813)
              ·
                refine ⟨69632236737352760420795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 742743858531762777821813 69632236737352760420795)
                ·
                  rfl

theorem cell20_457678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 5, 1, 5].length) (baseStart_457678 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_457678 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_457678 prefixEnd_457678 := by exact prefixLift 457678
  have htrace : WordTrace (prefixWord ++ tailWord_457678) baseStart_457678 baseEnd_457678 := by
    simpa [prefixWord, tailWord_457678, baseEnd_457678] using wordTrace_append hprefix tailTrace_457678
  have hstable : (prefixWord ++ tailWord_457678).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_457678).length < 2 ^ (prefixWord ++ tailWord_457678).sum := by decide
  have hdescent : baseEnd_457678 < baseStart_457678 := by decide
  rcases family_descends (prefixWord ++ tailWord_457678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_457726 : List Nat := [4, 2, 2, 2, 2, 1, 2, 1, 4]
def baseStart_457726 : Nat := 118140960795 + 457726 * 2 ^ 59
def prefixEnd_457726 : Nat := 4983230072969 + 3 ^ 40 * 457726 * 2
def baseEnd_457726 : Nat := 208918618719983447662189

theorem tailTrace_457726 : CollatzResearch.WordTrace tailWord_457726 prefixEnd_457726 208918618719983447662189 := by
  unfold tailWord_457726
  simp only [CollatzResearch.WordTrace]
  refine ⟨2086829842468043777776129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11129759159829566814806021 2086829842468043777776129)
  ·
    refine ⟨1565122381851032833332097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2086829842468043777776129 1565122381851032833332097)
    ·
      refine ⟨1173841786388274624999073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1565122381851032833332097 1173841786388274624999073)
      ·
        refine ⟨880381339791205968749305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1173841786388274624999073 880381339791205968749305)
        ·
          refine ⟨660286004843404476561979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 880381339791205968749305 660286004843404476561979)
          ·
            refine ⟨990429007265106714842969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 660286004843404476561979 990429007265106714842969)
            ·
              refine ⟨742821755448830036132227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 990429007265106714842969 742821755448830036132227)
              ·
                refine ⟨1114232633173245054198341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 742821755448830036132227 1114232633173245054198341)
                ·
                  refine ⟨208918618719983447662189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1114232633173245054198341 208918618719983447662189)
                  ·
                    rfl

theorem cell20_457726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 1, 2, 1, 4].length) (baseStart_457726 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_457726 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_457726 prefixEnd_457726 := by exact prefixLift 457726
  have htrace : WordTrace (prefixWord ++ tailWord_457726) baseStart_457726 baseEnd_457726 := by
    simpa [prefixWord, tailWord_457726, baseEnd_457726] using wordTrace_append hprefix tailTrace_457726
  have hstable : (prefixWord ++ tailWord_457726).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_457726).length < 2 ^ (prefixWord ++ tailWord_457726).sum := by decide
  have hdescent : baseEnd_457726 < baseStart_457726 := by decide
  rcases family_descends (prefixWord ++ tailWord_457726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_457740 : List Nat := [2, 2, 1, 2, 3, 3, 3, 1, 3]
def baseStart_457740 : Nat := 118140960795 + 457740 * 2 ^ 59
def prefixEnd_457740 : Nat := 4983230072969 + 3 ^ 40 * 457740 * 2
def baseEnd_457740 : Nat := 208925008701461621195465

theorem tailTrace_457740 : CollatzResearch.WordTrace tailWord_457740 prefixEnd_457740 208925008701461621195465 := by
  unfold tailWord_457740
  simp only [CollatzResearch.WordTrace]
  refine ⟨8347574680846815306609337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11130099574462420408812449 8347574680846815306609337)
  ·
    refine ⟨6260681010635111479957003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8347574680846815306609337 6260681010635111479957003)
    ·
      refine ⟨9391021515952667219935505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6260681010635111479957003 9391021515952667219935505)
      ·
        refine ⟨7043266136964500414951629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9391021515952667219935505 7043266136964500414951629)
        ·
          refine ⟨2641224801361687655606861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7043266136964500414951629 2641224801361687655606861)
          ·
            refine ⟨990459300510632870852573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2641224801361687655606861 990459300510632870852573)
            ·
              refine ⟨371422237691487326569715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 990459300510632870852573 371422237691487326569715)
              ·
                refine ⟨557133356537230989854573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 371422237691487326569715 557133356537230989854573)
                ·
                  refine ⟨208925008701461621195465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 557133356537230989854573 208925008701461621195465)
                  ·
                    rfl

theorem cell20_457740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 3, 3, 1, 3].length) (baseStart_457740 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_457740 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_457740 prefixEnd_457740 := by exact prefixLift 457740
  have htrace : WordTrace (prefixWord ++ tailWord_457740) baseStart_457740 baseEnd_457740 := by
    simpa [prefixWord, tailWord_457740, baseEnd_457740] using wordTrace_append hprefix tailTrace_457740
  have hstable : (prefixWord ++ tailWord_457740).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_457740).length < 2 ^ (prefixWord ++ tailWord_457740).sum := by decide
  have hdescent : baseEnd_457740 < baseStart_457740 := by decide
  rcases family_descends (prefixWord ++ tailWord_457740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_457746 : List Nat := [3, 2, 5, 1, 2, 1, 2, 4]
def baseStart_457746 : Nat := 118140960795 + 457746 * 2 ^ 59
def prefixEnd_457746 : Nat := 4983230072969 + 3 ^ 40 * 457746 * 2
def baseEnd_457746 : Nat := 69642582421650755665147

theorem tailTrace_457746 : CollatzResearch.WordTrace tailWord_457746 prefixEnd_457746 69642582421650755665147 := by
  unfold tailWord_457746
  simp only [CollatzResearch.WordTrace]
  refine ⟨4173842049917973409484273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11130245466447929091958061 4173842049917973409484273)
  ·
    refine ⟨3130381537438480057113205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4173842049917973409484273 3130381537438480057113205)
    ·
      refine ⟨293473269134857505354363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 3130381537438480057113205 293473269134857505354363)
      ·
        refine ⟨440209903702286258031545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 293473269134857505354363 440209903702286258031545)
        ·
          refine ⟨330157427776714693523659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 440209903702286258031545 330157427776714693523659)
          ·
            refine ⟨495236141665072040285489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 330157427776714693523659 495236141665072040285489)
            ·
              refine ⟨371427106248804030214117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 495236141665072040285489 371427106248804030214117)
              ·
                refine ⟨69642582421650755665147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 371427106248804030214117 69642582421650755665147)
                ·
                  rfl

theorem cell20_457746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 2, 1, 2, 4].length) (baseStart_457746 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_457746 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_457746 prefixEnd_457746 := by exact prefixLift 457746
  have htrace : WordTrace (prefixWord ++ tailWord_457746) baseStart_457746 baseEnd_457746 := by
    simpa [prefixWord, tailWord_457746, baseEnd_457746] using wordTrace_append hprefix tailTrace_457746
  have hstable : (prefixWord ++ tailWord_457746).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_457746).length < 2 ^ (prefixWord ++ tailWord_457746).sum := by decide
  have hdescent : baseEnd_457746 < baseStart_457746 := by decide
  rcases family_descends (prefixWord ++ tailWord_457746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_457760 : List Nat := [2, 1, 1, 7, 2, 1, 1, 3, 2]
def baseStart_457760 : Nat := 118140960795 + 457760 * 2 ^ 59
def prefixEnd_457760 : Nat := 4983230072969 + 3 ^ 40 * 457760 * 2
def baseEnd_457760 : Nat := 208934137246430440528717

theorem tailTrace_457760 : CollatzResearch.WordTrace tailWord_457760 prefixEnd_457760 208934137246430440528717 := by
  unfold tailWord_457760
  simp only [CollatzResearch.WordTrace]
  refine ⟨8347939410810587014473367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11130585881080782685964489 8347939410810587014473367)
  ·
    refine ⟨12521909116215880521710051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8347939410810587014473367 12521909116215880521710051)
    ·
      refine ⟨18782863674323820782565077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12521909116215880521710051 18782863674323820782565077)
      ·
        refine ⟨440223367366964549591369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 18782863674323820782565077 440223367366964549591369)
        ·
          refine ⟨330167525525223412193527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 440223367366964549591369 330167525525223412193527)
          ·
            refine ⟨495251288287835118290291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 330167525525223412193527 495251288287835118290291)
            ·
              refine ⟨742876932431752677435437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 495251288287835118290291 742876932431752677435437)
              ·
                refine ⟨278578849661907254038289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 742876932431752677435437 278578849661907254038289)
                ·
                  refine ⟨208934137246430440528717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 278578849661907254038289 208934137246430440528717)
                  ·
                    rfl

theorem cell20_457760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 2, 1, 1, 3, 2].length) (baseStart_457760 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_457760 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_457760 prefixEnd_457760 := by exact prefixLift 457760
  have htrace : WordTrace (prefixWord ++ tailWord_457760) baseStart_457760 baseEnd_457760 := by
    simpa [prefixWord, tailWord_457760, baseEnd_457760] using wordTrace_append hprefix tailTrace_457760
  have hstable : (prefixWord ++ tailWord_457760).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_457760).length < 2 ^ (prefixWord ++ tailWord_457760).sum := by decide
  have hdescent : baseEnd_457760 < baseStart_457760 := by decide
  rcases family_descends (prefixWord ++ tailWord_457760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_457764 : List Nat := [2, 3, 1, 4, 1, 1, 3, 3, 2]
def baseStart_457764 : Nat := 118140960795 + 457764 * 2 ^ 59
def prefixEnd_457764 : Nat := 4983230072969 + 3 ^ 40 * 457764 * 2
def baseEnd_457764 : Nat := 208935962955424204395367

theorem tailTrace_457764 : CollatzResearch.WordTrace tailWord_457764 prefixEnd_457764 208935962955424204395367 := by
  unfold tailWord_457764
  simp only [CollatzResearch.WordTrace]
  refine ⟨8348012356803341356046173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11130683142404455141394897 8348012356803341356046173)
  ·
    refine ⟨3130504633801253008517315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8348012356803341356046173 3130504633801253008517315)
    ·
      refine ⟨4695756950701879512775973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3130504633801253008517315 4695756950701879512775973)
      ·
        refine ⟨880454428256602408645495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4695756950701879512775973 880454428256602408645495)
        ·
          refine ⟨1320681642384903612968243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 880454428256602408645495 1320681642384903612968243)
          ·
            refine ⟨1981022463577355419452365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1320681642384903612968243 1981022463577355419452365)
            ·
              refine ⟨742883423841508282294637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1981022463577355419452365 742883423841508282294637)
              ·
                refine ⟨278581283940565605860489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 742883423841508282294637 278581283940565605860489)
                ·
                  refine ⟨208935962955424204395367, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 278581283940565605860489 208935962955424204395367)
                  ·
                    rfl

theorem cell20_457764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 3, 3, 2].length) (baseStart_457764 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_457764 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_457764 prefixEnd_457764 := by exact prefixLift 457764
  have htrace : WordTrace (prefixWord ++ tailWord_457764) baseStart_457764 baseEnd_457764 := by
    simpa [prefixWord, tailWord_457764, baseEnd_457764] using wordTrace_append hprefix tailTrace_457764
  have hstable : (prefixWord ++ tailWord_457764).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_457764).length < 2 ^ (prefixWord ++ tailWord_457764).sum := by decide
  have hdescent : baseEnd_457764 < baseStart_457764 := by decide
  rcases family_descends (prefixWord ++ tailWord_457764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_457785 : List Nat := [1, 2, 1, 5, 2, 3, 1, 1, 4]
def baseStart_457785 : Nat := 118140960795 + 457785 * 2 ^ 59
def prefixEnd_457785 : Nat := 4983230072969 + 3 ^ 40 * 457785 * 2
def baseEnd_457785 : Nat := 208945547927641464695281

theorem tailTrace_457785 : CollatzResearch.WordTrace tailWord_457785 prefixEnd_457785 208945547927641464695281 := by
  unfold tailWord_457785
  simp only [CollatzResearch.WordTrace]
  refine ⟨16696790646530603298606809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11131193764353735532404539 16696790646530603298606809)
  ·
    refine ⟨12522592984897952473955107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16696790646530603298606809 12522592984897952473955107)
    ·
      refine ⟨18783889477346928710932661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12522592984897952473955107 18783889477346928710932661)
      ·
        refine ⟨1760989638501274566649937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 18783889477346928710932661 1760989638501274566649937)
        ·
          refine ⟨1320742228875955924987453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1760989638501274566649937 1320742228875955924987453)
          ·
            refine ⟨495278335828483471870295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1320742228875955924987453 495278335828483471870295)
            ·
              refine ⟨742917503742725207805443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 495278335828483471870295 742917503742725207805443)
              ·
                refine ⟨1114376255614087811708165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 742917503742725207805443 1114376255614087811708165)
                ·
                  refine ⟨208945547927641464695281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1114376255614087811708165 208945547927641464695281)
                  ·
                    rfl

theorem cell20_457785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 3, 1, 1, 4].length) (baseStart_457785 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_457785 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_457785 prefixEnd_457785 := by exact prefixLift 457785
  have htrace : WordTrace (prefixWord ++ tailWord_457785) baseStart_457785 baseEnd_457785 := by
    simpa [prefixWord, tailWord_457785, baseEnd_457785] using wordTrace_append hprefix tailTrace_457785
  have hstable : (prefixWord ++ tailWord_457785).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_457785).length < 2 ^ (prefixWord ++ tailWord_457785).sum := by decide
  have hdescent : baseEnd_457785 < baseStart_457785 := by decide
  rcases family_descends (prefixWord ++ tailWord_457785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_457799 : List Nat := [1, 1, 4, 1, 3, 3, 1, 3, 3]
def baseStart_457799 : Nat := 118140960795 + 457799 * 2 ^ 59
def prefixEnd_457799 : Nat := 4983230072969 + 3 ^ 40 * 457799 * 2
def baseEnd_457799 : Nat := 208951937909119638228557

theorem tailTrace_457799 : CollatzResearch.WordTrace tailWord_457799 prefixEnd_457799 208951937909119638228557 := by
  unfold tailWord_457799
  simp only [CollatzResearch.WordTrace]
  refine ⟨16697301268479883689616451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11131534178986589126410967 16697301268479883689616451)
  ·
    refine ⟨25045951902719825534424677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16697301268479883689616451 25045951902719825534424677)
    ·
      refine ⟨4696115981759967287704627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 25045951902719825534424677 4696115981759967287704627)
      ·
        refine ⟨7044173972639950931556941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4696115981759967287704627 7044173972639950931556941)
        ·
          refine ⟨2641565239739981599333853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7044173972639950931556941 2641565239739981599333853)
          ·
            refine ⟨990586964902493099750195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2641565239739981599333853 990586964902493099750195)
            ·
              refine ⟨1485880447353739649625293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 990586964902493099750195 1485880447353739649625293)
              ·
                refine ⟨557205167757652368609485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1485880447353739649625293 557205167757652368609485)
                ·
                  refine ⟨208951937909119638228557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 557205167757652368609485 208951937909119638228557)
                  ·
                    rfl

theorem cell20_457799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 3, 1, 3, 3].length) (baseStart_457799 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_457799 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_457799 prefixEnd_457799 := by exact prefixLift 457799
  have htrace : WordTrace (prefixWord ++ tailWord_457799) baseStart_457799 baseEnd_457799 := by
    simpa [prefixWord, tailWord_457799, baseEnd_457799] using wordTrace_append hprefix tailTrace_457799
  have hstable : (prefixWord ++ tailWord_457799).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_457799).length < 2 ^ (prefixWord ++ tailWord_457799).sum := by decide
  have hdescent : baseEnd_457799 < baseStart_457799 := by decide
  rcases family_descends (prefixWord ++ tailWord_457799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_457837 : List Nat := [1, 5, 1, 1, 2, 2, 1, 4, 3]
def baseStart_457837 : Nat := 118140960795 + 457837 * 2 ^ 59
def prefixEnd_457837 : Nat := 4983230072969 + 3 ^ 40 * 457837 * 2
def baseEnd_457837 : Nat := 208969282144560394961735

theorem tailTrace_457837 : CollatzResearch.WordTrace tailWord_457837 prefixEnd_457837 208969282144560394961735 := by
  unfold tailWord_457837
  simp only [CollatzResearch.WordTrace]
  refine ⟨16698687242342216179499765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11132458161561477452999843 16698687242342216179499765)
  ·
    refine ⟨1565501928969582766828103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 16698687242342216179499765 1565501928969582766828103)
    ·
      refine ⟨2348252893454374150242155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1565501928969582766828103 2348252893454374150242155)
      ·
        refine ⟨3522379340181561225363233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2348252893454374150242155 3522379340181561225363233)
        ·
          refine ⟨2641784505136170919022425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3522379340181561225363233 2641784505136170919022425)
          ·
            refine ⟨1981338378852128189266819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2641784505136170919022425 1981338378852128189266819)
            ·
              refine ⟨2972007568278192283900229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1981338378852128189266819 2972007568278192283900229)
              ·
                refine ⟨557251419052161053231293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2972007568278192283900229 557251419052161053231293)
                ·
                  refine ⟨208969282144560394961735, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 557251419052161053231293 208969282144560394961735)
                  ·
                    rfl

theorem cell20_457837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 1, 4, 3].length) (baseStart_457837 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_457837 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_457837 prefixEnd_457837 := by exact prefixLift 457837
  have htrace : WordTrace (prefixWord ++ tailWord_457837) baseStart_457837 baseEnd_457837 := by
    simpa [prefixWord, tailWord_457837, baseEnd_457837] using wordTrace_append hprefix tailTrace_457837
  have hstable : (prefixWord ++ tailWord_457837).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_457837).length < 2 ^ (prefixWord ++ tailWord_457837).sum := by decide
  have hdescent : baseEnd_457837 < baseStart_457837 := by decide
  rcases family_descends (prefixWord ++ tailWord_457837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_457865 : List Nat := [1, 2, 1, 1, 4, 3, 1, 1, 6]
def baseStart_457865 : Nat := 118140960795 + 457865 * 2 ^ 59
def prefixEnd_457865 : Nat := 4983230072969 + 3 ^ 40 * 457865 * 2
def baseEnd_457865 : Nat := 208982062107516742028287

theorem tailTrace_457865 : CollatzResearch.WordTrace tailWord_457865 prefixEnd_457865 208982062107516742028287 := by
  unfold tailWord_457865
  simp only [CollatzResearch.WordTrace]
  refine ⟨16699708486240776961519049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11133138990827184641012699 16699708486240776961519049)
  ·
    refine ⟨12524781364680582721139287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16699708486240776961519049 12524781364680582721139287)
    ·
      refine ⟨18787172047020874081708931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12524781364680582721139287 18787172047020874081708931)
      ·
        refine ⟨28180758070531311122563397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18787172047020874081708931 28180758070531311122563397)
        ·
          refine ⟨5283892138224620835480637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28180758070531311122563397 5283892138224620835480637)
          ·
            refine ⟨1981459551834232813305239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5283892138224620835480637 1981459551834232813305239)
            ·
              refine ⟨2972189327751349219957859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1981459551834232813305239 2972189327751349219957859)
              ·
                refine ⟨4458283991627023829936789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2972189327751349219957859 4458283991627023829936789)
                ·
                  refine ⟨208982062107516742028287, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4458283991627023829936789 208982062107516742028287)
                  ·
                    rfl

theorem cell20_457865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 1, 1, 6].length) (baseStart_457865 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_457865 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_457865 prefixEnd_457865 := by exact prefixLift 457865
  have htrace : WordTrace (prefixWord ++ tailWord_457865) baseStart_457865 baseEnd_457865 := by
    simpa [prefixWord, tailWord_457865, baseEnd_457865] using wordTrace_append hprefix tailTrace_457865
  have hstable : (prefixWord ++ tailWord_457865).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_457865).length < 2 ^ (prefixWord ++ tailWord_457865).sum := by decide
  have hdescent : baseEnd_457865 < baseStart_457865 := by decide
  rcases family_descends (prefixWord ++ tailWord_457865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_457892 : List Nat := [2, 3, 1, 2, 3, 3, 1, 2, 3]
def baseStart_457892 : Nat := 118140960795 + 457892 * 2 ^ 59
def prefixEnd_457892 : Nat := 4983230072969 + 3 ^ 40 * 457892 * 2
def baseEnd_457892 : Nat := 208994385643224648128177

theorem tailTrace_457892 : CollatzResearch.WordTrace tailWord_457892 prefixEnd_457892 208994385643224648128177 := by
  unfold tailWord_457892
  simp only [CollatzResearch.WordTrace]
  refine ⟨8350346628571480286375965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11133795504761973715167953 8350346628571480286375965)
  ·
    refine ⟨3131379985714305107390987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8350346628571480286375965 3131379985714305107390987)
    ·
      refine ⟨4697069978571457661086481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3131379985714305107390987 4697069978571457661086481)
      ·
        refine ⟨3522802483928593245814861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4697069978571457661086481 3522802483928593245814861)
        ·
          refine ⟨1321050931473222467180573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3522802483928593245814861 1321050931473222467180573)
          ·
            refine ⟨495394099302458425192715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1321050931473222467180573 495394099302458425192715)
            ·
              refine ⟨743091148953687637789073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 495394099302458425192715 743091148953687637789073)
              ·
                refine ⟨557318361715265728341805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 743091148953687637789073 557318361715265728341805)
                ·
                  refine ⟨208994385643224648128177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 557318361715265728341805 208994385643224648128177)
                  ·
                    rfl

theorem cell20_457892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 3, 1, 2, 3].length) (baseStart_457892 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_457892 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_457892 prefixEnd_457892 := by exact prefixLift 457892
  have htrace : WordTrace (prefixWord ++ tailWord_457892) baseStart_457892 baseEnd_457892 := by
    simpa [prefixWord, tailWord_457892, baseEnd_457892] using wordTrace_append hprefix tailTrace_457892
  have hstable : (prefixWord ++ tailWord_457892).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_457892).length < 2 ^ (prefixWord ++ tailWord_457892).sum := by decide
  have hdescent : baseEnd_457892 < baseStart_457892 := by decide
  rcases family_descends (prefixWord ++ tailWord_457892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_457903 : List Nat := [1, 1, 2, 1, 2, 3, 3, 3, 4]
def baseStart_457903 : Nat := 118140960795 + 457903 * 2 ^ 59
def prefixEnd_457903 : Nat := 4983230072969 + 3 ^ 40 * 457903 * 2
def baseEnd_457903 : Nat := 208999406342957498761465

theorem tailTrace_457903 : CollatzResearch.WordTrace tailWord_457903 prefixEnd_457903 208999406342957498761465 := by
  unfold tailWord_457903
  simp only [CollatzResearch.WordTrace]
  refine ⟨16701094460103109451402363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11134062973402072967601575 16701094460103109451402363)
  ·
    refine ⟨25051641690154664177103545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16701094460103109451402363 25051641690154664177103545)
    ·
      refine ⟨18788731267615998132827659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25051641690154664177103545 18788731267615998132827659)
      ·
        refine ⟨28183096901423997199241489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18788731267615998132827659 28183096901423997199241489)
        ·
          refine ⟨21137322676067997899431117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28183096901423997199241489 21137322676067997899431117)
          ·
            refine ⟨7926496003525499212286669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21137322676067997899431117 7926496003525499212286669)
            ·
              refine ⟨2972436001322062204607501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7926496003525499212286669 2972436001322062204607501)
              ·
                refine ⟨1114663500495773326727813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2972436001322062204607501 1114663500495773326727813)
                ·
                  refine ⟨208999406342957498761465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1114663500495773326727813 208999406342957498761465)
                  ·
                    rfl

theorem cell20_457903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 3, 3, 4].length) (baseStart_457903 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_457903 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_457903 prefixEnd_457903 := by exact prefixLift 457903
  have htrace : WordTrace (prefixWord ++ tailWord_457903) baseStart_457903 baseEnd_457903 := by
    simpa [prefixWord, tailWord_457903, baseEnd_457903] using wordTrace_append hprefix tailTrace_457903
  have hstable : (prefixWord ++ tailWord_457903).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_457903).length < 2 ^ (prefixWord ++ tailWord_457903).sum := by decide
  have hdescent : baseEnd_457903 < baseStart_457903 := by decide
  rcases family_descends (prefixWord ++ tailWord_457903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_457944 : List Nat := [2, 1, 2, 2, 6, 1, 6]
def baseStart_457944 : Nat := 118140960795 + 457944 * 2 ^ 59
def prefixEnd_457944 : Nat := 4983230072969 + 3 ^ 40 * 457944 * 2
def baseEnd_457944 : Nat := 23224235540015953154959

theorem tailTrace_457944 : CollatzResearch.WordTrace tailWord_457944 prefixEnd_457944 23224235540015953154959 := by
  unfold tailWord_457944
  simp only [CollatzResearch.WordTrace]
  refine ⟨8351294926477286726822443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11135059901969715635763257 8351294926477286726822443)
  ·
    refine ⟨12526942389715930090233665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8351294926477286726822443 12526942389715930090233665)
    ·
      refine ⟨9395206792286947567675249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12526942389715930090233665 9395206792286947567675249)
      ·
        refine ⟨7046405094215210675756437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9395206792286947567675249 7046405094215210675756437)
        ·
          refine ⟨330300238791338000426083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 7046405094215210675756437 330300238791338000426083)
          ·
            refine ⟨495450358187007000639125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 330300238791338000426083 495450358187007000639125)
            ·
              refine ⟨23224235540015953154959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 495450358187007000639125 23224235540015953154959)
              ·
                rfl

theorem cell20_457944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 6, 1, 6].length) (baseStart_457944 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_457944 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_457944 prefixEnd_457944 := by exact prefixLift 457944
  have htrace : WordTrace (prefixWord ++ tailWord_457944) baseStart_457944 baseEnd_457944 := by
    simpa [prefixWord, tailWord_457944, baseEnd_457944] using wordTrace_append hprefix tailTrace_457944
  have hstable : (prefixWord ++ tailWord_457944).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_457944).length < 2 ^ (prefixWord ++ tailWord_457944).sum := by decide
  have hdescent : baseEnd_457944 < baseStart_457944 := by decide
  rcases family_descends (prefixWord ++ tailWord_457944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_457965 : List Nat := [1, 5, 1, 2, 2, 1, 1, 7]
def baseStart_457965 : Nat := 118140960795 + 457965 * 2 ^ 59
def prefixEnd_457965 : Nat := 4983230072969 + 3 ^ 40 * 457965 * 2
def baseEnd_457965 : Nat := 69675901610786946231515

theorem tailTrace_457965 : CollatzResearch.WordTrace tailWord_457965 prefixEnd_457965 69675901610786946231515 := by
  unfold tailWord_457965
  simp only [CollatzResearch.WordTrace]
  refine ⟨16703355785878494040159349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11135570523918996026772899 16703355785878494040159349)
  ·
    refine ⟨1565939604926108816264939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 16703355785878494040159349 1565939604926108816264939)
    ·
      refine ⟨2348909407389163224397409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1565939604926108816264939 2348909407389163224397409)
      ·
        refine ⟨1761682055541872418298057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2348909407389163224397409 1761682055541872418298057)
        ·
          refine ⟨1321261541656404313723543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1761682055541872418298057 1321261541656404313723543)
          ·
            refine ⟨1981892312484606470585315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1321261541656404313723543 1981892312484606470585315)
            ·
              refine ⟨2972838468726909705877973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1981892312484606470585315 2972838468726909705877973)
              ·
                refine ⟨69675901610786946231515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2972838468726909705877973 69675901610786946231515)
                ·
                  rfl

theorem cell20_457965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 1, 7].length) (baseStart_457965 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_457965 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_457965 prefixEnd_457965 := by exact prefixLift 457965
  have htrace : WordTrace (prefixWord ++ tailWord_457965) baseStart_457965 baseEnd_457965 := by
    simpa [prefixWord, tailWord_457965, baseEnd_457965] using wordTrace_append hprefix tailTrace_457965
  have hstable : (prefixWord ++ tailWord_457965).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_457965).length < 2 ^ (prefixWord ++ tailWord_457965).sum := by decide
  have hdescent : baseEnd_457965 < baseStart_457965 := by decide
  rcases family_descends (prefixWord ++ tailWord_457965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_458017 : List Nat := [1, 2, 3, 2, 1, 1, 1, 5, 4]
def baseStart_458017 : Nat := 118140960795 + 458017 * 2 ^ 59
def prefixEnd_458017 : Nat := 4983230072969 + 3 ^ 40 * 458017 * 2
def baseEnd_458017 : Nat := 209051439049279768960999

theorem tailTrace_458017 : CollatzResearch.WordTrace tailWord_458017 prefixEnd_458017 209051439049279768960999 := by
  unfold tailWord_458017
  simp only [CollatzResearch.WordTrace]
  refine ⟨16705252381690106921052305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11136834921126737947368203 16705252381690106921052305)
  ·
    refine ⟨12528939286267580190789229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16705252381690106921052305 12528939286267580190789229)
    ·
      refine ⟨4698352232350342571545961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12528939286267580190789229 4698352232350342571545961)
      ·
        refine ⟨3523764174262756928659471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4698352232350342571545961 3523764174262756928659471)
        ·
          refine ⟨5285646261394135392989207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3523764174262756928659471 5285646261394135392989207)
          ·
            refine ⟨7928469392091203089483811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5285646261394135392989207 7928469392091203089483811)
            ·
              refine ⟨11892704088136804634225717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7928469392091203089483811 11892704088136804634225717)
              ·
                refine ⟨1114941008262825434458661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 11892704088136804634225717 1114941008262825434458661)
                ·
                  refine ⟨209051439049279768960999, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1114941008262825434458661 209051439049279768960999)
                  ·
                    rfl

theorem cell20_458017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 5, 4].length) (baseStart_458017 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_458017 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_458017 prefixEnd_458017 := by exact prefixLift 458017
  have htrace : WordTrace (prefixWord ++ tailWord_458017) baseStart_458017 baseEnd_458017 := by
    simpa [prefixWord, tailWord_458017, baseEnd_458017] using wordTrace_append hprefix tailTrace_458017
  have hstable : (prefixWord ++ tailWord_458017).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_458017).length < 2 ^ (prefixWord ++ tailWord_458017).sum := by decide
  have hdescent : baseEnd_458017 < baseStart_458017 := by decide
  rcases family_descends (prefixWord ++ tailWord_458017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_458031 : List Nat := [1, 1, 2, 1, 2, 1, 3, 2, 7]
def baseStart_458031 : Nat := 118140960795 + 458031 * 2 ^ 59
def prefixEnd_458031 : Nat := 4983230072969 + 3 ^ 40 * 458031 * 2
def baseEnd_458031 : Nat := 209057829030757942494275

theorem tailTrace_458031 : CollatzResearch.WordTrace tailWord_458031 prefixEnd_458031 209057829030757942494275 := by
  unfold tailWord_458031
  simp only [CollatzResearch.WordTrace]
  refine ⟨16705763003639387312061947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11137175335759591541374631 16705763003639387312061947)
  ·
    refine ⟨25058644505459080968092921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16705763003639387312061947 25058644505459080968092921)
    ·
      refine ⟨18793983379094310726069691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25058644505459080968092921 18793983379094310726069691)
      ·
        refine ⟨28190975068641466089104537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18793983379094310726069691 28190975068641466089104537)
        ·
          refine ⟨21143231301481099566828403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28190975068641466089104537 21143231301481099566828403)
          ·
            refine ⟨31714846952221649350242605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21143231301481099566828403 31714846952221649350242605)
            ·
              refine ⟨11893067607083118506340977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31714846952221649350242605 11893067607083118506340977)
              ·
                refine ⟨8919800705312338879755733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11893067607083118506340977 8919800705312338879755733)
                ·
                  refine ⟨209057829030757942494275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8919800705312338879755733 209057829030757942494275)
                  ·
                    rfl

theorem cell20_458031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 2, 7].length) (baseStart_458031 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_458031 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_458031 prefixEnd_458031 := by exact prefixLift 458031
  have htrace : WordTrace (prefixWord ++ tailWord_458031) baseStart_458031 baseEnd_458031 := by
    simpa [prefixWord, tailWord_458031, baseEnd_458031] using wordTrace_append hprefix tailTrace_458031
  have hstable : (prefixWord ++ tailWord_458031).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_458031).length < 2 ^ (prefixWord ++ tailWord_458031).sum := by decide
  have hdescent : baseEnd_458031 < baseStart_458031 := by decide
  rcases family_descends (prefixWord ++ tailWord_458031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_458034 : List Nat := [3, 2, 1, 1, 4, 2, 1, 2, 4]
def baseStart_458034 : Nat := 118140960795 + 458034 * 2 ^ 59
def prefixEnd_458034 : Nat := 4983230072969 + 3 ^ 40 * 458034 * 2
def baseEnd_458034 : Nat := 209059198312503265394263

theorem tailTrace_458034 : CollatzResearch.WordTrace tailWord_458034 prefixEnd_458034 209059198312503265394263 := by
  unfold tailWord_458034
  simp only [CollatzResearch.WordTrace]
  refine ⟨4176468105657129706105289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11137248281752345882947437 4176468105657129706105289)
  ·
    refine ⟨3132351079242847279578967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4176468105657129706105289 3132351079242847279578967)
    ·
      refine ⟨4698526618864270919368451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3132351079242847279578967 4698526618864270919368451)
      ·
        refine ⟨7047789928296406379052677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4698526618864270919368451 7047789928296406379052677)
        ·
          refine ⟨1321460611555576196072377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7047789928296406379052677 1321460611555576196072377)
          ·
            refine ⟨991095458666682147054283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1321460611555576196072377 991095458666682147054283)
            ·
              refine ⟨1486643188000023220581425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 991095458666682147054283 1486643188000023220581425)
              ·
                refine ⟨1114982391000017415436069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1486643188000023220581425 1114982391000017415436069)
                ·
                  refine ⟨209059198312503265394263, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1114982391000017415436069 209059198312503265394263)
                  ·
                    rfl

theorem cell20_458034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 2, 1, 2, 4].length) (baseStart_458034 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_458034 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_458034 prefixEnd_458034 := by exact prefixLift 458034
  have htrace : WordTrace (prefixWord ++ tailWord_458034) baseStart_458034 baseEnd_458034 := by
    simpa [prefixWord, tailWord_458034, baseEnd_458034] using wordTrace_append hprefix tailTrace_458034
  have hstable : (prefixWord ++ tailWord_458034).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_458034).length < 2 ^ (prefixWord ++ tailWord_458034).sum := by decide
  have hdescent : baseEnd_458034 < baseStart_458034 := by decide
  rcases family_descends (prefixWord ++ tailWord_458034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_458062 : List Nat := [4, 1, 1, 1, 1, 1, 11]
def baseStart_458062 : Nat := 118140960795 + 458062 * 2 ^ 59
def prefixEnd_458062 : Nat := 4983230072969 + 3 ^ 40 * 458062 * 2
def baseEnd_458062 : Nat := 23230219808384401384535

theorem tailTrace_458062 : CollatzResearch.WordTrace tailWord_458062 prefixEnd_458062 23230219808384401384535 := by
  unfold tailWord_458062
  simp only [CollatzResearch.WordTrace]
  refine ⟨2088361708315884950805055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11137929111018053070960293 2088361708315884950805055)
  ·
    refine ⟨3132542562473827426207583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2088361708315884950805055 3132542562473827426207583)
    ·
      refine ⟨4698813843710741139311375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3132542562473827426207583 4698813843710741139311375)
      ·
        refine ⟨7048220765566111708967063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4698813843710741139311375 7048220765566111708967063)
        ·
          refine ⟨10572331148349167563450595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7048220765566111708967063 10572331148349167563450595)
          ·
            refine ⟨15858496722523751345175893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10572331148349167563450595 15858496722523751345175893)
            ·
              refine ⟨23230219808384401384535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 15858496722523751345175893 23230219808384401384535)
              ·
                rfl

theorem cell20_458062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 11].length) (baseStart_458062 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_458062 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_458062 prefixEnd_458062 := by exact prefixLift 458062
  have htrace : WordTrace (prefixWord ++ tailWord_458062) baseStart_458062 baseEnd_458062 := by
    simpa [prefixWord, tailWord_458062, baseEnd_458062] using wordTrace_append hprefix tailTrace_458062
  have hstable : (prefixWord ++ tailWord_458062).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_458062).length < 2 ^ (prefixWord ++ tailWord_458062).sum := by decide
  have hdescent : baseEnd_458062 < baseStart_458062 := by decide
  rcases family_descends (prefixWord ++ tailWord_458062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_458072 : List Nat := [2, 1, 2, 2, 1, 1, 3, 6, 2]
def baseStart_458072 : Nat := 118140960795 + 458072 * 2 ^ 59
def prefixEnd_458072 : Nat := 4983230072969 + 3 ^ 40 * 458072 * 2
def baseEnd_458072 : Nat := 209076542547944022127441

theorem tailTrace_458072 : CollatzResearch.WordTrace tailWord_458072 prefixEnd_458072 209076542547944022127441 := by
  unfold tailWord_458072
  simp only [CollatzResearch.WordTrace]
  refine ⟨8353629198245425657152235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11138172264327234209536313 8353629198245425657152235)
  ·
    refine ⟨12530443797368138485728353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8353629198245425657152235 12530443797368138485728353)
    ·
      refine ⟨9397832848026103864296265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12530443797368138485728353 9397832848026103864296265)
      ·
        refine ⟨7048374636019577898222199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9397832848026103864296265 7048374636019577898222199)
        ·
          refine ⟨10572561954029366847333299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7048374636019577898222199 10572561954029366847333299)
          ·
            refine ⟨15858842931044050270999949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10572561954029366847333299 15858842931044050270999949)
            ·
              refine ⟨5947066099141518851624981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15858842931044050270999949 5947066099141518851624981)
              ·
                refine ⟨278768723397258696169921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 5947066099141518851624981 278768723397258696169921)
                ·
                  refine ⟨209076542547944022127441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 278768723397258696169921 209076542547944022127441)
                  ·
                    rfl

theorem cell20_458072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 3, 6, 2].length) (baseStart_458072 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_458072 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_458072 prefixEnd_458072 := by exact prefixLift 458072
  have htrace : WordTrace (prefixWord ++ tailWord_458072) baseStart_458072 baseEnd_458072 := by
    simpa [prefixWord, tailWord_458072, baseEnd_458072] using wordTrace_append hprefix tailTrace_458072
  have hstable : (prefixWord ++ tailWord_458072).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_458072).length < 2 ^ (prefixWord ++ tailWord_458072).sum := by decide
  have hdescent : baseEnd_458072 < baseStart_458072 := by decide
  rcases family_descends (prefixWord ++ tailWord_458072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_458082 : List Nat := [3, 3, 2, 1, 1, 1, 5, 1, 3]
def baseStart_458082 : Nat := 118140960795 + 458082 * 2 ^ 59
def prefixEnd_458082 : Nat := 4983230072969 + 3 ^ 40 * 458082 * 2
def baseEnd_458082 : Nat := 209081106820428431794067

theorem tailTrace_458082 : CollatzResearch.WordTrace tailWord_458082 prefixEnd_458082 209081106820428431794067 := by
  unfold tailWord_458082
  simp only [CollatzResearch.WordTrace]
  refine ⟨4176905781613655755542125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11138415417636415348112333 4176905781613655755542125)
  ·
    refine ⟨1566339668105120908328297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4176905781613655755542125 1566339668105120908328297)
    ·
      refine ⟨1174754751078840681246223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1566339668105120908328297 1174754751078840681246223)
      ·
        refine ⟨1762132126618261021869335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1174754751078840681246223 1762132126618261021869335)
        ·
          refine ⟨2643198189927391532804003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1762132126618261021869335 2643198189927391532804003)
          ·
            refine ⟨3964797284891087299206005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2643198189927391532804003 3964797284891087299206005)
            ·
              refine ⟨371699745458539434300563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3964797284891087299206005 371699745458539434300563)
              ·
                refine ⟨557549618187809151450845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 371699745458539434300563 557549618187809151450845)
                ·
                  refine ⟨209081106820428431794067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 557549618187809151450845 209081106820428431794067)
                  ·
                    rfl

theorem cell20_458082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 5, 1, 3].length) (baseStart_458082 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_458082 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_458082 prefixEnd_458082 := by exact prefixLift 458082
  have htrace : WordTrace (prefixWord ++ tailWord_458082) baseStart_458082 baseEnd_458082 := by
    simpa [prefixWord, tailWord_458082, baseEnd_458082] using wordTrace_append hprefix tailTrace_458082
  have hstable : (prefixWord ++ tailWord_458082).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_458082).length < 2 ^ (prefixWord ++ tailWord_458082).sum := by decide
  have hdescent : baseEnd_458082 < baseStart_458082 := by decide
  rcases family_descends (prefixWord ++ tailWord_458082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_458107 : List Nat := [1, 1, 1, 1, 1, 6, 1, 1, 7]
def baseStart_458107 : Nat := 118140960795 + 458107 * 2 ^ 59
def prefixEnd_458107 : Nat := 4983230072969 + 3 ^ 40 * 458107 * 2
def baseEnd_458107 : Nat := 209092517501639455960631

theorem tailTrace_458107 : CollatzResearch.WordTrace tailWord_458107 prefixEnd_458107 209092517501639455960631 := by
  unfold tailWord_458107
  simp only [CollatzResearch.WordTrace]
  refine ⟨16708534951364052291828575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11139023300909368194552383 16708534951364052291828575)
  ·
    refine ⟨25062802427046078437742863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16708534951364052291828575 25062802427046078437742863)
    ·
      refine ⟨37594203640569117656614295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25062802427046078437742863 37594203640569117656614295)
      ·
        refine ⟨56391305460853676484921443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37594203640569117656614295 56391305460853676484921443)
        ·
          refine ⟨84586958191280514727382165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56391305460853676484921443 84586958191280514727382165)
          ·
            refine ⟨3965013665216274127846039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 84586958191280514727382165 3965013665216274127846039)
            ·
              refine ⟨5947520497824411191769059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3965013665216274127846039 5947520497824411191769059)
              ·
                refine ⟨8921280746736616787653589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5947520497824411191769059 8921280746736616787653589)
                ·
                  refine ⟨209092517501639455960631, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8921280746736616787653589 209092517501639455960631)
                  ·
                    rfl

theorem cell20_458107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 1, 1, 7].length) (baseStart_458107 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_458107 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_458107 prefixEnd_458107 := by exact prefixLift 458107
  have htrace : WordTrace (prefixWord ++ tailWord_458107) baseStart_458107 baseEnd_458107 := by
    simpa [prefixWord, tailWord_458107, baseEnd_458107] using wordTrace_append hprefix tailTrace_458107
  have hstable : (prefixWord ++ tailWord_458107).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_458107).length < 2 ^ (prefixWord ++ tailWord_458107).sum := by decide
  have hdescent : baseEnd_458107 < baseStart_458107 := by decide
  rcases family_descends (prefixWord ++ tailWord_458107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_458124 : List Nat := [2, 2, 1, 2, 1, 3, 2, 4, 3]
def baseStart_458124 : Nat := 118140960795 + 458124 * 2 ^ 59
def prefixEnd_458124 : Nat := 4983230072969 + 3 ^ 40 * 458124 * 2
def baseEnd_458124 : Nat := 209100276764862952393895

theorem tailTrace_458124 : CollatzResearch.WordTrace tailWord_458124 prefixEnd_458124 209100276764862952393895 := by
  unfold tailWord_458124
  simp only [CollatzResearch.WordTrace]
  refine ⟨8354577496151232097598713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11139436661534976130131617 8354577496151232097598713)
  ·
    refine ⟨6265933122113424073199035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8354577496151232097598713 6265933122113424073199035)
    ·
      refine ⟨9398899683170136109798553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6265933122113424073199035 9398899683170136109798553)
      ·
        refine ⟨7049174762377602082348915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9398899683170136109798553 7049174762377602082348915)
        ·
          refine ⟨10573762143566403123523373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7049174762377602082348915 10573762143566403123523373)
          ·
            refine ⟨3965160803837401171321265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10573762143566403123523373 3965160803837401171321265)
            ·
              refine ⟨2973870602878050878490949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3965160803837401171321265 2973870602878050878490949)
              ·
                refine ⟨557600738039634539717053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2973870602878050878490949 557600738039634539717053)
                ·
                  refine ⟨209100276764862952393895, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 557600738039634539717053 209100276764862952393895)
                  ·
                    rfl

theorem cell20_458124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 2, 4, 3].length) (baseStart_458124 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_458124 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_458124 prefixEnd_458124 := by exact prefixLift 458124
  have htrace : WordTrace (prefixWord ++ tailWord_458124) baseStart_458124 baseEnd_458124 := by
    simpa [prefixWord, tailWord_458124, baseEnd_458124] using wordTrace_append hprefix tailTrace_458124
  have hstable : (prefixWord ++ tailWord_458124).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_458124).length < 2 ^ (prefixWord ++ tailWord_458124).sum := by decide
  have hdescent : baseEnd_458124 < baseStart_458124 := by decide
  rcases family_descends (prefixWord ++ tailWord_458124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_458141 : List Nat := [1, 4, 2, 1, 3, 2, 1, 3, 3]
def baseStart_458141 : Nat := 118140960795 + 458141 * 2 ^ 59
def prefixEnd_458141 : Nat := 4983230072969 + 3 ^ 40 * 458141 * 2
def baseEnd_458141 : Nat := 209108036028086448827159

theorem tailTrace_458141 : CollatzResearch.WordTrace tailWord_458141 prefixEnd_458141 209108036028086448827159 := by
  unfold tailWord_458141
  simp only [CollatzResearch.WordTrace]
  refine ⟨16709775033240876098566277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11139850022160584065710851 16709775033240876098566277)
  ·
    refine ⟨3133082818732664268481177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16709775033240876098566277 3133082818732664268481177)
    ·
      refine ⟨2349812114049498201360883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3133082818732664268481177 2349812114049498201360883)
      ·
        refine ⟨3524718171074247302041325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2349812114049498201360883 3524718171074247302041325)
        ·
          refine ⟨1321769314152842738265497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3524718171074247302041325 1321769314152842738265497)
          ·
            refine ⟨991326985614632053699123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1321769314152842738265497 991326985614632053699123)
            ·
              refine ⟨1486990478421948080548685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 991326985614632053699123 1486990478421948080548685)
              ·
                refine ⟨557621429408230530205757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1486990478421948080548685 557621429408230530205757)
                ·
                  refine ⟨209108036028086448827159, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 557621429408230530205757 209108036028086448827159)
                  ·
                    rfl

theorem cell20_458141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 2, 1, 3, 3].length) (baseStart_458141 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_458141 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_458141 prefixEnd_458141 := by exact prefixLift 458141
  have htrace : WordTrace (prefixWord ++ tailWord_458141) baseStart_458141 baseEnd_458141 := by
    simpa [prefixWord, tailWord_458141, baseEnd_458141] using wordTrace_append hprefix tailTrace_458141
  have hstable : (prefixWord ++ tailWord_458141).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_458141).length < 2 ^ (prefixWord ++ tailWord_458141).sum := by decide
  have hdescent : baseEnd_458141 < baseStart_458141 := by decide
  rcases family_descends (prefixWord ++ tailWord_458141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_458200 : List Nat := [2, 1, 2, 2, 2, 1, 4, 3, 3]
def baseStart_458200 : Nat := 118140960795 + 458200 * 2 ^ 59
def prefixEnd_458200 : Nat := 4983230072969 + 3 ^ 40 * 458200 * 2
def baseEnd_458200 : Nat := 209134965235744465860251

theorem tailTrace_458200 : CollatzResearch.WordTrace tailWord_458200 prefixEnd_458200 209134965235744465860251 := by
  unfold tailWord_458200
  simp only [CollatzResearch.WordTrace]
  refine ⟨8355963470013564587482027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11141284626684752783309369 8355963470013564587482027)
  ·
    refine ⟨12533945205020346881223041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8355963470013564587482027 12533945205020346881223041)
    ·
      refine ⟨9400458903765260160917281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12533945205020346881223041 9400458903765260160917281)
      ·
        refine ⟨7050344177823945120687961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9400458903765260160917281 7050344177823945120687961)
        ·
          refine ⟨5287758133367958840515971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7050344177823945120687961 5287758133367958840515971)
          ·
            refine ⟨7931637200051938260773957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5287758133367958840515971 7931637200051938260773957)
            ·
              refine ⟨1487181975009738423895117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7931637200051938260773957 1487181975009738423895117)
              ·
                refine ⟨557693240628651908960669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1487181975009738423895117 557693240628651908960669)
                ·
                  refine ⟨209134965235744465860251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 557693240628651908960669 209134965235744465860251)
                  ·
                    rfl

theorem cell20_458200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 4, 3, 3].length) (baseStart_458200 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_458200 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_458200 prefixEnd_458200 := by exact prefixLift 458200
  have htrace : WordTrace (prefixWord ++ tailWord_458200) baseStart_458200 baseEnd_458200 := by
    simpa [prefixWord, tailWord_458200, baseEnd_458200] using wordTrace_append hprefix tailTrace_458200
  have hstable : (prefixWord ++ tailWord_458200).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_458200).length < 2 ^ (prefixWord ++ tailWord_458200).sum := by decide
  have hdescent : baseEnd_458200 < baseStart_458200 := by decide
  rcases family_descends (prefixWord ++ tailWord_458200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_458207 : List Nat := [1, 1, 2, 3, 3, 1, 3, 2, 4]
def baseStart_458207 : Nat := 118140960795 + 458207 * 2 ^ 59
def prefixEnd_458207 : Nat := 4983230072969 + 3 ^ 40 * 458207 * 2
def baseEnd_458207 : Nat := 209138160226483552626889

theorem tailTrace_458207 : CollatzResearch.WordTrace tailWord_458207 prefixEnd_458207 209138160226483552626889 := by
  unfold tailWord_458207
  simp only [CollatzResearch.WordTrace]
  refine ⟨16712182251001769370468875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11141454834001179580312583 16712182251001769370468875)
  ·
    refine ⟨25068273376502654055703313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16712182251001769370468875 25068273376502654055703313)
    ·
      refine ⟨18801205032376990541777485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25068273376502654055703313 18801205032376990541777485)
      ·
        refine ⟨7050451887141371453166557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18801205032376990541777485 7050451887141371453166557)
        ·
          refine ⟨2643919457678014294937459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7050451887141371453166557 2643919457678014294937459)
          ·
            refine ⟨3965879186517021442406189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2643919457678014294937459 3965879186517021442406189)
            ·
              refine ⟨1487204694943883040902321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3965879186517021442406189 1487204694943883040902321)
              ·
                refine ⟨1115403521207912280676741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1487204694943883040902321 1115403521207912280676741)
                ·
                  refine ⟨209138160226483552626889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1115403521207912280676741 209138160226483552626889)
                  ·
                    rfl

theorem cell20_458207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 3, 2, 4].length) (baseStart_458207 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_458207 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_458207 prefixEnd_458207 := by exact prefixLift 458207
  have htrace : WordTrace (prefixWord ++ tailWord_458207) baseStart_458207 baseEnd_458207 := by
    simpa [prefixWord, tailWord_458207, baseEnd_458207] using wordTrace_append hprefix tailTrace_458207
  have hstable : (prefixWord ++ tailWord_458207).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_458207).length < 2 ^ (prefixWord ++ tailWord_458207).sum := by decide
  have hdescent : baseEnd_458207 < baseStart_458207 := by decide
  rcases family_descends (prefixWord ++ tailWord_458207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_458224 : List Nat := [2, 1, 1, 1, 3, 4, 1, 5, 2]
def baseStart_458224 : Nat := 118140960795 + 458224 * 2 ^ 59
def prefixEnd_458224 : Nat := 4983230072969 + 3 ^ 40 * 458224 * 2
def baseEnd_458224 : Nat := 209145919489707049060153

theorem tailTrace_458224 : CollatzResearch.WordTrace tailWord_458224 prefixEnd_458224 209145919489707049060153 := by
  unfold tailWord_458224
  simp only [CollatzResearch.WordTrace]
  refine ⟨8356401145970090636918863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11141868194626787515891817 8356401145970090636918863)
  ·
    refine ⟨12534601718955135955378295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8356401145970090636918863 12534601718955135955378295)
    ·
      refine ⟨18801902578432703933067443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12534601718955135955378295 18801902578432703933067443)
      ·
        refine ⟨28202853867649055899601165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18801902578432703933067443 28202853867649055899601165)
        ·
          refine ⟨10576070200368395962350437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28202853867649055899601165 10576070200368395962350437)
          ·
            refine ⟨1983013162569074242940707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10576070200368395962350437 1983013162569074242940707)
            ·
              refine ⟨2974519743853611364411061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1983013162569074242940707 2974519743853611364411061)
              ·
                refine ⟨278861225986276065413537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2974519743853611364411061 278861225986276065413537)
                ·
                  refine ⟨209145919489707049060153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 278861225986276065413537 209145919489707049060153)
                  ·
                    rfl

theorem cell20_458224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 1, 5, 2].length) (baseStart_458224 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_458224 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_458224 prefixEnd_458224 := by exact prefixLift 458224
  have htrace : WordTrace (prefixWord ++ tailWord_458224) baseStart_458224 baseEnd_458224 := by
    simpa [prefixWord, tailWord_458224, baseEnd_458224] using wordTrace_append hprefix tailTrace_458224
  have hstable : (prefixWord ++ tailWord_458224).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_458224).length < 2 ^ (prefixWord ++ tailWord_458224).sum := by decide
  have hdescent : baseEnd_458224 < baseStart_458224 := by decide
  rcases family_descends (prefixWord ++ tailWord_458224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_458314 : List Nat := [3, 1, 2, 1, 1, 3, 3, 3, 3]
def baseStart_458314 : Nat := 118140960795 + 458314 * 2 ^ 59
def prefixEnd_458314 : Nat := 4983230072969 + 3 ^ 40 * 458314 * 2
def baseEnd_458314 : Nat := 209186997942066736059785

theorem tailTrace_458314 : CollatzResearch.WordTrace tailWord_458314 prefixEnd_458314 209186997942066736059785 := by
  unfold tailWord_458314
  simp only [CollatzResearch.WordTrace]
  refine ⟨4179021215403531661153499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11144056574409417763075997 4179021215403531661153499)
  ·
    refine ⟨6268531823105297491730249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4179021215403531661153499 6268531823105297491730249)
    ·
      refine ⟨4701398867328973118797687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6268531823105297491730249 4701398867328973118797687)
      ·
        refine ⟨7052098300993459678196531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4701398867328973118797687 7052098300993459678196531)
        ·
          refine ⟨10578147451490189517294797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7052098300993459678196531 10578147451490189517294797)
          ·
            refine ⟨3966805294308821068985549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10578147451490189517294797 3966805294308821068985549)
            ·
              refine ⟨1487551985365807900869581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3966805294308821068985549 1487551985365807900869581)
              ·
                refine ⟨557831994512177962826093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1487551985365807900869581 557831994512177962826093)
                ·
                  refine ⟨209186997942066736059785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 557831994512177962826093 209186997942066736059785)
                  ·
                    rfl

theorem cell20_458314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 3, 3, 3].length) (baseStart_458314 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_458314 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_458314 prefixEnd_458314 := by exact prefixLift 458314
  have htrace : WordTrace (prefixWord ++ tailWord_458314) baseStart_458314 baseEnd_458314 := by
    simpa [prefixWord, tailWord_458314, baseEnd_458314] using wordTrace_append hprefix tailTrace_458314
  have hstable : (prefixWord ++ tailWord_458314).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_458314).length < 2 ^ (prefixWord ++ tailWord_458314).sum := by decide
  have hdescent : baseEnd_458314 < baseStart_458314 := by decide
  rcases family_descends (prefixWord ++ tailWord_458314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_458352 : List Nat := [2, 1, 1, 1, 6, 1, 1, 4, 3]
def baseStart_458352 : Nat := 118140960795 + 458352 * 2 ^ 59
def prefixEnd_458352 : Nat := 4983230072969 + 3 ^ 40 * 458352 * 2
def baseEnd_458352 : Nat := 209204342177507492792963

theorem tailTrace_458352 : CollatzResearch.WordTrace tailWord_458352 prefixEnd_458352 209204342177507492792963 := by
  unfold tailWord_458352
  simp only [CollatzResearch.WordTrace]
  refine ⟨8358735417738229567248655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11144980556984306089664873 8358735417738229567248655)
  ·
    refine ⟨12538103126607344350872983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8358735417738229567248655 12538103126607344350872983)
    ·
      refine ⟨18807154689911016526309475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12538103126607344350872983 18807154689911016526309475)
      ·
        refine ⟨28210732034866524789464213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18807154689911016526309475 28210732034866524789464213)
        ·
          refine ⟨1322378064134368349506135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 28210732034866524789464213 1322378064134368349506135)
          ·
            refine ⟨1983567096201552524259203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1322378064134368349506135 1983567096201552524259203)
            ·
              refine ⟨2975350644302328786388805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1983567096201552524259203 2975350644302328786388805)
              ·
                refine ⟨557878245806686647447901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2975350644302328786388805 557878245806686647447901)
                ·
                  refine ⟨209204342177507492792963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 557878245806686647447901 209204342177507492792963)
                  ·
                    rfl

theorem cell20_458352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 1, 4, 3].length) (baseStart_458352 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_458352 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_458352 prefixEnd_458352 := by exact prefixLift 458352
  have htrace : WordTrace (prefixWord ++ tailWord_458352) baseStart_458352 baseEnd_458352 := by
    simpa [prefixWord, tailWord_458352, baseEnd_458352] using wordTrace_append hprefix tailTrace_458352
  have hstable : (prefixWord ++ tailWord_458352).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_458352).length < 2 ^ (prefixWord ++ tailWord_458352).sum := by decide
  have hdescent : baseEnd_458352 < baseStart_458352 := by decide
  rcases family_descends (prefixWord ++ tailWord_458352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_458404 : List Nat := [2, 3, 1, 2, 2, 3, 7]
def baseStart_458404 : Nat := 118140960795 + 458404 * 2 ^ 59
def prefixEnd_458404 : Nat := 4983230072969 + 3 ^ 40 * 458404 * 2
def baseEnd_458404 : Nat := 23247564043825158117713

theorem tailTrace_458404 : CollatzResearch.WordTrace tailWord_458404 prefixEnd_458404 23247564043825158117713 := by
  unfold tailWord_458404
  simp only [CollatzResearch.WordTrace]
  refine ⟨8359683715644036007695133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11146244954192048010260177 8359683715644036007695133)
  ·
    refine ⟨3134881393366513502885675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8359683715644036007695133 3134881393366513502885675)
    ·
      refine ⟨4702322090049770254328513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3134881393366513502885675 4702322090049770254328513)
      ·
        refine ⟨3526741567537327690746385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4702322090049770254328513 3526741567537327690746385)
        ·
          refine ⟨2645056175652995768059789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3526741567537327690746385 2645056175652995768059789)
          ·
            refine ⟨991896065869873413022421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2645056175652995768059789 991896065869873413022421)
            ·
              refine ⟨23247564043825158117713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 991896065869873413022421 23247564043825158117713)
              ·
                rfl

theorem cell20_458404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 3, 7].length) (baseStart_458404 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_458404 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_458404 prefixEnd_458404 := by exact prefixLift 458404
  have htrace : WordTrace (prefixWord ++ tailWord_458404) baseStart_458404 baseEnd_458404 := by
    simpa [prefixWord, tailWord_458404, baseEnd_458404] using wordTrace_append hprefix tailTrace_458404
  have hstable : (prefixWord ++ tailWord_458404).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_458404).length < 2 ^ (prefixWord ++ tailWord_458404).sum := by decide
  have hdescent : baseEnd_458404 < baseStart_458404 := by decide
  rcases family_descends (prefixWord ++ tailWord_458404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_458445 : List Nat := [1, 6, 2, 1, 1, 1, 1, 2, 5]
def baseStart_458445 : Nat := 118140960795 + 458445 * 2 ^ 59
def prefixEnd_458445 : Nat := 4983230072969 + 3 ^ 40 * 458445 * 2
def baseEnd_458445 : Nat := 209246789911612502692583

theorem tailTrace_458445 : CollatzResearch.WordTrace tailWord_458445 prefixEnd_458445 209246789911612502692583 := by
  unfold tailWord_458445
  simp only [CollatzResearch.WordTrace]
  refine ⟨16720862824139536017632789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11147241882759690678421859 16720862824139536017632789)
  ·
    refine ⟨783790444881540750826537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 16720862824139536017632789 783790444881540750826537)
    ·
      refine ⟨587842833661155563119903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 783790444881540750826537 587842833661155563119903)
      ·
        refine ⟨881764250491733344679855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 587842833661155563119903 881764250491733344679855)
        ·
          refine ⟨1322646375737600017019783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 881764250491733344679855 1322646375737600017019783)
          ·
            refine ⟨1983969563606400025529675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1322646375737600017019783 1983969563606400025529675)
            ·
              refine ⟨2975954345409600038294513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1983969563606400025529675 2975954345409600038294513)
              ·
                refine ⟨2231965759057200028720885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2975954345409600038294513 2231965759057200028720885)
                ·
                  refine ⟨209246789911612502692583, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2231965759057200028720885 209246789911612502692583)
                  ·
                    rfl

theorem cell20_458445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 1, 2, 5].length) (baseStart_458445 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_458445 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_458445 prefixEnd_458445 := by exact prefixLift 458445
  have htrace : WordTrace (prefixWord ++ tailWord_458445) baseStart_458445 baseEnd_458445 := by
    simpa [prefixWord, tailWord_458445, baseEnd_458445] using wordTrace_append hprefix tailTrace_458445
  have hstable : (prefixWord ++ tailWord_458445).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_458445).length < 2 ^ (prefixWord ++ tailWord_458445).sum := by decide
  have hdescent : baseEnd_458445 < baseStart_458445 := by decide
  rcases family_descends (prefixWord ++ tailWord_458445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_458449 : List Nat := [1, 2, 2, 1, 2, 4, 1, 2, 5]
def baseStart_458449 : Nat := 118140960795 + 458449 * 2 ^ 59
def prefixEnd_458449 : Nat := 4983230072969 + 3 ^ 40 * 458449 * 2
def baseEnd_458449 : Nat := 209248615620606266559233

theorem tailTrace_458449 : CollatzResearch.WordTrace tailWord_458449 prefixEnd_458449 209248615620606266559233 := by
  unfold tailWord_458449
  simp only [CollatzResearch.WordTrace]
  refine ⟨16721008716125044700778401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11147339144083363133852267 16721008716125044700778401)
  ·
    refine ⟨12540756537093783525583801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16721008716125044700778401 12540756537093783525583801)
    ·
      refine ⟨9405567402820337644187851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12540756537093783525583801 9405567402820337644187851)
      ·
        refine ⟨14108351104230506466281777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9405567402820337644187851 14108351104230506466281777)
        ·
          refine ⟨10581263328172879849711333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14108351104230506466281777 10581263328172879849711333)
          ·
            refine ⟨1983986874032414971820875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10581263328172879849711333 1983986874032414971820875)
            ·
              refine ⟨2975980311048622457731313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1983986874032414971820875 2975980311048622457731313)
              ·
                refine ⟨2231985233286466843298485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2975980311048622457731313 2231985233286466843298485)
                ·
                  refine ⟨209248615620606266559233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2231985233286466843298485 209248615620606266559233)
                  ·
                    rfl

theorem cell20_458449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 1, 2, 5].length) (baseStart_458449 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_458449 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_458449 prefixEnd_458449 := by exact prefixLift 458449
  have htrace : WordTrace (prefixWord ++ tailWord_458449) baseStart_458449 baseEnd_458449 := by
    simpa [prefixWord, tailWord_458449, baseEnd_458449] using wordTrace_append hprefix tailTrace_458449
  have hstable : (prefixWord ++ tailWord_458449).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_458449).length < 2 ^ (prefixWord ++ tailWord_458449).sum := by decide
  have hdescent : baseEnd_458449 < baseStart_458449 := by decide
  rcases family_descends (prefixWord ++ tailWord_458449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_458469 : List Nat := [1, 3, 1, 4, 1, 1, 5, 2, 2]
def baseStart_458469 : Nat := 118140960795 + 458469 * 2 ^ 59
def prefixEnd_458469 : Nat := 4983230072969 + 3 ^ 40 * 458469 * 2
def baseEnd_458469 : Nat := 209257744165575085892485

theorem tailTrace_458469 : CollatzResearch.WordTrace tailWord_458469 prefixEnd_458469 209257744165575085892485 := by
  unfold tailWord_458469
  simp only [CollatzResearch.WordTrace]
  refine ⟨16721738176052588116506461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11147825450701725411004307 16721738176052588116506461)
  ·
    refine ⟨6270651816019720543689923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16721738176052588116506461 6270651816019720543689923)
    ·
      refine ⟨9405977724029580815534885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6270651816019720543689923 9405977724029580815534885)
      ·
        refine ⟨1763620823255546402912791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9405977724029580815534885 1763620823255546402912791)
        ·
          refine ⟨2645431234883319604369187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1763620823255546402912791 2645431234883319604369187)
          ·
            refine ⟨3968146852324979406553781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2645431234883319604369187 3968146852324979406553781)
            ·
              refine ⟨372013767405466819364417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3968146852324979406553781 372013767405466819364417)
              ·
                refine ⟨279010325554100114523313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 372013767405466819364417 279010325554100114523313)
                ·
                  refine ⟨209257744165575085892485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 279010325554100114523313 209257744165575085892485)
                  ·
                    rfl

theorem cell20_458469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 5, 2, 2].length) (baseStart_458469 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_458469 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_458469 prefixEnd_458469 := by exact prefixLift 458469
  have htrace : WordTrace (prefixWord ++ tailWord_458469) baseStart_458469 baseEnd_458469 := by
    simpa [prefixWord, tailWord_458469, baseEnd_458469] using wordTrace_append hprefix tailTrace_458469
  have hstable : (prefixWord ++ tailWord_458469).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_458469).length < 2 ^ (prefixWord ++ tailWord_458469).sum := by decide
  have hdescent : baseEnd_458469 < baseStart_458469 := by decide
  rcases family_descends (prefixWord ++ tailWord_458469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_458528 : List Nat := [2, 1, 1, 5, 1, 1, 3, 4, 2]
def baseStart_458528 : Nat := 118140960795 + 458528 * 2 ^ 59
def prefixEnd_458528 : Nat := 4983230072969 + 3 ^ 40 * 458528 * 2
def baseEnd_458528 : Nat := 209284673373233102925577

theorem tailTrace_458528 : CollatzResearch.WordTrace tailWord_458528 prefixEnd_458528 209284673373233102925577 := by
  unfold tailWord_458528
  simp only [CollatzResearch.WordTrace]
  refine ⟨8361945041419420596452119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11149260055225894128602825 8361945041419420596452119)
  ·
    refine ⟨12542917562129130894678179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8361945041419420596452119 12542917562129130894678179)
    ·
      refine ⟨18814376343193696342017269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12542917562129130894678179 18814376343193696342017269)
      ·
        refine ⟨1763847782174409032064119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 18814376343193696342017269 1763847782174409032064119)
        ·
          refine ⟨2645771673261613548096179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1763847782174409032064119 2645771673261613548096179)
          ·
            refine ⟨3968657509892420322144269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2645771673261613548096179 3968657509892420322144269)
            ·
              refine ⟨1488246566209657620804101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3968657509892420322144269 1488246566209657620804101)
              ·
                refine ⟨279046231164310803900769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1488246566209657620804101 279046231164310803900769)
                ·
                  refine ⟨209284673373233102925577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 279046231164310803900769 209284673373233102925577)
                  ·
                    rfl

theorem cell20_458528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 3, 4, 2].length) (baseStart_458528 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_458528 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_458528 prefixEnd_458528 := by exact prefixLift 458528
  have htrace : WordTrace (prefixWord ++ tailWord_458528) baseStart_458528 baseEnd_458528 := by
    simpa [prefixWord, tailWord_458528, baseEnd_458528] using wordTrace_append hprefix tailTrace_458528
  have hstable : (prefixWord ++ tailWord_458528).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_458528).length < 2 ^ (prefixWord ++ tailWord_458528).sum := by decide
  have hdescent : baseEnd_458528 < baseStart_458528 := by decide
  rcases family_descends (prefixWord ++ tailWord_458528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_458570 : List Nat := [3, 1, 2, 1, 1, 1, 3, 2, 6]
def baseStart_458570 : Nat := 118140960795 + 458570 * 2 ^ 59
def prefixEnd_458570 : Nat := 4983230072969 + 3 ^ 40 * 458570 * 2
def baseEnd_458570 : Nat := 209303843317667623525405

theorem tailTrace_458570 : CollatzResearch.WordTrace tailWord_458570 prefixEnd_458570 209303843317667623525405 := by
  unfold tailWord_458570
  simp only [CollatzResearch.WordTrace]
  refine ⟨4181355487171670591483291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11150281299124454910622109 4181355487171670591483291)
  ·
    refine ⟨6272033230757505887224937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4181355487171670591483291 6272033230757505887224937)
    ·
      refine ⟨4704024923068129415418703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6272033230757505887224937 4704024923068129415418703)
      ·
        refine ⟨7056037384602194123128055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4704024923068129415418703 7056037384602194123128055)
        ·
          refine ⟨10584056076903291184692083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7056037384602194123128055 10584056076903291184692083)
          ·
            refine ⟨15876084115354936777038125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10584056076903291184692083 15876084115354936777038125)
            ·
              refine ⟨5953531543258101291389297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15876084115354936777038125 5953531543258101291389297)
              ·
                refine ⟨4465148657443575968541973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5953531543258101291389297 4465148657443575968541973)
                ·
                  refine ⟨209303843317667623525405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4465148657443575968541973 209303843317667623525405)
                  ·
                    rfl

theorem cell20_458570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 3, 2, 6].length) (baseStart_458570 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_458570 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_458570 prefixEnd_458570 := by exact prefixLift 458570
  have htrace : WordTrace (prefixWord ++ tailWord_458570) baseStart_458570 baseEnd_458570 := by
    simpa [prefixWord, tailWord_458570, baseEnd_458570] using wordTrace_append hprefix tailTrace_458570
  have hstable : (prefixWord ++ tailWord_458570).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_458570).length < 2 ^ (prefixWord ++ tailWord_458570).sum := by decide
  have hdescent : baseEnd_458570 < baseStart_458570 := by decide
  rcases family_descends (prefixWord ++ tailWord_458570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_458573 : List Nat := [1, 6, 1, 2, 1, 2, 7]
def baseStart_458573 : Nat := 118140960795 + 458573 * 2 ^ 59
def prefixEnd_458573 : Nat := 4983230072969 + 3 ^ 40 * 458573 * 2
def baseEnd_458573 : Nat := 23256134733268105158377

theorem tailTrace_458573 : CollatzResearch.WordTrace tailWord_458573 prefixEnd_458573 23256134733268105158377 := by
  unfold tailWord_458573
  simp only [CollatzResearch.WordTrace]
  refine ⟨16725531367675813878292373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11150354245117209252194915 16725531367675813878292373)
  ·
    refine ⟨784009282859803775544955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 16725531367675813878292373 784009282859803775544955)
    ·
      refine ⟨1176013924289705663317433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 784009282859803775544955 1176013924289705663317433)
      ·
        refine ⟨882010443217279247488075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1176013924289705663317433 882010443217279247488075)
        ·
          refine ⟨1323015664825918871232113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 882010443217279247488075 1323015664825918871232113)
          ·
            refine ⟨992261748619439153424085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1323015664825918871232113 992261748619439153424085)
            ·
              refine ⟨23256134733268105158377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 992261748619439153424085 23256134733268105158377)
              ·
                rfl

theorem cell20_458573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 2, 7].length) (baseStart_458573 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_458573 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_458573 prefixEnd_458573 := by exact prefixLift 458573
  have htrace : WordTrace (prefixWord ++ tailWord_458573) baseStart_458573 baseEnd_458573 := by
    simpa [prefixWord, tailWord_458573, baseEnd_458573] using wordTrace_append hprefix tailTrace_458573
  have hstable : (prefixWord ++ tailWord_458573).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_458573).length < 2 ^ (prefixWord ++ tailWord_458573).sum := by decide
  have hdescent : baseEnd_458573 < baseStart_458573 := by decide
  rcases family_descends (prefixWord ++ tailWord_458573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_458580 : List Nat := [2, 4, 1, 1, 3, 2, 1, 1, 5]
def baseStart_458580 : Nat := 118140960795 + 458580 * 2 ^ 59
def prefixEnd_458580 : Nat := 4983230072969 + 3 ^ 40 * 458580 * 2
def baseEnd_458580 : Nat := 209308407590152033192031

theorem tailTrace_458580 : CollatzResearch.WordTrace tailWord_458580 prefixEnd_458580 209308407590152033192031 := by
  unfold tailWord_458580
  simp only [CollatzResearch.WordTrace]
  refine ⟨8362893339325227036898597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11150524452433636049198129 8362893339325227036898597)
  ·
    refine ⟨1568042501123480069418487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8362893339325227036898597 1568042501123480069418487)
    ·
      refine ⟨2352063751685220104127731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1568042501123480069418487 2352063751685220104127731)
      ·
        refine ⟨3528095627527830156191597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2352063751685220104127731 3528095627527830156191597)
        ·
          refine ⟨1323035860322936308571849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3528095627527830156191597 1323035860322936308571849)
          ·
            refine ⟨992276895242202231428887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1323035860322936308571849 992276895242202231428887)
            ·
              refine ⟨1488415342863303347143331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 992276895242202231428887 1488415342863303347143331)
              ·
                refine ⟨2232623014294955020714997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1488415342863303347143331 2232623014294955020714997)
                ·
                  refine ⟨209308407590152033192031, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2232623014294955020714997 209308407590152033192031)
                  ·
                    rfl

theorem cell20_458580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 2, 1, 1, 5].length) (baseStart_458580 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_458580 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_458580 prefixEnd_458580 := by exact prefixLift 458580
  have htrace : WordTrace (prefixWord ++ tailWord_458580) baseStart_458580 baseEnd_458580 := by
    simpa [prefixWord, tailWord_458580, baseEnd_458580] using wordTrace_append hprefix tailTrace_458580
  have hstable : (prefixWord ++ tailWord_458580).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_458580).length < 2 ^ (prefixWord ++ tailWord_458580).sum := by decide
  have hdescent : baseEnd_458580 < baseStart_458580 := by decide
  rcases family_descends (prefixWord ++ tailWord_458580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_458601 : List Nat := [1, 2, 1, 1, 1, 3, 1, 7, 3]
def baseStart_458601 : Nat := 118140960795 + 458601 * 2 ^ 59
def prefixEnd_458601 : Nat := 4983230072969 + 3 ^ 40 * 458601 * 2
def baseEnd_458601 : Nat := 209317992562369293491945

theorem tailTrace_458601 : CollatzResearch.WordTrace tailWord_458601 prefixEnd_458601 209317992562369293491945 := by
  unfold tailWord_458601
  simp only [CollatzResearch.WordTrace]
  refine ⟨16726552611574374660311657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11151035074382916440207771 16726552611574374660311657)
  ·
    refine ⟨12544914458680780995233743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16726552611574374660311657 12544914458680780995233743)
    ·
      refine ⟨18817371688021171492850615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12544914458680780995233743 18817371688021171492850615)
      ·
        refine ⟨28226057532031757239275923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18817371688021171492850615 28226057532031757239275923)
        ·
          refine ⟨42339086298047635858913885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28226057532031757239275923 42339086298047635858913885)
          ·
            refine ⟨15877157361767863447092707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42339086298047635858913885 15877157361767863447092707)
            ·
              refine ⟨23815736042651795170639061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15877157361767863447092707 23815736042651795170639061)
              ·
                refine ⟨558181313499651449311853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 23815736042651795170639061 558181313499651449311853)
                ·
                  refine ⟨209317992562369293491945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 558181313499651449311853 209317992562369293491945)
                  ·
                    rfl

theorem cell20_458601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 7, 3].length) (baseStart_458601 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_458601 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_458601 prefixEnd_458601 := by exact prefixLift 458601
  have htrace : WordTrace (prefixWord ++ tailWord_458601) baseStart_458601 baseEnd_458601 := by
    simpa [prefixWord, tailWord_458601, baseEnd_458601] using wordTrace_append hprefix tailTrace_458601
  have hstable : (prefixWord ++ tailWord_458601).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_458601).length < 2 ^ (prefixWord ++ tailWord_458601).sum := by decide
  have hdescent : baseEnd_458601 < baseStart_458601 := by decide
  rcases family_descends (prefixWord ++ tailWord_458601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_458638 : List Nat := [4, 1, 1, 5, 2, 1, 1, 1, 4]
def baseStart_458638 : Nat := 118140960795 + 458638 * 2 ^ 59
def prefixEnd_458638 : Nat := 4983230072969 + 3 ^ 40 * 458638 * 2
def baseEnd_458638 : Nat := 209334880370561609258461

theorem tailTrace_458638 : CollatzResearch.WordTrace tailWord_458638 prefixEnd_458638 209334880370561609258461 := by
  unfold tailWord_458638
  simp only [CollatzResearch.WordTrace]
  refine ⟨2090987764055041247426071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11151934741626886652939045 2090987764055041247426071)
  ·
    refine ⟨3136481646082561871139107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2090987764055041247426071 3136481646082561871139107)
    ·
      refine ⟨4704722469123842806708661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3136481646082561871139107 4704722469123842806708661)
      ·
        refine ⟨441067731480360263128937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 4704722469123842806708661 441067731480360263128937)
        ·
          refine ⟨330800798610270197346703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 441067731480360263128937 330800798610270197346703)
          ·
            refine ⟨496201197915405296020055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 330800798610270197346703 496201197915405296020055)
            ·
              refine ⟨744301796873107944030083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 496201197915405296020055 744301796873107944030083)
              ·
                refine ⟨1116452695309661916045125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 744301796873107944030083 1116452695309661916045125)
                ·
                  refine ⟨209334880370561609258461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1116452695309661916045125 209334880370561609258461)
                  ·
                    rfl

theorem cell20_458638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 2, 1, 1, 1, 4].length) (baseStart_458638 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_458638 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_458638 prefixEnd_458638 := by exact prefixLift 458638
  have htrace : WordTrace (prefixWord ++ tailWord_458638) baseStart_458638 baseEnd_458638 := by
    simpa [prefixWord, tailWord_458638, baseEnd_458638] using wordTrace_append hprefix tailTrace_458638
  have hstable : (prefixWord ++ tailWord_458638).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_458638).length < 2 ^ (prefixWord ++ tailWord_458638).sum := by decide
  have hdescent : baseEnd_458638 < baseStart_458638 := by decide
  rcases family_descends (prefixWord ++ tailWord_458638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_458642 : List Nat := [3, 2, 3, 2, 1, 1, 3, 1, 4]
def baseStart_458642 : Nat := 118140960795 + 458642 * 2 ^ 59
def prefixEnd_458642 : Nat := 4983230072969 + 3 ^ 40 * 458642 * 2
def baseEnd_458642 : Nat := 209336706079555373125111

theorem tailTrace_458642 : CollatzResearch.WordTrace tailWord_458642 prefixEnd_458642 209336706079555373125111 := by
  unfold tailWord_458642
  simp only [CollatzResearch.WordTrace]
  refine ⟨4182012001106459665638545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11152032002950559108369453 4182012001106459665638545)
  ·
    refine ⟨3136509000829844749228909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4182012001106459665638545 3136509000829844749228909)
    ·
      refine ⟨1176190875311191780960841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3136509000829844749228909 1176190875311191780960841)
      ·
        refine ⟨882143156483393835720631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1176190875311191780960841 882143156483393835720631)
        ·
          refine ⟨1323214734725090753580947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 882143156483393835720631 1323214734725090753580947)
          ·
            refine ⟨1984822102087636130371421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1323214734725090753580947 1984822102087636130371421)
            ·
              refine ⟨744308288282863548889283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1984822102087636130371421 744308288282863548889283)
              ·
                refine ⟨1116462432424295323333925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 744308288282863548889283 1116462432424295323333925)
                ·
                  refine ⟨209336706079555373125111, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1116462432424295323333925 209336706079555373125111)
                  ·
                    rfl

theorem cell20_458642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 3, 1, 4].length) (baseStart_458642 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_458642 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_458642 prefixEnd_458642 := by exact prefixLift 458642
  have htrace : WordTrace (prefixWord ++ tailWord_458642) baseStart_458642 baseEnd_458642 := by
    simpa [prefixWord, tailWord_458642, baseEnd_458642] using wordTrace_append hprefix tailTrace_458642
  have hstable : (prefixWord ++ tailWord_458642).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_458642).length < 2 ^ (prefixWord ++ tailWord_458642).sum := by decide
  have hdescent : baseEnd_458642 < baseStart_458642 := by decide
  rcases family_descends (prefixWord ++ tailWord_458642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_458652 : List Nat := [2, 2, 3, 3, 1, 3, 2, 1, 3]
def baseStart_458652 : Nat := 118140960795 + 458652 * 2 ^ 59
def prefixEnd_458652 : Nat := 4983230072969 + 3 ^ 40 * 458652 * 2
def baseEnd_458652 : Nat := 209341270352039782791737

theorem tailTrace_458652 : CollatzResearch.WordTrace tailWord_458652 prefixEnd_458652 209341270352039782791737 := by
  unfold tailWord_458652
  simp only [CollatzResearch.WordTrace]
  refine ⟨8364206367194805185209105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11152275156259740246945473 8364206367194805185209105)
  ·
    refine ⟨6273154775396103888906829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8364206367194805185209105 6273154775396103888906829)
    ·
      refine ⟨2352433040773538958340061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6273154775396103888906829 2352433040773538958340061)
      ·
        refine ⟨882162390290077109377523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2352433040773538958340061 882162390290077109377523)
        ·
          refine ⟨1323243585435115664066285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 882162390290077109377523 1323243585435115664066285)
          ·
            refine ⟨496216344538168374024857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1323243585435115664066285 496216344538168374024857)
            ·
              refine ⟨372162258403626280518643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 496216344538168374024857 372162258403626280518643)
              ·
                refine ⟨558243387605439420777965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 372162258403626280518643 558243387605439420777965)
                ·
                  refine ⟨209341270352039782791737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 558243387605439420777965 209341270352039782791737)
                  ·
                    rfl

theorem cell20_458652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 3, 2, 1, 3].length) (baseStart_458652 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_458652 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_458652 prefixEnd_458652 := by exact prefixLift 458652
  have htrace : WordTrace (prefixWord ++ tailWord_458652) baseStart_458652 baseEnd_458652 := by
    simpa [prefixWord, tailWord_458652, baseEnd_458652] using wordTrace_append hprefix tailTrace_458652
  have hstable : (prefixWord ++ tailWord_458652).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_458652).length < 2 ^ (prefixWord ++ tailWord_458652).sum := by decide
  have hdescent : baseEnd_458652 < baseStart_458652 := by decide
  rcases family_descends (prefixWord ++ tailWord_458652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_458753 : List Nat := [1, 2, 4, 1, 2, 1, 3, 1, 5]
def baseStart_458753 : Nat := 118140960795 + 458753 * 2 ^ 59
def prefixEnd_458753 : Nat := 4983230072969 + 3 ^ 40 * 458753 * 2
def baseEnd_458753 : Nat := 209387369504132320424657

theorem tailTrace_458753 : CollatzResearch.WordTrace tailWord_458753 prefixEnd_458753 209387369504132320424657 := by
  unfold tailWord_458753
  simp only [CollatzResearch.WordTrace]
  refine ⟨16732096507023704619844913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11154731004682469746563275 16732096507023704619844913)
  ·
    refine ⟨12549072380267778464883685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16732096507023704619844913 12549072380267778464883685)
    ·
      refine ⟨2352951071300208462165691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12549072380267778464883685 2352951071300208462165691)
      ·
        refine ⟨3529426606950312693248537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2352951071300208462165691 3529426606950312693248537)
        ·
          refine ⟨2647069955212734519936403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3529426606950312693248537 2647069955212734519936403)
          ·
            refine ⟨3970604932819101779904605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2647069955212734519936403 3970604932819101779904605)
            ·
              refine ⟨1488976849807163167464227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3970604932819101779904605 1488976849807163167464227)
              ·
                refine ⟨2233465274710744751196341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1488976849807163167464227 2233465274710744751196341)
                ·
                  refine ⟨209387369504132320424657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2233465274710744751196341 209387369504132320424657)
                  ·
                    rfl

theorem cell20_458753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 3, 1, 5].length) (baseStart_458753 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_458753 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_458753 prefixEnd_458753 := by exact prefixLift 458753
  have htrace : WordTrace (prefixWord ++ tailWord_458753) baseStart_458753 baseEnd_458753 := by
    simpa [prefixWord, tailWord_458753, baseEnd_458753] using wordTrace_append hprefix tailTrace_458753
  have hstable : (prefixWord ++ tailWord_458753).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_458753).length < 2 ^ (prefixWord ++ tailWord_458753).sum := by decide
  have hdescent : baseEnd_458753 < baseStart_458753 := by decide
  rcases family_descends (prefixWord ++ tailWord_458753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_458805 : List Nat := [1, 3, 3, 1, 1, 1, 10]
def baseStart_458805 : Nat := 118140960795 + 458805 * 2 ^ 59
def prefixEnd_458805 : Nat := 4983230072969 + 3 ^ 40 * 458805 * 2
def baseEnd_458805 : Nat := 23267900413450138965679

theorem tailTrace_458805 : CollatzResearch.WordTrace tailWord_458805 prefixEnd_458805 23267900413450138965679 := by
  unfold tailWord_458805
  simp only [CollatzResearch.WordTrace]
  refine ⟨16733993102835317500737869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11155995401890211667158579 16733993102835317500737869)
  ·
    refine ⟨6275247413563244062776701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16733993102835317500737869 6275247413563244062776701)
    ·
      refine ⟨2353217780086216523541263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6275247413563244062776701 2353217780086216523541263)
      ·
        refine ⟨3529826670129324785311895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2353217780086216523541263 3529826670129324785311895)
        ·
          refine ⟨5294740005193987177967843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3529826670129324785311895 5294740005193987177967843)
          ·
            refine ⟨7942110007790980766951765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5294740005193987177967843 7942110007790980766951765)
            ·
              refine ⟨23267900413450138965679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 7942110007790980766951765 23267900413450138965679)
              ·
                rfl

theorem cell20_458805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 10].length) (baseStart_458805 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_458805 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_458805 prefixEnd_458805 := by exact prefixLift 458805
  have htrace : WordTrace (prefixWord ++ tailWord_458805) baseStart_458805 baseEnd_458805 := by
    simpa [prefixWord, tailWord_458805, baseEnd_458805] using wordTrace_append hprefix tailTrace_458805
  have hstable : (prefixWord ++ tailWord_458805).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_458805).length < 2 ^ (prefixWord ++ tailWord_458805).sum := by decide
  have hdescent : baseEnd_458805 < baseStart_458805 := by decide
  rcases family_descends (prefixWord ++ tailWord_458805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_458815 : List Nat := [1, 1, 2, 2, 3, 1, 2, 6, 2]
def baseStart_458815 : Nat := 118140960795 + 458815 * 2 ^ 59
def prefixEnd_458815 : Nat := 4983230072969 + 3 ^ 40 * 458815 * 2
def baseEnd_458815 : Nat := 209415667993535660357737

theorem tailTrace_458815 : CollatzResearch.WordTrace tailWord_458815 prefixEnd_458815 209415667993535660357737 := by
  unfold tailWord_458815
  simp only [CollatzResearch.WordTrace]
  refine ⟨16734357832799089208601899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11156238555199392805734599 16734357832799089208601899)
  ·
    refine ⟨25101536749198633812902849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16734357832799089208601899 25101536749198633812902849)
    ·
      refine ⟨18826152561898975359677137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25101536749198633812902849 18826152561898975359677137)
      ·
        refine ⟨14119614421424231519757853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18826152561898975359677137 14119614421424231519757853)
        ·
          refine ⟨5294855408034086819909195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14119614421424231519757853 5294855408034086819909195)
          ·
            refine ⟨7942283112051130229863793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5294855408034086819909195 7942283112051130229863793)
            ·
              refine ⟨5956712334038347672397845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7942283112051130229863793 5956712334038347672397845)
              ·
                refine ⟨279220890658047547143649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 5956712334038347672397845 279220890658047547143649)
                ·
                  refine ⟨209415667993535660357737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 279220890658047547143649 209415667993535660357737)
                  ·
                    rfl

theorem cell20_458815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 2, 6, 2].length) (baseStart_458815 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_458815 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_458815 prefixEnd_458815 := by exact prefixLift 458815
  have htrace : WordTrace (prefixWord ++ tailWord_458815) baseStart_458815 baseEnd_458815 := by
    simpa [prefixWord, tailWord_458815, baseEnd_458815] using wordTrace_append hprefix tailTrace_458815
  have hstable : (prefixWord ++ tailWord_458815).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_458815).length < 2 ^ (prefixWord ++ tailWord_458815).sum := by decide
  have hdescent : baseEnd_458815 < baseStart_458815 := by decide
  rcases family_descends (prefixWord ++ tailWord_458815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_458836 : List Nat := [2, 4, 1, 1, 1, 1, 1, 3, 6]
def baseStart_458836 : Nat := 118140960795 + 458836 * 2 ^ 59
def prefixEnd_458836 : Nat := 4983230072969 + 3 ^ 40 * 458836 * 2
def baseEnd_458836 : Nat := 209425252965752920657651

theorem tailTrace_458836 : CollatzResearch.WordTrace tailWord_458836 prefixEnd_458836 209425252965752920657651 := by
  unfold tailWord_458836
  simp only [CollatzResearch.WordTrace]
  refine ⟨8367561882861504897558181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11156749177148673196744241 8367561882861504897558181)
  ·
    refine ⟨1568917853036532168292159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8367561882861504897558181 1568917853036532168292159)
    ·
      refine ⟨2353376779554798252438239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1568917853036532168292159 2353376779554798252438239)
      ·
        refine ⟨3530065169332197378657359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2353376779554798252438239 3530065169332197378657359)
        ·
          refine ⟨5295097753998296067986039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3530065169332197378657359 5295097753998296067986039)
          ·
            refine ⟨7942646630997444101979059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5295097753998296067986039 7942646630997444101979059)
            ·
              refine ⟨11913969946496166152968589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7942646630997444101979059 11913969946496166152968589)
              ·
                refine ⟨4467738729936062307363221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11913969946496166152968589 4467738729936062307363221)
                ·
                  refine ⟨209425252965752920657651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4467738729936062307363221 209425252965752920657651)
                  ·
                    rfl

theorem cell20_458836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 3, 6].length) (baseStart_458836 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_458836 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_458836 prefixEnd_458836 := by exact prefixLift 458836
  have htrace : WordTrace (prefixWord ++ tailWord_458836) baseStart_458836 baseEnd_458836 := by
    simpa [prefixWord, tailWord_458836, baseEnd_458836] using wordTrace_append hprefix tailTrace_458836
  have hstable : (prefixWord ++ tailWord_458836).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_458836).length < 2 ^ (prefixWord ++ tailWord_458836).sum := by decide
  have hdescent : baseEnd_458836 < baseStart_458836 := by decide
  rcases family_descends (prefixWord ++ tailWord_458836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_458908 : List Nat := [2, 2, 3, 2, 1, 1, 4, 3, 2]
def baseStart_458908 : Nat := 118140960795 + 458908 * 2 ^ 59
def prefixEnd_458908 : Nat := 4983230072969 + 3 ^ 40 * 458908 * 2
def baseEnd_458908 : Nat := 209458115727640670257357

theorem tailTrace_458908 : CollatzResearch.WordTrace tailWord_458908 prefixEnd_458908 209458115727640670257357 := by
  unfold tailWord_458908
  simp only [CollatzResearch.WordTrace]
  refine ⟨8368874910731083045868689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11158499880974777394491585 8368874910731083045868689)
  ·
    refine ⟨6276656183048312284401517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8368874910731083045868689 6276656183048312284401517)
    ·
      refine ⟨2353746068643117106650569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6276656183048312284401517 2353746068643117106650569)
      ·
        refine ⟨1765309551482337829987927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2353746068643117106650569 1765309551482337829987927)
        ·
          refine ⟨2647964327223506744981891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1765309551482337829987927 2647964327223506744981891)
          ·
            refine ⟨3971946490835260117472837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2647964327223506744981891 3971946490835260117472837)
            ·
              refine ⟨744739967031611272026157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3971946490835260117472837 744739967031611272026157)
              ·
                refine ⟨279277487636854227009809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 744739967031611272026157 279277487636854227009809)
                ·
                  refine ⟨209458115727640670257357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 279277487636854227009809 209458115727640670257357)
                  ·
                    rfl

theorem cell20_458908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 4, 3, 2].length) (baseStart_458908 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_458908 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_458908 prefixEnd_458908 := by exact prefixLift 458908
  have htrace : WordTrace (prefixWord ++ tailWord_458908) baseStart_458908 baseEnd_458908 := by
    simpa [prefixWord, tailWord_458908, baseEnd_458908] using wordTrace_append hprefix tailTrace_458908
  have hstable : (prefixWord ++ tailWord_458908).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_458908).length < 2 ^ (prefixWord ++ tailWord_458908).sum := by decide
  have hdescent : baseEnd_458908 < baseStart_458908 := by decide
  rcases family_descends (prefixWord ++ tailWord_458908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_458971 : List Nat := [1, 1, 1, 1, 1, 1, 1, 5, 8]
def baseStart_458971 : Nat := 118140960795 + 458971 * 2 ^ 59
def prefixEnd_458971 : Nat := 4983230072969 + 3 ^ 40 * 458971 * 2
def baseEnd_458971 : Nat := 209486870644292451157099

theorem tailTrace_458971 : CollatzResearch.WordTrace tailWord_458971 prefixEnd_458971 209486870644292451157099 := by
  unfold tailWord_458971
  simp only [CollatzResearch.WordTrace]
  refine ⟨16740047620233927851280767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11160031746822618567520511 16740047620233927851280767)
  ·
    refine ⟨25110071430350891776921151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16740047620233927851280767 25110071430350891776921151)
    ·
      refine ⟨37665107145526337665381727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25110071430350891776921151 37665107145526337665381727)
      ·
        refine ⟨56497660718289506498072591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37665107145526337665381727 56497660718289506498072591)
        ·
          refine ⟨84746491077434259747108887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56497660718289506498072591 84746491077434259747108887)
          ·
            refine ⟨127119736616151389620663331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84746491077434259747108887 127119736616151389620663331)
            ·
              refine ⟨190679604924227084430994997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 127119736616151389620663331 190679604924227084430994997)
              ·
                refine ⟨17876212961646289165405781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 190679604924227084430994997 17876212961646289165405781)
                ·
                  refine ⟨209486870644292451157099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 17876212961646289165405781 209486870644292451157099)
                  ·
                    rfl

theorem cell20_458971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 5, 8].length) (baseStart_458971 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_458971 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_458971 prefixEnd_458971 := by exact prefixLift 458971
  have htrace : WordTrace (prefixWord ++ tailWord_458971) baseStart_458971 baseEnd_458971 := by
    simpa [prefixWord, tailWord_458971, baseEnd_458971] using wordTrace_append hprefix tailTrace_458971
  have hstable : (prefixWord ++ tailWord_458971).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_458971).length < 2 ^ (prefixWord ++ tailWord_458971).sum := by decide
  have hdescent : baseEnd_458971 < baseStart_458971 := by decide
  rcases family_descends (prefixWord ++ tailWord_458971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_458981 : List Nat := [1, 3, 1, 4, 2, 1, 2, 1, 5]
def baseStart_458981 : Nat := 118140960795 + 458981 * 2 ^ 59
def prefixEnd_458981 : Nat := 4983230072969 + 3 ^ 40 * 458981 * 2
def baseEnd_458981 : Nat := 209491434916776860823725

theorem tailTrace_458981 : CollatzResearch.WordTrace tailWord_458981 prefixEnd_458981 209491434916776860823725 := by
  unfold tailWord_458981
  simp only [CollatzResearch.WordTrace]
  refine ⟨16740412350197699559144797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11160274900131799706096531 16740412350197699559144797)
  ·
    refine ⟨6277654631324137334679299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16740412350197699559144797 6277654631324137334679299)
    ·
      refine ⟨9416481946986206002018949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6277654631324137334679299 9416481946986206002018949)
      ·
        refine ⟨1765590365059913625378553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9416481946986206002018949 1765590365059913625378553)
        ·
          refine ⟨1324192773794935219033915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1765590365059913625378553 1324192773794935219033915)
          ·
            refine ⟨1986289160692402828550873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1324192773794935219033915 1986289160692402828550873)
            ·
              refine ⟨1489716870519302121413155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1986289160692402828550873 1489716870519302121413155)
              ·
                refine ⟨2234575305778953182119733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1489716870519302121413155 2234575305778953182119733)
                ·
                  refine ⟨209491434916776860823725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2234575305778953182119733 209491434916776860823725)
                  ·
                    rfl

theorem cell20_458981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 2, 1, 5].length) (baseStart_458981 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_458981 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_458981 prefixEnd_458981 := by exact prefixLift 458981
  have htrace : WordTrace (prefixWord ++ tailWord_458981) baseStart_458981 baseEnd_458981 := by
    simpa [prefixWord, tailWord_458981, baseEnd_458981] using wordTrace_append hprefix tailTrace_458981
  have hstable : (prefixWord ++ tailWord_458981).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_458981).length < 2 ^ (prefixWord ++ tailWord_458981).sum := by decide
  have hdescent : baseEnd_458981 < baseStart_458981 := by decide
  rcases family_descends (prefixWord ++ tailWord_458981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_458995 : List Nat := [1, 1, 1, 2, 2, 4, 4, 5]
def baseStart_458995 : Nat := 118140960795 + 458995 * 2 ^ 59
def prefixEnd_458995 : Nat := 4983230072969 + 3 ^ 40 * 458995 * 2
def baseEnd_458995 : Nat := 69832608299418344785667

theorem tailTrace_458995 : CollatzResearch.WordTrace tailWord_458995 prefixEnd_458995 69832608299418344785667 := by
  unfold tailWord_458995
  simp only [CollatzResearch.WordTrace]
  refine ⟨16740922972146979950154439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11160615314764653300102959 16740922972146979950154439)
  ·
    refine ⟨25111384458220469925231659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16740922972146979950154439 25111384458220469925231659)
    ·
      refine ⟨37667076687330704887847489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25111384458220469925231659 37667076687330704887847489)
      ·
        refine ⟨28250307515498028665885617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37667076687330704887847489 28250307515498028665885617)
        ·
          refine ⟨21187730636623521499414213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28250307515498028665885617 21187730636623521499414213)
          ·
            refine ⟨3972699494366910281140165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21187730636623521499414213 3972699494366910281140165)
            ·
              refine ⟨744881155193795677713781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3972699494366910281140165 744881155193795677713781)
              ·
                refine ⟨69832608299418344785667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 744881155193795677713781 69832608299418344785667)
                ·
                  rfl

theorem cell20_458995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 4, 5].length) (baseStart_458995 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_458995 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_458995 prefixEnd_458995 := by exact prefixLift 458995
  have htrace : WordTrace (prefixWord ++ tailWord_458995) baseStart_458995 baseEnd_458995 := by
    simpa [prefixWord, tailWord_458995, baseEnd_458995] using wordTrace_append hprefix tailTrace_458995
  have hstable : (prefixWord ++ tailWord_458995).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_458995).length < 2 ^ (prefixWord ++ tailWord_458995).sum := by decide
  have hdescent : baseEnd_458995 < baseStart_458995 := by decide
  rcases family_descends (prefixWord ++ tailWord_458995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_459039 : List Nat := [1, 1, 2, 4, 3, 3, 2, 2, 2]
def baseStart_459039 : Nat := 118140960795 + 459039 * 2 ^ 59
def prefixEnd_459039 : Nat := 4983230072969 + 3 ^ 40 * 459039 * 2
def baseEnd_459039 : Nat := 209517907697186436890155

theorem tailTrace_459039 : CollatzResearch.WordTrace tailWord_459039 prefixEnd_459039 209517907697186436890155 := by
  unfold tailWord_459039
  simp only [CollatzResearch.WordTrace]
  refine ⟨16742527783987575464756171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11161685189325050309837447 16742527783987575464756171)
  ·
    refine ⟨25113791675981363197134257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16742527783987575464756171 25113791675981363197134257)
    ·
      refine ⟨18835343756986022397850693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25113791675981363197134257 18835343756986022397850693)
      ·
        refine ⟨3531626954434879199597005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18835343756986022397850693 3531626954434879199597005)
        ·
          refine ⟨1324360107913079699848877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3531626954434879199597005 1324360107913079699848877)
          ·
            refine ⟨496635040467404887443329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1324360107913079699848877 496635040467404887443329)
            ·
              refine ⟨372476280350553665582497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 496635040467404887443329 372476280350553665582497)
              ·
                refine ⟨279357210262915249186873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 372476280350553665582497 279357210262915249186873)
                ·
                  refine ⟨209517907697186436890155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 279357210262915249186873 209517907697186436890155)
                  ·
                    rfl

theorem cell20_459039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 3, 2, 2, 2].length) (baseStart_459039 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_459039 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_459039 prefixEnd_459039 := by exact prefixLift 459039
  have htrace : WordTrace (prefixWord ++ tailWord_459039) baseStart_459039 baseEnd_459039 := by
    simpa [prefixWord, tailWord_459039, baseEnd_459039] using wordTrace_append hprefix tailTrace_459039
  have hstable : (prefixWord ++ tailWord_459039).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_459039).length < 2 ^ (prefixWord ++ tailWord_459039).sum := by decide
  have hdescent : baseEnd_459039 < baseStart_459039 := by decide
  rcases family_descends (prefixWord ++ tailWord_459039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_459043 : List Nat := [1, 1, 1, 4, 2, 2, 3, 4, 2]
def baseStart_459043 : Nat := 118140960795 + 459043 * 2 ^ 59
def prefixEnd_459043 : Nat := 4983230072969 + 3 ^ 40 * 459043 * 2
def baseEnd_459043 : Nat := 209519733406180200756805

theorem tailTrace_459043 : CollatzResearch.WordTrace tailWord_459043 prefixEnd_459043 209519733406180200756805 := by
  unfold tailWord_459043
  simp only [CollatzResearch.WordTrace]
  refine ⟨16742673675973084147901783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11161782450648722765267855 16742673675973084147901783)
  ·
    refine ⟨25114010513959626221852675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16742673675973084147901783 25114010513959626221852675)
    ·
      refine ⟨37671015770939439332779013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25114010513959626221852675 37671015770939439332779013)
      ·
        refine ⟨7063315457051144874896065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 37671015770939439332779013 7063315457051144874896065)
        ·
          refine ⟨5297486592788358656172049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7063315457051144874896065 5297486592788358656172049)
          ·
            refine ⟨3973114944591268992129037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5297486592788358656172049 3973114944591268992129037)
            ·
              refine ⟨1489918104221725872048389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3973114944591268992129037 1489918104221725872048389)
              ·
                refine ⟨279359644541573601009073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1489918104221725872048389 279359644541573601009073)
                ·
                  refine ⟨209519733406180200756805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 279359644541573601009073 209519733406180200756805)
                  ·
                    rfl

theorem cell20_459043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 3, 4, 2].length) (baseStart_459043 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_459043 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_459043 prefixEnd_459043 := by exact prefixLift 459043
  have htrace : WordTrace (prefixWord ++ tailWord_459043) baseStart_459043 baseEnd_459043 := by
    simpa [prefixWord, tailWord_459043, baseEnd_459043] using wordTrace_append hprefix tailTrace_459043
  have hstable : (prefixWord ++ tailWord_459043).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_459043).length < 2 ^ (prefixWord ++ tailWord_459043).sum := by decide
  have hdescent : baseEnd_459043 < baseStart_459043 := by decide
  rcases family_descends (prefixWord ++ tailWord_459043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_459147 : List Nat := [1, 1, 1, 1, 4, 6, 6]
def baseStart_459147 : Nat := 118140960795 + 459147 * 2 ^ 59
def prefixEnd_459147 : Nat := 4983230072969 + 3 ^ 40 * 459147 * 2
def baseEnd_459147 : Nat := 23285244648890895698857

theorem tailTrace_459147 : CollatzResearch.WordTrace tailWord_459147 prefixEnd_459147 23285244648890895698857 := by
  unfold tailWord_459147
  simp only [CollatzResearch.WordTrace]
  refine ⟨16746466867596309909687695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11164311245064206606458463 16746466867596309909687695)
  ·
    refine ⟨25119700301394464864531543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16746466867596309909687695 25119700301394464864531543)
    ·
      refine ⟨37679550452091697296797315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25119700301394464864531543 37679550452091697296797315)
      ·
        refine ⟨56519325678137545945195973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37679550452091697296797315 56519325678137545945195973)
        ·
          refine ⟨10597373564650789864724245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 56519325678137545945195973 10597373564650789864724245)
          ·
            refine ⟨496751885843005774908949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 10597373564650789864724245 496751885843005774908949)
            ·
              refine ⟨23285244648890895698857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 496751885843005774908949 23285244648890895698857)
              ·
                rfl

theorem cell20_459147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 6, 6].length) (baseStart_459147 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_459147 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_459147 prefixEnd_459147 := by exact prefixLift 459147
  have htrace : WordTrace (prefixWord ++ tailWord_459147) baseStart_459147 baseEnd_459147 := by
    simpa [prefixWord, tailWord_459147, baseEnd_459147] using wordTrace_append hprefix tailTrace_459147
  have hstable : (prefixWord ++ tailWord_459147).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_459147).length < 2 ^ (prefixWord ++ tailWord_459147).sum := by decide
  have hdescent : baseEnd_459147 < baseStart_459147 := by decide
  rcases family_descends (prefixWord ++ tailWord_459147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_459171 : List Nat := [1, 1, 1, 4, 1, 5, 1, 3, 3]
def baseStart_459171 : Nat := 118140960795 + 459171 * 2 ^ 59
def prefixEnd_459171 : Nat := 4983230072969 + 3 ^ 40 * 459171 * 2
def baseEnd_459171 : Nat := 209578156093980644489615

theorem tailTrace_459171 : CollatzResearch.WordTrace tailWord_459171 prefixEnd_459171 209578156093980644489615 := by
  unfold tailWord_459171
  simp only [CollatzResearch.WordTrace]
  refine ⟨16747342219509362008561367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11164894813006241339040911 16747342219509362008561367)
  ·
    refine ⟨25121013329264043012842051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16747342219509362008561367 25121013329264043012842051)
    ·
      refine ⟨37681519993896064519263077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25121013329264043012842051 37681519993896064519263077)
      ·
        refine ⟨7065284998855512097361827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 37681519993896064519263077 7065284998855512097361827)
        ·
          refine ⟨10597927498283268146042741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7065284998855512097361827 10597927498283268146042741)
          ·
            refine ⟨993555702964056388691507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 10597927498283268146042741 993555702964056388691507)
            ·
              refine ⟨1490333554446084583037261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 993555702964056388691507 1490333554446084583037261)
              ·
                refine ⟨558875082917281718638973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1490333554446084583037261 558875082917281718638973)
                ·
                  refine ⟨209578156093980644489615, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 558875082917281718638973 209578156093980644489615)
                  ·
                    rfl

theorem cell20_459171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 5, 1, 3, 3].length) (baseStart_459171 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_459171 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_459171 prefixEnd_459171 := by exact prefixLift 459171
  have htrace : WordTrace (prefixWord ++ tailWord_459171) baseStart_459171 baseEnd_459171 := by
    simpa [prefixWord, tailWord_459171, baseEnd_459171] using wordTrace_append hprefix tailTrace_459171
  have hstable : (prefixWord ++ tailWord_459171).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_459171).length < 2 ^ (prefixWord ++ tailWord_459171).sum := by decide
  have hdescent : baseEnd_459171 < baseStart_459171 := by decide
  rcases family_descends (prefixWord ++ tailWord_459171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_459185 : List Nat := [1, 2, 2, 4, 1, 2, 2, 6]
def baseStart_459185 : Nat := 118140960795 + 459185 * 2 ^ 59
def prefixEnd_459185 : Nat := 4983230072969 + 3 ^ 40 * 459185 * 2
def baseEnd_459185 : Nat := 69861515358486272674297

theorem tailTrace_459185 : CollatzResearch.WordTrace tailWord_459185 prefixEnd_459185 69861515358486272674297 := by
  unfold tailWord_459185
  simp only [CollatzResearch.WordTrace]
  refine ⟨16747852841458642399571009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11165235227639094933047339 16747852841458642399571009)
  ·
    refine ⟨12560889631093981799678257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16747852841458642399571009 12560889631093981799678257)
    ·
      refine ⟨9420667223320486349758693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12560889631093981799678257 9420667223320486349758693)
      ·
        refine ⟨1766375104372591190579755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9420667223320486349758693 1766375104372591190579755)
        ·
          refine ⟨2649562656558886785869633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1766375104372591190579755 2649562656558886785869633)
          ·
            refine ⟨1987171992419165089402225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2649562656558886785869633 1987171992419165089402225)
            ·
              refine ⟨1490378994314373817051669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1987171992419165089402225 1490378994314373817051669)
              ·
                refine ⟨69861515358486272674297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1490378994314373817051669 69861515358486272674297)
                ·
                  rfl

theorem cell20_459185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 2, 6].length) (baseStart_459185 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_459185 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_459185 prefixEnd_459185 := by exact prefixLift 459185
  have htrace : WordTrace (prefixWord ++ tailWord_459185) baseStart_459185 baseEnd_459185 := by
    simpa [prefixWord, tailWord_459185, baseEnd_459185] using wordTrace_append hprefix tailTrace_459185
  have hstable : (prefixWord ++ tailWord_459185).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_459185).length < 2 ^ (prefixWord ++ tailWord_459185).sum := by decide
  have hdescent : baseEnd_459185 < baseStart_459185 := by decide
  rcases family_descends (prefixWord ++ tailWord_459185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_459212 : List Nat := [2, 2, 1, 4, 3, 1, 1, 4, 2]
def baseStart_459212 : Nat := 118140960795 + 459212 * 2 ^ 59
def prefixEnd_459212 : Nat := 4983230072969 + 3 ^ 40 * 459212 * 2
def baseEnd_459212 : Nat := 209596869611166724122781

theorem tailTrace_459212 : CollatzResearch.WordTrace tailWord_459212 prefixEnd_459212 209596869611166724122781 := by
  unfold tailWord_459212
  simp only [CollatzResearch.WordTrace]
  refine ⟨8374418806180413005401945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11165891741573884007202593 8374418806180413005401945)
  ·
    refine ⟨6280814104635309754051459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8374418806180413005401945 6280814104635309754051459)
    ·
      refine ⟨9421221156952964631077189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6280814104635309754051459 9421221156952964631077189)
      ·
        refine ⟨1766478966928680868326973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9421221156952964631077189 1766478966928680868326973)
        ·
          refine ⟨662429612598255325622615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1766478966928680868326973 662429612598255325622615)
          ·
            refine ⟨993644418897382988433923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 662429612598255325622615 993644418897382988433923)
            ·
              refine ⟨1490466628346074482650885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 993644418897382988433923 1490466628346074482650885)
              ·
                refine ⟨279462492814888965497041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1490466628346074482650885 279462492814888965497041)
                ·
                  refine ⟨209596869611166724122781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 279462492814888965497041 209596869611166724122781)
                  ·
                    rfl

theorem cell20_459212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 1, 1, 4, 2].length) (baseStart_459212 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_459212 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_459212 prefixEnd_459212 := by exact prefixLift 459212
  have htrace : WordTrace (prefixWord ++ tailWord_459212) baseStart_459212 baseEnd_459212 := by
    simpa [prefixWord, tailWord_459212, baseEnd_459212] using wordTrace_append hprefix tailTrace_459212
  have hstable : (prefixWord ++ tailWord_459212).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_459212).length < 2 ^ (prefixWord ++ tailWord_459212).sum := by decide
  have hdescent : baseEnd_459212 < baseStart_459212 := by decide
  rcases family_descends (prefixWord ++ tailWord_459212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_459240 : List Nat := [2, 1, 4, 1, 1, 4, 3, 4]
def baseStart_459240 : Nat := 118140960795 + 459240 * 2 ^ 59
def prefixEnd_459240 : Nat := 4983230072969 + 3 ^ 40 * 459240 * 2
def baseEnd_459240 : Nat := 69869883191374357063111

theorem tailTrace_459240 : CollatzResearch.WordTrace tailWord_459240 prefixEnd_459240 69869883191374357063111 := by
  unfold tailWord_459240
  simp only [CollatzResearch.WordTrace]
  refine ⟨8374929428129693396411587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11166572570839591195215449 8374929428129693396411587)
  ·
    refine ⟨12562394142194540094617381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8374929428129693396411587 12562394142194540094617381)
    ·
      refine ⟨2355448901661476267740759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12562394142194540094617381 2355448901661476267740759)
      ·
        refine ⟨3533173352492214401611139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2355448901661476267740759 3533173352492214401611139)
        ·
          refine ⟨5299760028738321602416709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3533173352492214401611139 5299760028738321602416709)
          ·
            refine ⟨993705005388435300453133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5299760028738321602416709 993705005388435300453133)
            ·
              refine ⟨372639377020663237669925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 993705005388435300453133 372639377020663237669925)
              ·
                refine ⟨69869883191374357063111, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 372639377020663237669925 69869883191374357063111)
                ·
                  rfl

theorem cell20_459240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 4, 3, 4].length) (baseStart_459240 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_459240 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_459240 prefixEnd_459240 := by exact prefixLift 459240
  have htrace : WordTrace (prefixWord ++ tailWord_459240) baseStart_459240 baseEnd_459240 := by
    simpa [prefixWord, tailWord_459240, baseEnd_459240] using wordTrace_append hprefix tailTrace_459240
  have hstable : (prefixWord ++ tailWord_459240).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_459240).length < 2 ^ (prefixWord ++ tailWord_459240).sum := by decide
  have hdescent : baseEnd_459240 < baseStart_459240 := by decide
  rcases family_descends (prefixWord ++ tailWord_459240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_459254 : List Nat := [5, 1, 1, 1, 2, 1, 1, 2, 6]
def baseStart_459254 : Nat := 118140960795 + 459254 * 2 ^ 59
def prefixEnd_459254 : Nat := 4983230072969 + 3 ^ 40 * 459254 * 2
def baseEnd_459254 : Nat := 209616039555601244722609

theorem tailTrace_459254 : CollatzResearch.WordTrace tailWord_459254 prefixEnd_459254 209616039555601244722609 := by
  unfold tailWord_459254
  simp only [CollatzResearch.WordTrace]
  refine ⟨1046898092388041698989551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 11166912985472444789221877 1046898092388041698989551)
  ·
    refine ⟨1570347138582062548484327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1046898092388041698989551 1570347138582062548484327)
    ·
      refine ⟨2355520707873093822726491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1570347138582062548484327 2355520707873093822726491)
      ·
        refine ⟨3533281061809640734089737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2355520707873093822726491 3533281061809640734089737)
        ·
          refine ⟨2649960796357230550567303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3533281061809640734089737 2649960796357230550567303)
          ·
            refine ⟨3974941194535845825850955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2649960796357230550567303 3974941194535845825850955)
            ·
              refine ⟨5962411791803768738776433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3974941194535845825850955 5962411791803768738776433)
              ·
                refine ⟨4471808843852826554082325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5962411791803768738776433 4471808843852826554082325)
                ·
                  refine ⟨209616039555601244722609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4471808843852826554082325 209616039555601244722609)
                  ·
                    rfl

theorem cell20_459254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 1, 2, 6].length) (baseStart_459254 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_459254 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_459254 prefixEnd_459254 := by exact prefixLift 459254
  have htrace : WordTrace (prefixWord ++ tailWord_459254) baseStart_459254 baseEnd_459254 := by
    simpa [prefixWord, tailWord_459254, baseEnd_459254] using wordTrace_append hprefix tailTrace_459254
  have hstable : (prefixWord ++ tailWord_459254).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_459254).length < 2 ^ (prefixWord ++ tailWord_459254).sum := by decide
  have hdescent : baseEnd_459254 < baseStart_459254 := by decide
  rcases family_descends (prefixWord ++ tailWord_459254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_459271 : List Nat := [1, 1, 4, 3, 3, 1, 2, 1, 4]
def baseStart_459271 : Nat := 118140960795 + 459271 * 2 ^ 59
def prefixEnd_459271 : Nat := 4983230072969 + 3 ^ 40 * 459271 * 2
def baseEnd_459271 : Nat := 209623798818824741155873

theorem tailTrace_459271 : CollatzResearch.WordTrace tailWord_459271 prefixEnd_459271 209623798818824741155873 := by
  unfold tailWord_459271
  simp only [CollatzResearch.WordTrace]
  refine ⟨16750989519147079087201667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11167326346098052724801111 16750989519147079087201667)
  ·
    refine ⟨25126484278720618630802501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16750989519147079087201667 25126484278720618630802501)
    ·
      refine ⟨4711215802260115993275469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 25126484278720618630802501 4711215802260115993275469)
      ·
        refine ⟨1766705925847543497478301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4711215802260115993275469 1766705925847543497478301)
        ·
          refine ⟨662514722192828811554363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1766705925847543497478301 662514722192828811554363)
          ·
            refine ⟨993772083289243217331545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 662514722192828811554363 993772083289243217331545)
            ·
              refine ⟨745329062466932412998659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 993772083289243217331545 745329062466932412998659)
              ·
                refine ⟨1117993593700398619497989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 745329062466932412998659 1117993593700398619497989)
                ·
                  refine ⟨209623798818824741155873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1117993593700398619497989 209623798818824741155873)
                  ·
                    rfl

theorem cell20_459271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 1, 2, 1, 4].length) (baseStart_459271 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_459271 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_459271 prefixEnd_459271 := by exact prefixLift 459271
  have htrace : WordTrace (prefixWord ++ tailWord_459271) baseStart_459271 baseEnd_459271 := by
    simpa [prefixWord, tailWord_459271, baseEnd_459271] using wordTrace_append hprefix tailTrace_459271
  have hstable : (prefixWord ++ tailWord_459271).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_459271).length < 2 ^ (prefixWord ++ tailWord_459271).sum := by decide
  have hdescent : baseEnd_459271 < baseStart_459271 := by decide
  rcases family_descends (prefixWord ++ tailWord_459271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_459292 : List Nat := [2, 2, 3, 1, 2, 2, 2, 2, 4]
def baseStart_459292 : Nat := 118140960795 + 459292 * 2 ^ 59
def prefixEnd_459292 : Nat := 4983230072969 + 3 ^ 40 * 459292 * 2
def baseEnd_459292 : Nat := 209633383791042001455787

theorem tailTrace_459292 : CollatzResearch.WordTrace tailWord_459292 prefixEnd_459292 209633383791042001455787 := by
  unfold tailWord_459292
  simp only [CollatzResearch.WordTrace]
  refine ⟨8375877726035499836858065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11167836968047333115810753 8375877726035499836858065)
  ·
    refine ⟨6281908294526624877643549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8375877726035499836858065 6281908294526624877643549)
    ·
      refine ⟨2355715610447484329116331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6281908294526624877643549 2355715610447484329116331)
      ·
        refine ⟨3533573415671226493674497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2355715610447484329116331 3533573415671226493674497)
        ·
          refine ⟨2650180061753419870255873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3533573415671226493674497 2650180061753419870255873)
          ·
            refine ⟨1987635046315064902691905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2650180061753419870255873 1987635046315064902691905)
            ·
              refine ⟨1490726284736298677018929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1987635046315064902691905 1490726284736298677018929)
              ·
                refine ⟨1118044713552224007764197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1490726284736298677018929 1118044713552224007764197)
                ·
                  refine ⟨209633383791042001455787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1118044713552224007764197 209633383791042001455787)
                  ·
                    rfl

theorem cell20_459292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 2, 2, 4].length) (baseStart_459292 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_459292 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_459292 prefixEnd_459292 := by exact prefixLift 459292
  have htrace : WordTrace (prefixWord ++ tailWord_459292) baseStart_459292 baseEnd_459292 := by
    simpa [prefixWord, tailWord_459292, baseEnd_459292] using wordTrace_append hprefix tailTrace_459292
  have hstable : (prefixWord ++ tailWord_459292).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_459292).length < 2 ^ (prefixWord ++ tailWord_459292).sum := by decide
  have hdescent : baseEnd_459292 < baseStart_459292 := by decide
  rcases family_descends (prefixWord ++ tailWord_459292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_459299 : List Nat := [1, 1, 1, 4, 4, 2, 1, 6]
def baseStart_459299 : Nat := 118140960795 + 459299 * 2 ^ 59
def prefixEnd_459299 : Nat := 4983230072969 + 3 ^ 40 * 459299 * 2
def baseEnd_459299 : Nat := 69878859593927029407475

theorem tailTrace_459299 : CollatzResearch.WordTrace tailWord_459299 prefixEnd_459299 69878859593927029407475 := by
  unfold tailWord_459299
  simp only [CollatzResearch.WordTrace]
  refine ⟨16752010763045639869220951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11168007175363759912813967 16752010763045639869220951)
  ·
    refine ⟨25128016144568459803831427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16752010763045639869220951 25128016144568459803831427)
    ·
      refine ⟨37692024216852689705747141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25128016144568459803831427 37692024216852689705747141)
      ·
        refine ⟨7067254540659879319827589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 37692024216852689705747141 7067254540659879319827589)
        ·
          refine ⟨1325110226373727372467673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7067254540659879319827589 1325110226373727372467673)
          ·
            refine ⟨993832669780295529350755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1325110226373727372467673 993832669780295529350755)
            ·
              refine ⟨1490749004670443294026133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 993832669780295529350755 1490749004670443294026133)
              ·
                refine ⟨69878859593927029407475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1490749004670443294026133 69878859593927029407475)
                ·
                  rfl

theorem cell20_459299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 2, 1, 6].length) (baseStart_459299 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_459299 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_459299 prefixEnd_459299 := by exact prefixLift 459299
  have htrace : WordTrace (prefixWord ++ tailWord_459299) baseStart_459299 baseEnd_459299 := by
    simpa [prefixWord, tailWord_459299, baseEnd_459299] using wordTrace_append hprefix tailTrace_459299
  have hstable : (prefixWord ++ tailWord_459299).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_459299).length < 2 ^ (prefixWord ++ tailWord_459299).sum := by decide
  have hdescent : baseEnd_459299 < baseStart_459299 := by decide
  rcases family_descends (prefixWord ++ tailWord_459299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_459313 : List Nat := [1, 2, 2, 3, 1, 1, 2, 2, 6]
def baseStart_459313 : Nat := 118140960795 + 459313 * 2 ^ 59
def prefixEnd_459313 : Nat := 4983230072969 + 3 ^ 40 * 459313 * 2
def baseEnd_459313 : Nat := 209642968763259261755701

theorem tailTrace_459313 : CollatzResearch.WordTrace tailWord_459313 prefixEnd_459313 209642968763259261755701 := by
  unfold tailWord_459313
  simp only [CollatzResearch.WordTrace]
  refine ⟨16752521384994920260230593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11168347589996613506820395 16752521384994920260230593)
  ·
    refine ⟨12564391038746190195172945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16752521384994920260230593 12564391038746190195172945)
    ·
      refine ⟨9423293279059642646379709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12564391038746190195172945 9423293279059642646379709)
      ·
        refine ⟨3533734979647365992392391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9423293279059642646379709 3533734979647365992392391)
        ·
          refine ⟨5300602469471048988588587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3533734979647365992392391 5300602469471048988588587)
          ·
            refine ⟨7950903704206573482882881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5300602469471048988588587 7950903704206573482882881)
            ·
              refine ⟨5963177778154930112162161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7950903704206573482882881 5963177778154930112162161)
              ·
                refine ⟨4472383333616197584121621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5963177778154930112162161 4472383333616197584121621)
                ·
                  refine ⟨209642968763259261755701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4472383333616197584121621 209642968763259261755701)
                  ·
                    rfl

theorem cell20_459313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 2, 2, 6].length) (baseStart_459313 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_459313 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_459313 prefixEnd_459313 := by exact prefixLift 459313
  have htrace : WordTrace (prefixWord ++ tailWord_459313) baseStart_459313 baseEnd_459313 := by
    simpa [prefixWord, tailWord_459313, baseEnd_459313] using wordTrace_append hprefix tailTrace_459313
  have hstable : (prefixWord ++ tailWord_459313).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_459313).length < 2 ^ (prefixWord ++ tailWord_459313).sum := by decide
  have hdescent : baseEnd_459313 < baseStart_459313 := by decide
  rcases family_descends (prefixWord ++ tailWord_459313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_459332 : List Nat := [2, 3, 5, 1, 2, 1, 2, 1, 3]
def baseStart_459332 : Nat := 118140960795 + 459332 * 2 ^ 59
def prefixEnd_459332 : Nat := 4983230072969 + 3 ^ 40 * 459332 * 2
def baseEnd_459332 : Nat := 209651640880979640122291

theorem tailTrace_459332 : CollatzResearch.WordTrace tailWord_459332 prefixEnd_459332 209651640880979640122291 := by
  unfold tailWord_459332
  simp only [CollatzResearch.WordTrace]
  refine ⟨8376607185963043252586125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11168809581284057670114833 8376607185963043252586125)
  ·
    refine ⟨3141227694736141219719797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8376607185963043252586125 3141227694736141219719797)
    ·
      refine ⟨294490096381513239348731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 3141227694736141219719797 294490096381513239348731)
      ·
        refine ⟨441735144572269859023097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 294490096381513239348731 441735144572269859023097)
        ·
          refine ⟨331301358429202394267323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 441735144572269859023097 331301358429202394267323)
          ·
            refine ⟨496952037643803591400985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 331301358429202394267323 496952037643803591400985)
            ·
              refine ⟨372714028232852693550739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 496952037643803591400985 372714028232852693550739)
              ·
                refine ⟨559071042349279040326109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 372714028232852693550739 559071042349279040326109)
                ·
                  refine ⟨209651640880979640122291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 559071042349279040326109 209651640880979640122291)
                  ·
                    rfl

theorem cell20_459332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 2, 1, 2, 1, 3].length) (baseStart_459332 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_459332 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_459332 prefixEnd_459332 := by exact prefixLift 459332
  have htrace : WordTrace (prefixWord ++ tailWord_459332) baseStart_459332 baseEnd_459332 := by
    simpa [prefixWord, tailWord_459332, baseEnd_459332] using wordTrace_append hprefix tailTrace_459332
  have hstable : (prefixWord ++ tailWord_459332).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_459332).length < 2 ^ (prefixWord ++ tailWord_459332).sum := by decide
  have hdescent : baseEnd_459332 < baseStart_459332 := by decide
  rcases family_descends (prefixWord ++ tailWord_459332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_459351 : List Nat := [1, 1, 3, 2, 2, 2, 2, 1, 6]
def baseStart_459351 : Nat := 118140960795 + 459351 * 2 ^ 59
def prefixEnd_459351 : Nat := 4983230072969 + 3 ^ 40 * 459351 * 2
def baseEnd_459351 : Nat := 209660312998700018488879

theorem tailTrace_459351 : CollatzResearch.WordTrace tailWord_459351 prefixEnd_459351 209660312998700018488879 := by
  unfold tailWord_459351
  simp only [CollatzResearch.WordTrace]
  refine ⟨16753907358857252750113907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11169271572571501833409271 16753907358857252750113907)
  ·
    refine ⟨25130861038285879125170861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16753907358857252750113907 25130861038285879125170861)
    ·
      refine ⟨9424072889357204671939073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25130861038285879125170861 9424072889357204671939073)
      ·
        refine ⟨7068054667017903503954305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9424072889357204671939073 7068054667017903503954305)
        ·
          refine ⟨5301041000263427627965729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7068054667017903503954305 5301041000263427627965729)
          ·
            refine ⟨3975780750197570720974297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5301041000263427627965729 3975780750197570720974297)
            ·
              refine ⟨2981835562648178040730723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3975780750197570720974297 2981835562648178040730723)
              ·
                refine ⟨4472753343972267061096085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2981835562648178040730723 4472753343972267061096085)
                ·
                  refine ⟨209660312998700018488879, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4472753343972267061096085 209660312998700018488879)
                  ·
                    rfl

theorem cell20_459351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 2, 1, 6].length) (baseStart_459351 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_459351 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_459351 prefixEnd_459351 := by exact prefixLift 459351
  have htrace : WordTrace (prefixWord ++ tailWord_459351) baseStart_459351 baseEnd_459351 := by
    simpa [prefixWord, tailWord_459351, baseEnd_459351] using wordTrace_append hprefix tailTrace_459351
  have hstable : (prefixWord ++ tailWord_459351).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_459351).length < 2 ^ (prefixWord ++ tailWord_459351).sum := by decide
  have hdescent : baseEnd_459351 < baseStart_459351 := by decide
  rcases family_descends (prefixWord ++ tailWord_459351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_459378 : List Nat := [3, 2, 1, 2, 4, 1, 2, 2, 3]
def baseStart_459378 : Nat := 118140960795 + 459378 * 2 ^ 59
def prefixEnd_459378 : Nat := 4983230072969 + 3 ^ 40 * 459378 * 2
def baseEnd_459378 : Nat := 209672636534407924588769

theorem tailTrace_459378 : CollatzResearch.WordTrace tailWord_459378 prefixEnd_459378 209672636534407924588769 := by
  unfold tailWord_459378
  simp only [CollatzResearch.WordTrace]
  refine ⟨4188723032439859090336697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11169928086506290907564525 4188723032439859090336697)
  ·
    refine ⟨3141542274329894317752523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4188723032439859090336697 3141542274329894317752523)
    ·
      refine ⟨4712313411494841476628785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3141542274329894317752523 4712313411494841476628785)
      ·
        refine ⟨3534235058621131107471589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4712313411494841476628785 3534235058621131107471589)
        ·
          refine ⟨662669073491462082650923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3534235058621131107471589 662669073491462082650923)
          ·
            refine ⟨994003610237193123976385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 662669073491462082650923 994003610237193123976385)
            ·
              refine ⟨745502707677894842982289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 994003610237193123976385 745502707677894842982289)
              ·
                refine ⟨559127030758421132236717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 745502707677894842982289 559127030758421132236717)
                ·
                  refine ⟨209672636534407924588769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 559127030758421132236717 209672636534407924588769)
                  ·
                    rfl

theorem cell20_459378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 1, 2, 2, 3].length) (baseStart_459378 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_459378 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_459378 prefixEnd_459378 := by exact prefixLift 459378
  have htrace : WordTrace (prefixWord ++ tailWord_459378) baseStart_459378 baseEnd_459378 := by
    simpa [prefixWord, tailWord_459378, baseEnd_459378] using wordTrace_append hprefix tailTrace_459378
  have hstable : (prefixWord ++ tailWord_459378).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_459378).length < 2 ^ (prefixWord ++ tailWord_459378).sum := by decide
  have hdescent : baseEnd_459378 < baseStart_459378 := by decide
  rcases family_descends (prefixWord ++ tailWord_459378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_459385 : List Nat := [1, 2, 1, 3, 3, 3, 1, 4, 2]
def baseStart_459385 : Nat := 118140960795 + 459385 * 2 ^ 59
def prefixEnd_459385 : Nat := 4983230072969 + 3 ^ 40 * 459385 * 2
def baseEnd_459385 : Nat := 209675831525147011355407

theorem tailTrace_459385 : CollatzResearch.WordTrace tailWord_459385 prefixEnd_459385 209675831525147011355407 := by
  unfold tailWord_459385
  simp only [CollatzResearch.WordTrace]
  refine ⟨16755147440734076556851609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11170098293822717704567739 16755147440734076556851609)
  ·
    refine ⟨12566360580550557417638707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16755147440734076556851609 12566360580550557417638707)
    ·
      refine ⟨18849540870825836126458061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12566360580550557417638707 18849540870825836126458061)
      ·
        refine ⟨7068577826559688547421773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18849540870825836126458061 7068577826559688547421773)
        ·
          refine ⟨2650716684959883205283165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7068577826559688547421773 2650716684959883205283165)
          ·
            refine ⟨994018756859956201981187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2650716684959883205283165 994018756859956201981187)
            ·
              refine ⟨1491028135289934302971781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 994018756859956201981187 1491028135289934302971781)
              ·
                refine ⟨279567775366862681807209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1491028135289934302971781 279567775366862681807209)
                ·
                  refine ⟨209675831525147011355407, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 279567775366862681807209 209675831525147011355407)
                  ·
                    rfl

theorem cell20_459385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 3, 1, 4, 2].length) (baseStart_459385 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_459385 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_459385 prefixEnd_459385 := by exact prefixLift 459385
  have htrace : WordTrace (prefixWord ++ tailWord_459385) baseStart_459385 baseEnd_459385 := by
    simpa [prefixWord, tailWord_459385, baseEnd_459385] using wordTrace_append hprefix tailTrace_459385
  have hstable : (prefixWord ++ tailWord_459385).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_459385).length < 2 ^ (prefixWord ++ tailWord_459385).sum := by decide
  have hdescent : baseEnd_459385 < baseStart_459385 := by decide
  rcases family_descends (prefixWord ++ tailWord_459385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_459406 : List Nat := [4, 1, 1, 3, 1, 1, 3, 2, 4]
def baseStart_459406 : Nat := 118140960795 + 459406 * 2 ^ 59
def prefixEnd_459406 : Nat := 4983230072969 + 3 ^ 40 * 459406 * 2
def baseEnd_459406 : Nat := 209685416497364271655321

theorem tailTrace_459406 : CollatzResearch.WordTrace tailWord_459406 prefixEnd_459406 209685416497364271655321 := by
  unfold tailWord_459406
  simp only [CollatzResearch.WordTrace]
  refine ⟨2094489171707249642920759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11170608915771998095577381 2094489171707249642920759)
  ·
    refine ⟨3141733757560874464381139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2094489171707249642920759 3141733757560874464381139)
    ·
      refine ⟨4712600636341311696571709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3141733757560874464381139 4712600636341311696571709)
      ·
        refine ⟨1767225238627991886214391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4712600636341311696571709 1767225238627991886214391)
        ·
          refine ⟨2650837857941987829321587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1767225238627991886214391 2650837857941987829321587)
          ·
            refine ⟨3976256786912981743982381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2650837857941987829321587 3976256786912981743982381)
            ·
              refine ⟨1491096295092368153993393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3976256786912981743982381 1491096295092368153993393)
              ·
                refine ⟨1118322221319276115495045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1491096295092368153993393 1118322221319276115495045)
                ·
                  refine ⟨209685416497364271655321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1118322221319276115495045 209685416497364271655321)
                  ·
                    rfl

theorem cell20_459406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 3, 2, 4].length) (baseStart_459406 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_459406 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_459406 prefixEnd_459406 := by exact prefixLift 459406
  have htrace : WordTrace (prefixWord ++ tailWord_459406) baseStart_459406 baseEnd_459406 := by
    simpa [prefixWord, tailWord_459406, baseEnd_459406] using wordTrace_append hprefix tailTrace_459406
  have hstable : (prefixWord ++ tailWord_459406).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_459406).length < 2 ^ (prefixWord ++ tailWord_459406).sum := by decide
  have hdescent : baseEnd_459406 < baseStart_459406 := by decide
  rcases family_descends (prefixWord ++ tailWord_459406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_459437 : List Nat := [1, 5, 2, 1, 1, 3, 1, 1, 5]
def baseStart_459437 : Nat := 118140960795 + 459437 * 2 ^ 59
def prefixEnd_459437 : Nat := 4983230072969 + 3 ^ 40 * 459437 * 2
def baseEnd_459437 : Nat := 209699565742065941621861

theorem tailTrace_459437 : CollatzResearch.WordTrace tailWord_459437 prefixEnd_459437 209699565742065941621861 := by
  unfold tailWord_459437
  simp only [CollatzResearch.WordTrace]
  refine ⟨16757044036545689437744565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11171362691030459625163043 16757044036545689437744565)
  ·
    refine ⟨1570972878426158384788553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 16757044036545689437744565 1570972878426158384788553)
    ·
      refine ⟨1178229658819618788591415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1570972878426158384788553 1178229658819618788591415)
      ·
        refine ⟨1767344488229428182887123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1178229658819618788591415 1767344488229428182887123)
        ·
          refine ⟨2651016732344142274330685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1767344488229428182887123 2651016732344142274330685)
          ·
            refine ⟨994131274629053352874007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2651016732344142274330685 994131274629053352874007)
            ·
              refine ⟨1491196911943580029311011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 994131274629053352874007 1491196911943580029311011)
              ·
                refine ⟨2236795367915370043966517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1491196911943580029311011 2236795367915370043966517)
                ·
                  refine ⟨209699565742065941621861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2236795367915370043966517 209699565742065941621861)
                  ·
                    rfl

theorem cell20_459437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 3, 1, 1, 5].length) (baseStart_459437 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_459437 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_459437 prefixEnd_459437 := by exact prefixLift 459437
  have htrace : WordTrace (prefixWord ++ tailWord_459437) baseStart_459437 baseEnd_459437 := by
    simpa [prefixWord, tailWord_459437, baseEnd_459437] using wordTrace_append hprefix tailTrace_459437
  have hstable : (prefixWord ++ tailWord_459437).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_459437).length < 2 ^ (prefixWord ++ tailWord_459437).sum := by decide
  have hdescent : baseEnd_459437 < baseStart_459437 := by decide
  rcases family_descends (prefixWord ++ tailWord_459437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_459454 : List Nat := [4, 2, 1, 1, 2, 1, 5, 1, 3]
def baseStart_459454 : Nat := 118140960795 + 459454 * 2 ^ 59
def prefixEnd_459454 : Nat := 4983230072969 + 3 ^ 40 * 459454 * 2
def baseEnd_459454 : Nat := 209707325005289438055125

theorem tailTrace_459454 : CollatzResearch.WordTrace tailWord_459454 prefixEnd_459454 209707325005289438055125 := by
  unfold tailWord_459454
  simp only [CollatzResearch.WordTrace]
  refine ⟨2094708009685512667639177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11171776051656067560742277 2094708009685512667639177)
  ·
    refine ⟨1571031007264134500729383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2094708009685512667639177 1571031007264134500729383)
    ·
      refine ⟨2356546510896201751094075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1571031007264134500729383 2356546510896201751094075)
      ·
        refine ⟨3534819766344302626641113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2356546510896201751094075 3534819766344302626641113)
        ·
          refine ⟨2651114824758226969980835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3534819766344302626641113 2651114824758226969980835)
          ·
            refine ⟨3976672237137340454971253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2651114824758226969980835 3976672237137340454971253)
            ·
              refine ⟨372813022231625667653555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3976672237137340454971253 372813022231625667653555)
              ·
                refine ⟨559219533347438501480333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 372813022231625667653555 559219533347438501480333)
                ·
                  refine ⟨209707325005289438055125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 559219533347438501480333 209707325005289438055125)
                  ·
                    rfl

theorem cell20_459454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 5, 1, 3].length) (baseStart_459454 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_459454 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_459454 prefixEnd_459454 := by exact prefixLift 459454
  have htrace : WordTrace (prefixWord ++ tailWord_459454) baseStart_459454 baseEnd_459454 := by
    simpa [prefixWord, tailWord_459454, baseEnd_459454] using wordTrace_append hprefix tailTrace_459454
  have hstable : (prefixWord ++ tailWord_459454).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_459454).length < 2 ^ (prefixWord ++ tailWord_459454).sum := by decide
  have hdescent : baseEnd_459454 < baseStart_459454 := by decide
  rcases family_descends (prefixWord ++ tailWord_459454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_459468 : List Nat := [2, 2, 1, 5, 1, 1, 4, 4]
def baseStart_459468 : Nat := 118140960795 + 459468 * 2 ^ 59
def prefixEnd_459468 : Nat := 4983230072969 + 3 ^ 40 * 459468 * 2
def baseEnd_459468 : Nat := 69904571662255870529467

theorem tailTrace_459468 : CollatzResearch.WordTrace tailWord_459468 prefixEnd_459468 69904571662255870529467 := by
  unfold tailWord_459468
  simp only [CollatzResearch.WordTrace]
  refine ⟨8379087349716690866061529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11172116466288921154748705 8379087349716690866061529)
  ·
    refine ⟨6284315512287518149546147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8379087349716690866061529 6284315512287518149546147)
    ·
      refine ⟨9426473268431277224319221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6284315512287518149546147 9426473268431277224319221)
      ·
        refine ⟨883731868915432239779927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 9426473268431277224319221 883731868915432239779927)
        ·
          refine ⟨1325597803373148359669891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 883731868915432239779927 1325597803373148359669891)
          ·
            refine ⟨1988396705059722539504837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1325597803373148359669891 1988396705059722539504837)
            ·
              refine ⟨372824382198697976157157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1988396705059722539504837 372824382198697976157157)
              ·
                refine ⟨69904571662255870529467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 372824382198697976157157 69904571662255870529467)
                ·
                  rfl

theorem cell20_459468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 4, 4].length) (baseStart_459468 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_459468 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_459468 prefixEnd_459468 := by exact prefixLift 459468
  have htrace : WordTrace (prefixWord ++ tailWord_459468) baseStart_459468 baseEnd_459468 := by
    simpa [prefixWord, tailWord_459468, baseEnd_459468] using wordTrace_append hprefix tailTrace_459468
  have hstable : (prefixWord ++ tailWord_459468).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_459468).length < 2 ^ (prefixWord ++ tailWord_459468).sum := by decide
  have hdescent : baseEnd_459468 < baseStart_459468 := by decide
  rcases family_descends (prefixWord ++ tailWord_459468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_459489 : List Nat := [1, 2, 3, 1, 4, 3, 6]
def baseStart_459489 : Nat := 118140960795 + 459489 * 2 ^ 59
def prefixEnd_459489 : Nat := 4983230072969 + 3 ^ 40 * 459489 * 2
def baseEnd_459489 : Nat := 23302588884331652432035

theorem tailTrace_459489 : CollatzResearch.WordTrace tailWord_459489 prefixEnd_459489 23302588884331652432035 := by
  unfold tailWord_459489
  simp only [CollatzResearch.WordTrace]
  refine ⟨16758940632357302318637521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11172627088238201545758347 16758940632357302318637521)
  ·
    refine ⟨12569205474267976738978141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16758940632357302318637521 12569205474267976738978141)
    ·
      refine ⟨4713452052850491277116803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12569205474267976738978141 4713452052850491277116803)
      ·
        refine ⟨7070178079275736915675205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4713452052850491277116803 7070178079275736915675205)
        ·
          refine ⟨1325658389864200671689101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7070178079275736915675205 1325658389864200671689101)
          ·
            refine ⟨497121896199075251883413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1325658389864200671689101 497121896199075251883413)
            ·
              refine ⟨23302588884331652432035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 497121896199075251883413 23302588884331652432035)
              ·
                rfl

theorem cell20_459489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 3, 6].length) (baseStart_459489 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_459489 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_459489 prefixEnd_459489 := by exact prefixLift 459489
  have htrace : WordTrace (prefixWord ++ tailWord_459489) baseStart_459489 baseEnd_459489 := by
    simpa [prefixWord, tailWord_459489, baseEnd_459489] using wordTrace_append hprefix tailTrace_459489
  have hstable : (prefixWord ++ tailWord_459489).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_459489).length < 2 ^ (prefixWord ++ tailWord_459489).sum := by decide
  have hdescent : baseEnd_459489 < baseStart_459489 := by decide
  rcases family_descends (prefixWord ++ tailWord_459489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_459527 : List Nat := [1, 1, 4, 4, 1, 1, 2, 6]
def baseStart_459527 : Nat := 118140960795 + 459527 * 2 ^ 59
def prefixEnd_459527 : Nat := 4983230072969 + 3 ^ 40 * 459527 * 2
def baseEnd_459527 : Nat := 69913548064808542873831

theorem tailTrace_459527 : CollatzResearch.WordTrace tailWord_459527 prefixEnd_459527 69913548064808542873831 := by
  unfold tailWord_459527
  simp only [CollatzResearch.WordTrace]
  refine ⟨16760326606219634808520835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11173551070813089872347223 16760326606219634808520835)
  ·
    refine ⟨25140489909329452212781253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16760326606219634808520835 25140489909329452212781253)
    ·
      refine ⟨4713841857999272289896485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 25140489909329452212781253 4713841857999272289896485)
      ·
        refine ⟨883845348374863554355591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4713841857999272289896485 883845348374863554355591)
        ·
          refine ⟨1325768022562295331533387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 883845348374863554355591 1325768022562295331533387)
          ·
            refine ⟨1988652033843442997300081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1325768022562295331533387 1988652033843442997300081)
            ·
              refine ⟨1491489025382582247975061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1988652033843442997300081 1491489025382582247975061)
              ·
                refine ⟨69913548064808542873831, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1491489025382582247975061 69913548064808542873831)
                ·
                  rfl

theorem cell20_459527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 2, 6].length) (baseStart_459527 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_459527 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_459527 prefixEnd_459527 := by exact prefixLift 459527
  have htrace : WordTrace (prefixWord ++ tailWord_459527) baseStart_459527 baseEnd_459527 := by
    simpa [prefixWord, tailWord_459527, baseEnd_459527] using wordTrace_append hprefix tailTrace_459527
  have hstable : (prefixWord ++ tailWord_459527).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_459527).length < 2 ^ (prefixWord ++ tailWord_459527).sum := by decide
  have hdescent : baseEnd_459527 < baseStart_459527 := by decide
  rcases family_descends (prefixWord ++ tailWord_459527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_459548 : List Nat := [2, 2, 3, 1, 1, 11]
def baseStart_459548 : Nat := 118140960795 + 459548 * 2 ^ 59
def prefixEnd_459548 : Nat := 4983230072969 + 3 ^ 40 * 459548 * 2
def baseEnd_459548 : Nat := 7768527006171958848941

theorem tailTrace_459548 : CollatzResearch.WordTrace tailWord_459548 prefixEnd_459548 7768527006171958848941 := by
  unfold tailWord_459548
  simp only [CollatzResearch.WordTrace]
  refine ⟨8380546269571777697517649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11174061692762370263356865 8380546269571777697517649)
  ·
    refine ⟨6285409702178833273138237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8380546269571777697517649 6285409702178833273138237)
    ·
      refine ⟨2357028638317062477426839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6285409702178833273138237 2357028638317062477426839)
      ·
        refine ⟨3535542957475593716140259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2357028638317062477426839 3535542957475593716140259)
        ·
          refine ⟨5303314436213390574210389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3535542957475593716140259 5303314436213390574210389)
          ·
            refine ⟨7768527006171958848941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 5303314436213390574210389 7768527006171958848941)
            ·
              rfl

theorem cell20_459548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 11].length) (baseStart_459548 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_459548 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_459548 prefixEnd_459548 := by exact prefixLift 459548
  have htrace : WordTrace (prefixWord ++ tailWord_459548) baseStart_459548 baseEnd_459548 := by
    simpa [prefixWord, tailWord_459548, baseEnd_459548] using wordTrace_append hprefix tailTrace_459548
  have hstable : (prefixWord ++ tailWord_459548).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_459548).length < 2 ^ (prefixWord ++ tailWord_459548).sum := by decide
  have hdescent : baseEnd_459548 < baseStart_459548 := by decide
  rcases family_descends (prefixWord ++ tailWord_459548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_459551 : List Nat := [1, 1, 2, 4, 2, 3, 2, 2, 3]
def baseStart_459551 : Nat := 118140960795 + 459551 * 2 ^ 59
def prefixEnd_459551 : Nat := 4983230072969 + 3 ^ 40 * 459551 * 2
def baseEnd_459551 : Nat := 209751598448388211821395

theorem tailTrace_459551 : CollatzResearch.WordTrace tailWord_459551 prefixEnd_459551 209751598448388211821395 := by
  unfold tailWord_459551
  simp only [CollatzResearch.WordTrace]
  refine ⟨16761201958132686907394507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11174134638755124604929671 16761201958132686907394507)
  ·
    refine ⟨25141802937199030361091761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16761201958132686907394507 25141802937199030361091761)
    ·
      refine ⟨18856352202899272770818821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25141802937199030361091761 18856352202899272770818821)
      ·
        refine ⟨3535566038043613644528529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18856352202899272770818821 3535566038043613644528529)
        ·
          refine ⟨2651674528532710233396397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3535566038043613644528529 2651674528532710233396397)
          ·
            refine ⟨994377948199766337523649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2651674528532710233396397 994377948199766337523649)
            ·
              refine ⟨745783461149824753142737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 994377948199766337523649 745783461149824753142737)
              ·
                refine ⟨559337595862368564857053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 745783461149824753142737 559337595862368564857053)
                ·
                  refine ⟨209751598448388211821395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 559337595862368564857053 209751598448388211821395)
                  ·
                    rfl

theorem cell20_459551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 3, 2, 2, 3].length) (baseStart_459551 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_459551 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_459551 prefixEnd_459551 := by exact prefixLift 459551
  have htrace : WordTrace (prefixWord ++ tailWord_459551) baseStart_459551 baseEnd_459551 := by
    simpa [prefixWord, tailWord_459551, baseEnd_459551] using wordTrace_append hprefix tailTrace_459551
  have hstable : (prefixWord ++ tailWord_459551).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_459551).length < 2 ^ (prefixWord ++ tailWord_459551).sum := by decide
  have hdescent : baseEnd_459551 < baseStart_459551 := by decide
  rcases family_descends (prefixWord ++ tailWord_459551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_459554 : List Nat := [3, 3, 1, 1, 2, 2, 4, 2, 2]
def baseStart_459554 : Nat := 118140960795 + 459554 * 2 ^ 59
def prefixEnd_459554 : Nat := 4983230072969 + 3 ^ 40 * 459554 * 2
def baseEnd_459554 : Nat := 209752967730133534721383

theorem tailTrace_459554 : CollatzResearch.WordTrace tailWord_459554 prefixEnd_459554 209752967730133534721383 := by
  unfold tailWord_459554
  simp only [CollatzResearch.WordTrace]
  refine ⟨4190327844280454604938429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11174207584747878946502477 4190327844280454604938429)
  ·
    refine ⟨1571372941605170476851911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4190327844280454604938429 1571372941605170476851911)
    ·
      refine ⟨2357059412407755715277867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1571372941605170476851911 2357059412407755715277867)
      ·
        refine ⟨3535589118611633572916801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2357059412407755715277867 3535589118611633572916801)
        ·
          refine ⟨2651691838958725179687601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3535589118611633572916801 2651691838958725179687601)
          ·
            refine ⟨1988768879219043884765701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2651691838958725179687601 1988768879219043884765701)
            ·
              refine ⟨372894164853570728393569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1988768879219043884765701 372894164853570728393569)
              ·
                refine ⟨279670623640178046295177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 372894164853570728393569 279670623640178046295177)
                ·
                  refine ⟨209752967730133534721383, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 279670623640178046295177 209752967730133534721383)
                  ·
                    rfl

theorem cell20_459554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 4, 2, 2].length) (baseStart_459554 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_459554 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_459554 prefixEnd_459554 := by exact prefixLift 459554
  have htrace : WordTrace (prefixWord ++ tailWord_459554) baseStart_459554 baseEnd_459554 := by
    simpa [prefixWord, tailWord_459554, baseEnd_459554] using wordTrace_append hprefix tailTrace_459554
  have hstable : (prefixWord ++ tailWord_459554).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_459554).length < 2 ^ (prefixWord ++ tailWord_459554).sum := by decide
  have hdescent : baseEnd_459554 < baseStart_459554 := by decide
  rcases family_descends (prefixWord ++ tailWord_459554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_459610 : List Nat := [3, 1, 1, 2, 1, 5, 1, 1, 5]
def baseStart_459610 : Nat := 118140960795 + 459610 * 2 ^ 59
def prefixEnd_459610 : Nat := 4983230072969 + 3 ^ 40 * 459610 * 2
def baseEnd_459610 : Nat := 209778527656046228854487

theorem tailTrace_459610 : CollatzResearch.WordTrace tailWord_459610 prefixEnd_459610 209778527656046228854487 := by
  unfold tailWord_459610
  simp only [CollatzResearch.WordTrace]
  refine ⟨4190838466229734995948071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11175569243279293322528189 4190838466229734995948071)
  ·
    refine ⟨6286257699344602493922107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4190838466229734995948071 6286257699344602493922107)
    ·
      refine ⟨9429386549016903740883161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6286257699344602493922107 9429386549016903740883161)
      ·
        refine ⟨7072039911762677805662371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9429386549016903740883161 7072039911762677805662371)
        ·
          refine ⟨10608059867644016708493557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7072039911762677805662371 10608059867644016708493557)
          ·
            refine ⟨994505612591626566421271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 10608059867644016708493557 994505612591626566421271)
            ·
              refine ⟨1491758418887439849631907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 994505612591626566421271 1491758418887439849631907)
              ·
                refine ⟨2237637628331159774447861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1491758418887439849631907 2237637628331159774447861)
                ·
                  refine ⟨209778527656046228854487, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2237637628331159774447861 209778527656046228854487)
                  ·
                    rfl

theorem cell20_459610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 5, 1, 1, 5].length) (baseStart_459610 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_459610 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_459610 prefixEnd_459610 := by exact prefixLift 459610
  have htrace : WordTrace (prefixWord ++ tailWord_459610) baseStart_459610 baseEnd_459610 := by
    simpa [prefixWord, tailWord_459610, baseEnd_459610] using wordTrace_append hprefix tailTrace_459610
  have hstable : (prefixWord ++ tailWord_459610).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_459610).length < 2 ^ (prefixWord ++ tailWord_459610).sum := by decide
  have hdescent : baseEnd_459610 < baseStart_459610 := by decide
  rcases family_descends (prefixWord ++ tailWord_459610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_459641 : List Nat := [1, 2, 1, 3, 2, 3, 4, 4]
def baseStart_459641 : Nat := 118140960795 + 459641 * 2 ^ 59
def prefixEnd_459641 : Nat := 4983230072969 + 3 ^ 40 * 459641 * 2
def baseEnd_459641 : Nat := 69930892300249299607009

theorem tailTrace_459641 : CollatzResearch.WordTrace tailWord_459641 prefixEnd_459641 69930892300249299607009 := by
  unfold tailWord_459641
  simp only [CollatzResearch.WordTrace]
  refine ⟨16764484527806632278170777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11176323018537754852113851 16764484527806632278170777)
  ·
    refine ⟨12573363395854974208628083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16764484527806632278170777 12573363395854974208628083)
    ·
      refine ⟨18860045093782461312942125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12573363395854974208628083 18860045093782461312942125)
      ·
        refine ⟨7072516910168422992353297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18860045093782461312942125 7072516910168422992353297)
        ·
          refine ⟨5304387682626317244264973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7072516910168422992353297 5304387682626317244264973)
          ·
            refine ⟨1989145380984868966599365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5304387682626317244264973 1989145380984868966599365)
            ·
              refine ⟨372964758934662931237381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1989145380984868966599365 372964758934662931237381)
              ·
                refine ⟨69930892300249299607009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 372964758934662931237381 69930892300249299607009)
                ·
                  rfl

theorem cell20_459641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 4, 4].length) (baseStart_459641 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_459641 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_459641 prefixEnd_459641 := by exact prefixLift 459641
  have htrace : WordTrace (prefixWord ++ tailWord_459641) baseStart_459641 baseEnd_459641 := by
    simpa [prefixWord, tailWord_459641, baseEnd_459641] using wordTrace_append hprefix tailTrace_459641
  have hstable : (prefixWord ++ tailWord_459641).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_459641).length < 2 ^ (prefixWord ++ tailWord_459641).sum := by decide
  have hdescent : baseEnd_459641 < baseStart_459641 := by decide
  rcases family_descends (prefixWord ++ tailWord_459641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_459668 : List Nat := [2, 4, 2, 1, 1, 1, 5, 2, 2]
def baseStart_459668 : Nat := 118140960795 + 459668 * 2 ^ 59
def prefixEnd_459668 : Nat := 4983230072969 + 3 ^ 40 * 459668 * 2
def baseEnd_459668 : Nat := 209805000436455804920917

theorem tailTrace_459668 : CollatzResearch.WordTrace tailWord_459668 prefixEnd_459668 209805000436455804920917 := by
  unfold tailWord_459668
  simp only [CollatzResearch.WordTrace]
  refine ⟨8382734649354407944701829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11176979532472543926269105 8382734649354407944701829)
  ·
    refine ⟨1571762746753951489631593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8382734649354407944701829 1571762746753951489631593)
    ·
      refine ⟨1178822060065463617223695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1571762746753951489631593 1178822060065463617223695)
      ·
        refine ⟨1768233090098195425835543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1178822060065463617223695 1768233090098195425835543)
        ·
          refine ⟨2652349635147293138753315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1768233090098195425835543 2652349635147293138753315)
          ·
            refine ⟨3978524452720939708129973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2652349635147293138753315 3978524452720939708129973)
            ·
              refine ⟨372986667442588097637185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3978524452720939708129973 372986667442588097637185)
              ·
                refine ⟨279740000581941073227889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 372986667442588097637185 279740000581941073227889)
                ·
                  refine ⟨209805000436455804920917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 279740000581941073227889 209805000436455804920917)
                  ·
                    rfl

theorem cell20_459668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 5, 2, 2].length) (baseStart_459668 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_459668 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_459668 prefixEnd_459668 := by exact prefixLift 459668
  have htrace : WordTrace (prefixWord ++ tailWord_459668) baseStart_459668 baseEnd_459668 := by
    simpa [prefixWord, tailWord_459668, baseEnd_459668] using wordTrace_append hprefix tailTrace_459668
  have hstable : (prefixWord ++ tailWord_459668).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_459668).length < 2 ^ (prefixWord ++ tailWord_459668).sum := by decide
  have hdescent : baseEnd_459668 < baseStart_459668 := by decide
  rcases family_descends (prefixWord ++ tailWord_459668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_459679 : List Nat := [1, 1, 2, 5, 2, 2, 2, 5]
def baseStart_459679 : Nat := 118140960795 + 459679 * 2 ^ 59
def prefixEnd_459679 : Nat := 4983230072969 + 3 ^ 40 * 459679 * 2
def baseEnd_459679 : Nat := 69936673712062885184735

theorem tailTrace_459679 : CollatzResearch.WordTrace tailWord_459679 prefixEnd_459679 69936673712062885184735 := by
  unfold tailWord_459679
  simp only [CollatzResearch.WordTrace]
  refine ⟨16765870501668964768054091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11177247001112643178702727 16765870501668964768054091)
  ·
    refine ⟨25148805752503447152081137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16765870501668964768054091 25148805752503447152081137)
    ·
      refine ⟨18861604314377585364060853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25148805752503447152081137 18861604314377585364060853)
      ·
        refine ⟨1768275404472898627880705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 18861604314377585364060853 1768275404472898627880705)
        ·
          refine ⟨1326206553354673970910529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1768275404472898627880705 1326206553354673970910529)
          ·
            refine ⟨994654915016005478182897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1326206553354673970910529 994654915016005478182897)
            ·
              refine ⟨745991186262004108637173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 994654915016005478182897 745991186262004108637173)
              ·
                refine ⟨69936673712062885184735, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 745991186262004108637173 69936673712062885184735)
                ·
                  rfl

theorem cell20_459679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 2, 2, 5].length) (baseStart_459679 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_459679 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_459679 prefixEnd_459679 := by exact prefixLift 459679
  have htrace : WordTrace (prefixWord ++ tailWord_459679) baseStart_459679 baseEnd_459679 := by
    simpa [prefixWord, tailWord_459679, baseEnd_459679] using wordTrace_append hprefix tailTrace_459679
  have hstable : (prefixWord ++ tailWord_459679).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_459679).length < 2 ^ (prefixWord ++ tailWord_459679).sum := by decide
  have hdescent : baseEnd_459679 < baseStart_459679 := by decide
  rcases family_descends (prefixWord ++ tailWord_459679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_459682 : List Nat := [3, 3, 1, 2, 2, 1, 4, 1, 3]
def baseStart_459682 : Nat := 118140960795 + 459682 * 2 ^ 59
def prefixEnd_459682 : Nat := 4983230072969 + 3 ^ 40 * 459682 * 2
def baseEnd_459682 : Nat := 209811390417933978454193

theorem tailTrace_459682 : CollatzResearch.WordTrace tailWord_459682 prefixEnd_459682 209811390417933978454193 := by
  unfold tailWord_459682
  simp only [CollatzResearch.WordTrace]
  refine ⟨4191494980164524070103325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11177319947105397520275533 4191494980164524070103325)
  ·
    refine ⟨1571810617561696526288747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4191494980164524070103325 1571810617561696526288747)
    ·
      refine ⟨2357715926342544789433121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1571810617561696526288747 2357715926342544789433121)
      ·
        refine ⟨1768286944756908592074841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2357715926342544789433121 1768286944756908592074841)
        ·
          refine ⟨1326215208567681444056131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1768286944756908592074841 1326215208567681444056131)
          ·
            refine ⟨1989322812851522166084197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1326215208567681444056131 1989322812851522166084197)
            ·
              refine ⟨372998027409660406140787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1989322812851522166084197 372998027409660406140787)
              ·
                refine ⟨559497041114490609211181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 372998027409660406140787 559497041114490609211181)
                ·
                  refine ⟨209811390417933978454193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 559497041114490609211181 209811390417933978454193)
                  ·
                    rfl

theorem cell20_459682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 4, 1, 3].length) (baseStart_459682 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_459682 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_459682 prefixEnd_459682 := by exact prefixLift 459682
  have htrace : WordTrace (prefixWord ++ tailWord_459682) baseStart_459682 baseEnd_459682 := by
    simpa [prefixWord, tailWord_459682, baseEnd_459682] using wordTrace_append hprefix tailTrace_459682
  have hstable : (prefixWord ++ tailWord_459682).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_459682).length < 2 ^ (prefixWord ++ tailWord_459682).sum := by decide
  have hdescent : baseEnd_459682 < baseStart_459682 := by decide
  rcases family_descends (prefixWord ++ tailWord_459682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_459727 : List Nat := [1, 1, 2, 1, 1, 6, 4, 2, 2]
def baseStart_459727 : Nat := 118140960795 + 459727 * 2 ^ 59
def prefixEnd_459727 : Nat := 4983230072969 + 3 ^ 40 * 459727 * 2
def baseEnd_459727 : Nat := 209831929644113821954009

theorem tailTrace_459727 : CollatzResearch.WordTrace tailWord_459727 prefixEnd_459727 209831929644113821954009 := by
  unfold tailWord_459727
  simp only [CollatzResearch.WordTrace]
  refine ⟨16767621205495068965801435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11178414136996712643867623 16767621205495068965801435)
  ·
    refine ⟨25151431808242603448702153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16767621205495068965801435 25151431808242603448702153)
    ·
      refine ⟨18863573856181952586526615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25151431808242603448702153 18863573856181952586526615)
      ·
        refine ⟨28295360784272928879789923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18863573856181952586526615 28295360784272928879789923)
        ·
          refine ⟨42443041176409393319684885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28295360784272928879789923 42443041176409393319684885)
          ·
            refine ⟨1989517555144190311860229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 42443041176409393319684885 1989517555144190311860229)
            ·
              refine ⟨373034541589535683473793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1989517555144190311860229 373034541589535683473793)
              ·
                refine ⟨279775906192151762605345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 373034541589535683473793 279775906192151762605345)
                ·
                  refine ⟨209831929644113821954009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 279775906192151762605345 209831929644113821954009)
                  ·
                    rfl

theorem cell20_459727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 4, 2, 2].length) (baseStart_459727 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_459727 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_459727 prefixEnd_459727 := by exact prefixLift 459727
  have htrace : WordTrace (prefixWord ++ tailWord_459727) baseStart_459727 baseEnd_459727 := by
    simpa [prefixWord, tailWord_459727, baseEnd_459727] using wordTrace_append hprefix tailTrace_459727
  have hstable : (prefixWord ++ tailWord_459727).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_459727).length < 2 ^ (prefixWord ++ tailWord_459727).sum := by decide
  have hdescent : baseEnd_459727 < baseStart_459727 := by decide
  rcases family_descends (prefixWord ++ tailWord_459727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_459734 : List Nat := [5, 2, 1, 1, 2, 1, 3, 5]
def baseStart_459734 : Nat := 118140960795 + 459734 * 2 ^ 59
def prefixEnd_459734 : Nat := 4983230072969 + 3 ^ 40 * 459734 * 2
def baseEnd_459734 : Nat := 69945041544950969573549

theorem tailTrace_459734 : CollatzResearch.WordTrace tailWord_459734 prefixEnd_459734 69945041544950969573549 := by
  unfold tailWord_459734
  simp only [CollatzResearch.WordTrace]
  refine ⟨1047992282279356822581641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 11178584344313139440870837 1047992282279356822581641)
  ·
    refine ⟨785994211709517616936231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1047992282279356822581641 785994211709517616936231)
    ·
      refine ⟨1178991317564276425404347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 785994211709517616936231 1178991317564276425404347)
      ·
        refine ⟨1768486976346414638106521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1178991317564276425404347 1768486976346414638106521)
        ·
          refine ⟨1326365232259810978579891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1768486976346414638106521 1326365232259810978579891)
          ·
            refine ⟨1989547848389716467869837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1326365232259810978579891 1989547848389716467869837)
            ·
              refine ⟨746080443146143675451189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1989547848389716467869837 746080443146143675451189)
              ·
                refine ⟨69945041544950969573549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 746080443146143675451189 69945041544950969573549)
                ·
                  rfl

theorem cell20_459734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 3, 5].length) (baseStart_459734 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_459734 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_459734 prefixEnd_459734 := by exact prefixLift 459734
  have htrace : WordTrace (prefixWord ++ tailWord_459734) baseStart_459734 baseEnd_459734 := by
    simpa [prefixWord, tailWord_459734, baseEnd_459734] using wordTrace_append hprefix tailTrace_459734
  have hstable : (prefixWord ++ tailWord_459734).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_459734).length < 2 ^ (prefixWord ++ tailWord_459734).sum := by decide
  have hdescent : baseEnd_459734 < baseStart_459734 := by decide
  rcases family_descends (prefixWord ++ tailWord_459734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_459741 : List Nat := [1, 4, 3, 1, 2, 1, 2, 3, 3]
def baseStart_459741 : Nat := 118140960795 + 459741 * 2 ^ 59
def prefixEnd_459741 : Nat := 4983230072969 + 3 ^ 40 * 459741 * 2
def baseEnd_459741 : Nat := 209838319625591995487285

theorem tailTrace_459741 : CollatzResearch.WordTrace tailWord_459741 prefixEnd_459741 209838319625591995487285 := by
  unfold tailWord_459741
  simp only [CollatzResearch.WordTrace]
  refine ⟨16768131827444349356811077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11178754551629566237874051 16768131827444349356811077)
  ·
    refine ⟨3144024717645815504402077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16768131827444349356811077 3144024717645815504402077)
    ·
      refine ⟨1179009269117180814150779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3144024717645815504402077 1179009269117180814150779)
      ·
        refine ⟨1768513903675771221226169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1179009269117180814150779 1768513903675771221226169)
        ·
          refine ⟨1326385427756828415919627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1768513903675771221226169 1326385427756828415919627)
          ·
            refine ⟨1989578141635242623879441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1326385427756828415919627 1989578141635242623879441)
            ·
              refine ⟨1492183606226431967909581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1989578141635242623879441 1492183606226431967909581)
              ·
                refine ⟨559568852334911987966093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1492183606226431967909581 559568852334911987966093)
                ·
                  refine ⟨209838319625591995487285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 559568852334911987966093 209838319625591995487285)
                  ·
                    rfl

theorem cell20_459741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 2, 3, 3].length) (baseStart_459741 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_459741 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_459741 prefixEnd_459741 := by exact prefixLift 459741
  have htrace : WordTrace (prefixWord ++ tailWord_459741) baseStart_459741 baseEnd_459741 := by
    simpa [prefixWord, tailWord_459741, baseEnd_459741] using wordTrace_append hprefix tailTrace_459741
  have hstable : (prefixWord ++ tailWord_459741).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_459741).length < 2 ^ (prefixWord ++ tailWord_459741).sum := by decide
  have hdescent : baseEnd_459741 < baseStart_459741 := by decide
  rcases family_descends (prefixWord ++ tailWord_459741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_459745 : List Nat := [1, 2, 3, 1, 2, 1, 1, 2, 7]
def baseStart_459745 : Nat := 118140960795 + 459745 * 2 ^ 59
def prefixEnd_459745 : Nat := 4983230072969 + 3 ^ 40 * 459745 * 2
def baseEnd_459745 : Nat := 209840145334585759353935

theorem tailTrace_459745 : CollatzResearch.WordTrace tailWord_459745 prefixEnd_459745 209840145334585759353935 := by
  unfold tailWord_459745
  simp only [CollatzResearch.WordTrace]
  refine ⟨16768277719429858039956689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11178851812953238693304459 16768277719429858039956689)
  ·
    refine ⟨12576208289572393529967517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16768277719429858039956689 12576208289572393529967517)
    ·
      refine ⟨4716078108589647573737819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12576208289572393529967517 4716078108589647573737819)
      ·
        refine ⟨7074117162884471360606729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4716078108589647573737819 7074117162884471360606729)
        ·
          refine ⟨5305587872163353520455047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7074117162884471360606729 5305587872163353520455047)
          ·
            refine ⟨7958381808245030280682571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5305587872163353520455047 7958381808245030280682571)
            ·
              refine ⟨11937572712367545421023857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7958381808245030280682571 11937572712367545421023857)
              ·
                refine ⟨8953179534275659065767893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11937572712367545421023857 8953179534275659065767893)
                ·
                  refine ⟨209840145334585759353935, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8953179534275659065767893 209840145334585759353935)
                  ·
                    rfl

theorem cell20_459745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 2, 7].length) (baseStart_459745 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_459745 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_459745 prefixEnd_459745 := by exact prefixLift 459745
  have htrace : WordTrace (prefixWord ++ tailWord_459745) baseStart_459745 baseEnd_459745 := by
    simpa [prefixWord, tailWord_459745, baseEnd_459745] using wordTrace_append hprefix tailTrace_459745
  have hstable : (prefixWord ++ tailWord_459745).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_459745).length < 2 ^ (prefixWord ++ tailWord_459745).sum := by decide
  have hdescent : baseEnd_459745 < baseStart_459745 := by decide
  rcases family_descends (prefixWord ++ tailWord_459745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_459786 : List Nat := [3, 1, 2, 2, 3, 2, 2, 1, 4]
def baseStart_459786 : Nat := 118140960795 + 459786 * 2 ^ 59
def prefixEnd_459786 : Nat := 4983230072969 + 3 ^ 40 * 459786 * 2
def baseEnd_459786 : Nat := 209858858851771838987101

theorem tailTrace_459786 : CollatzResearch.WordTrace tailWord_459786 prefixEnd_459786 209858858851771838987101 := by
  unfold tailWord_459786
  simp only [CollatzResearch.WordTrace]
  refine ⟨4192443278070330510549803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11179848741520881361466141 4192443278070330510549803)
  ·
    refine ⟨6288664917105495765824705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4192443278070330510549803 6288664917105495765824705)
    ·
      refine ⟨4716498687829121824368529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6288664917105495765824705 4716498687829121824368529)
      ·
        refine ⟨3537374015871841368276397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4716498687829121824368529 3537374015871841368276397)
        ·
          refine ⟨1326515255951940513103649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3537374015871841368276397 1326515255951940513103649)
          ·
            refine ⟨994886441963955384827737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1326515255951940513103649 994886441963955384827737)
            ·
              refine ⟨746164831472966538620803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 994886441963955384827737 746164831472966538620803)
              ·
                refine ⟨1119247247209449807931205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 746164831472966538620803 1119247247209449807931205)
                ·
                  refine ⟨209858858851771838987101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1119247247209449807931205 209858858851771838987101)
                  ·
                    rfl

theorem cell20_459786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 2, 2, 1, 4].length) (baseStart_459786 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_459786 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_459786 prefixEnd_459786 := by exact prefixLift 459786
  have htrace : WordTrace (prefixWord ++ tailWord_459786) baseStart_459786 baseEnd_459786 := by
    simpa [prefixWord, tailWord_459786, baseEnd_459786] using wordTrace_append hprefix tailTrace_459786
  have hstable : (prefixWord ++ tailWord_459786).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_459786).length < 2 ^ (prefixWord ++ tailWord_459786).sum := by decide
  have hdescent : baseEnd_459786 < baseStart_459786 := by decide
  rcases family_descends (prefixWord ++ tailWord_459786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_459807 : List Nat := [1, 1, 2, 4, 1, 3, 2, 2, 4]
def baseStart_459807 : Nat := 118140960795 + 459807 * 2 ^ 59
def prefixEnd_459807 : Nat := 4983230072969 + 3 ^ 40 * 459807 * 2
def baseEnd_459807 : Nat := 209868443823989099287015

theorem tailTrace_459807 : CollatzResearch.WordTrace tailWord_459807 prefixEnd_459807 209868443823989099287015 := by
  unfold tailWord_459807
  simp only [CollatzResearch.WordTrace]
  refine ⟨16770539045205242628713675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11180359363470161752475783 16770539045205242628713675)
  ·
    refine ⟨25155808567807863943070513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16770539045205242628713675 25155808567807863943070513)
    ·
      refine ⟨18866856425855897957302885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25155808567807863943070513 18866856425855897957302885)
      ·
        refine ⟨3537535579847980866994291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18866856425855897957302885 3537535579847980866994291)
        ·
          refine ⟨5306303369771971300491437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3537535579847980866994291 5306303369771971300491437)
          ·
            refine ⟨1989863763664489237684289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5306303369771971300491437 1989863763664489237684289)
            ·
              refine ⟨1492397822748366928263217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1989863763664489237684289 1492397822748366928263217)
              ·
                refine ⟨1119298367061275196197413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1492397822748366928263217 1119298367061275196197413)
                ·
                  refine ⟨209868443823989099287015, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1119298367061275196197413 209868443823989099287015)
                  ·
                    rfl

theorem cell20_459807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 2, 2, 4].length) (baseStart_459807 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_459807 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_459807 prefixEnd_459807 := by exact prefixLift 459807
  have htrace : WordTrace (prefixWord ++ tailWord_459807) baseStart_459807 baseEnd_459807 := by
    simpa [prefixWord, tailWord_459807, baseEnd_459807] using wordTrace_append hprefix tailTrace_459807
  have hstable : (prefixWord ++ tailWord_459807).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_459807).length < 2 ^ (prefixWord ++ tailWord_459807).sum := by decide
  have hdescent : baseEnd_459807 < baseStart_459807 := by decide
  rcases family_descends (prefixWord ++ tailWord_459807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_459810 : List Nat := [3, 3, 1, 1, 1, 5, 2, 4]
def baseStart_459810 : Nat := 118140960795 + 459810 * 2 ^ 59
def prefixEnd_459810 : Nat := 4983230072969 + 3 ^ 40 * 459810 * 2
def baseEnd_459810 : Nat := 69956604368578140729001

theorem tailTrace_459810 : CollatzResearch.WordTrace tailWord_459810 prefixEnd_459810 69956604368578140729001 := by
  unfold tailWord_459810
  simp only [CollatzResearch.WordTrace]
  refine ⟨4192662116048593535268221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11180432309462916094048589 4192662116048593535268221)
  ·
    refine ⟨1572248293518222575725583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4192662116048593535268221 1572248293518222575725583)
    ·
      refine ⟨2358372440277333863588375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1572248293518222575725583 2358372440277333863588375)
      ·
        refine ⟨3537558660416000795382563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2358372440277333863588375 3537558660416000795382563)
        ·
          refine ⟨5306337990624001193073845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3537558660416000795382563 5306337990624001193073845)
          ·
            refine ⟨497469186621000111850673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 5306337990624001193073845 497469186621000111850673)
            ·
              refine ⟨373101889965750083888005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 497469186621000111850673 373101889965750083888005)
              ·
                refine ⟨69956604368578140729001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 373101889965750083888005 69956604368578140729001)
                ·
                  rfl

theorem cell20_459810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 5, 2, 4].length) (baseStart_459810 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_459810 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_459810 prefixEnd_459810 := by exact prefixLift 459810
  have htrace : WordTrace (prefixWord ++ tailWord_459810) baseStart_459810 baseEnd_459810 := by
    simpa [prefixWord, tailWord_459810, baseEnd_459810] using wordTrace_append hprefix tailTrace_459810
  have hstable : (prefixWord ++ tailWord_459810).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_459810).length < 2 ^ (prefixWord ++ tailWord_459810).sum := by decide
  have hdescent : baseEnd_459810 < baseStart_459810 := by decide
  rcases family_descends (prefixWord ++ tailWord_459810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_459841 : List Nat := [1, 2, 5, 1, 3, 2, 1, 1, 4]
def baseStart_459841 : Nat := 118140960795 + 459841 * 2 ^ 59
def prefixEnd_459841 : Nat := 4983230072969 + 3 ^ 40 * 459841 * 2
def baseEnd_459841 : Nat := 209883962350436092153543

theorem tailTrace_459841 : CollatzResearch.WordTrace tailWord_459841 prefixEnd_459841 209883962350436092153543 := by
  unfold tailWord_459841
  simp only [CollatzResearch.WordTrace]
  refine ⟨16771779127082066435451377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11181186084721377623634251 16771779127082066435451377)
  ·
    refine ⟨12578834345311549826588533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16771779127082066435451377 12578834345311549826588533)
    ·
      refine ⟨1179265719872957796242675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 12578834345311549826588533 1179265719872957796242675)
      ·
        refine ⟨1768898579809436694364013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1179265719872957796242675 1768898579809436694364013)
        ·
          refine ⟨663336967428538760386505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1768898579809436694364013 663336967428538760386505)
          ·
            refine ⟨497502725571404070289879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 663336967428538760386505 497502725571404070289879)
            ·
              refine ⟨746254088357106105434819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 497502725571404070289879 746254088357106105434819)
              ·
                refine ⟨1119381132535659158152229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 746254088357106105434819 1119381132535659158152229)
                ·
                  refine ⟨209883962350436092153543, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1119381132535659158152229 209883962350436092153543)
                  ·
                    rfl

theorem cell20_459841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 2, 1, 1, 4].length) (baseStart_459841 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_459841 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_459841 prefixEnd_459841 := by exact prefixLift 459841
  have htrace : WordTrace (prefixWord ++ tailWord_459841) baseStart_459841 baseEnd_459841 := by
    simpa [prefixWord, tailWord_459841, baseEnd_459841] using wordTrace_append hprefix tailTrace_459841
  have hstable : (prefixWord ++ tailWord_459841).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_459841).length < 2 ^ (prefixWord ++ tailWord_459841).sum := by decide
  have hdescent : baseEnd_459841 < baseStart_459841 := by decide
  rcases family_descends (prefixWord ++ tailWord_459841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_459845 : List Nat := [1, 3, 1, 1, 1, 3, 5, 1, 4]
def baseStart_459845 : Nat := 118140960795 + 459845 * 2 ^ 59
def prefixEnd_459845 : Nat := 4983230072969 + 3 ^ 40 * 459845 * 2
def baseEnd_459845 : Nat := 209885788059429856020193

theorem tailTrace_459845 : CollatzResearch.WordTrace tailWord_459845 prefixEnd_459845 209885788059429856020193 := by
  unfold tailWord_459845
  simp only [CollatzResearch.WordTrace]
  refine ⟨16771925019067575118596989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11181283346045050079064659 16771925019067575118596989)
  ·
    refine ⟨6289471882150340669473871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16771925019067575118596989 6289471882150340669473871)
    ·
      refine ⟨9434207823225511004210807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6289471882150340669473871 9434207823225511004210807)
      ·
        refine ⟨14151311734838266506316211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9434207823225511004210807 14151311734838266506316211)
        ·
          refine ⟨21226967602257399759474317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14151311734838266506316211 21226967602257399759474317)
          ·
            refine ⟨7960112850846524909802869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21226967602257399759474317 7960112850846524909802869)
            ·
              refine ⟨746260579766861710294019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 7960112850846524909802869 746260579766861710294019)
              ·
                refine ⟨1119390869650292565441029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 746260579766861710294019 1119390869650292565441029)
                ·
                  refine ⟨209885788059429856020193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1119390869650292565441029 209885788059429856020193)
                  ·
                    rfl

theorem cell20_459845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 5, 1, 4].length) (baseStart_459845 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_459845 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_459845 prefixEnd_459845 := by exact prefixLift 459845
  have htrace : WordTrace (prefixWord ++ tailWord_459845) baseStart_459845 baseEnd_459845 := by
    simpa [prefixWord, tailWord_459845, baseEnd_459845] using wordTrace_append hprefix tailTrace_459845
  have hstable : (prefixWord ++ tailWord_459845).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_459845).length < 2 ^ (prefixWord ++ tailWord_459845).sum := by decide
  have hdescent : baseEnd_459845 < baseStart_459845 := by decide
  rcases family_descends (prefixWord ++ tailWord_459845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_459900 : List Nat := [2, 2, 2, 1, 1, 3, 3, 4, 2]
def baseStart_459900 : Nat := 118140960795 + 459900 * 2 ^ 59
def prefixEnd_459900 : Nat := 4983230072969 + 3 ^ 40 * 459900 * 2
def baseEnd_459900 : Nat := 209910891558094109186635

theorem tailTrace_459900 : CollatzResearch.WordTrace tailWord_459900 prefixEnd_459900 209910891558094109186635 := by
  unfold tailWord_459900
  simp only [CollatzResearch.WordTrace]
  refine ⟨8386965516934159755924577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11182620689245546341232769 8386965516934159755924577)
  ·
    refine ⟨6290224137700619816943433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8386965516934159755924577 6290224137700619816943433)
    ·
      refine ⟨4717668103275464862707575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6290224137700619816943433 4717668103275464862707575)
      ·
        refine ⟨7076502154913197294061363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4717668103275464862707575 7076502154913197294061363)
        ·
          refine ⟨10614753232369795941092045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7076502154913197294061363 10614753232369795941092045)
          ·
            refine ⟨3980532462138673477909517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10614753232369795941092045 3980532462138673477909517)
            ·
              refine ⟨1492699673302002554216069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3980532462138673477909517 1492699673302002554216069)
              ·
                refine ⟨279881188744125478915513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1492699673302002554216069 279881188744125478915513)
                ·
                  refine ⟨209910891558094109186635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 279881188744125478915513 209910891558094109186635)
                  ·
                    rfl

theorem cell20_459900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 3, 4, 2].length) (baseStart_459900 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_459900 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_459900 prefixEnd_459900 := by exact prefixLift 459900
  have htrace : WordTrace (prefixWord ++ tailWord_459900) baseStart_459900 baseEnd_459900 := by
    simpa [prefixWord, tailWord_459900, baseEnd_459900] using wordTrace_append hprefix tailTrace_459900
  have hstable : (prefixWord ++ tailWord_459900).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_459900).length < 2 ^ (prefixWord ++ tailWord_459900).sum := by decide
  have hdescent : baseEnd_459900 < baseStart_459900 := by decide
  rcases family_descends (prefixWord ++ tailWord_459900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_459914 : List Nat := [3, 1, 2, 3, 1, 1, 1, 5, 3]
def baseStart_459914 : Nat := 118140960795 + 459914 * 2 ^ 59
def prefixEnd_459914 : Nat := 4983230072969 + 3 ^ 40 * 459914 * 2
def baseEnd_459914 : Nat := 209917281539572282719911

theorem tailTrace_459914 : CollatzResearch.WordTrace tailWord_459914 prefixEnd_459914 209917281539572282719911 := by
  unfold tailWord_459914
  simp only [CollatzResearch.WordTrace]
  refine ⟨4193610413954399975714699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11182961103878399935239197 4193610413954399975714699)
  ·
    refine ⟨6290415620931599963572049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4193610413954399975714699 6290415620931599963572049)
    ·
      refine ⟨4717811715698699972679037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6290415620931599963572049 4717811715698699972679037)
      ·
        refine ⟨1769179393387012489754639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4717811715698699972679037 1769179393387012489754639)
        ·
          refine ⟨2653769090080518734631959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1769179393387012489754639 2653769090080518734631959)
          ·
            refine ⟨3980653635120778101947939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2653769090080518734631959 3980653635120778101947939)
            ·
              refine ⟨5970980452681167152921909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3980653635120778101947939 5970980452681167152921909)
              ·
                refine ⟨559779417438859420586429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5970980452681167152921909 559779417438859420586429)
                ·
                  refine ⟨209917281539572282719911, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 559779417438859420586429 209917281539572282719911)
                  ·
                    rfl

theorem cell20_459914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 1, 5, 3].length) (baseStart_459914 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_459914 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_459914 prefixEnd_459914 := by exact prefixLift 459914
  have htrace : WordTrace (prefixWord ++ tailWord_459914) baseStart_459914 baseEnd_459914 := by
    simpa [prefixWord, tailWord_459914, baseEnd_459914] using wordTrace_append hprefix tailTrace_459914
  have hstable : (prefixWord ++ tailWord_459914).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_459914).length < 2 ^ (prefixWord ++ tailWord_459914).sum := by decide
  have hdescent : baseEnd_459914 < baseStart_459914 := by decide
  rcases family_descends (prefixWord ++ tailWord_459914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_459934 : List Nat := [4, 3, 1, 1, 2, 2, 2, 3, 2]
def baseStart_459934 : Nat := 118140960795 + 459934 * 2 ^ 59
def prefixEnd_459934 : Nat := 4983230072969 + 3 ^ 40 * 459934 * 2
def baseEnd_459934 : Nat := 209926410084541102053163

theorem tailTrace_459934 : CollatzResearch.WordTrace tailWord_459934 prefixEnd_459934 209926410084541102053163 := by
  unfold tailWord_459934
  simp only [CollatzResearch.WordTrace]
  refine ⟨2096896389468142914823357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11183447410496762212391237 2096896389468142914823357)
  ·
    refine ⟨786336146050553593058759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2096896389468142914823357 786336146050553593058759)
    ·
      refine ⟨1179504219075830389588139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 786336146050553593058759 1179504219075830389588139)
      ·
        refine ⟨1769256328613745584382209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1179504219075830389588139 1769256328613745584382209)
        ·
          refine ⟨1326942246460309188286657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1769256328613745584382209 1326942246460309188286657)
          ·
            refine ⟨995206684845231891214993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1326942246460309188286657 995206684845231891214993)
            ·
              refine ⟨746405013633923918411245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 995206684845231891214993 746405013633923918411245)
              ·
                refine ⟨279901880112721469404217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 746405013633923918411245 279901880112721469404217)
                ·
                  refine ⟨209926410084541102053163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 279901880112721469404217 209926410084541102053163)
                  ·
                    rfl

theorem cell20_459934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 2, 2, 3, 2].length) (baseStart_459934 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_459934 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_459934 prefixEnd_459934 := by exact prefixLift 459934
  have htrace : WordTrace (prefixWord ++ tailWord_459934) baseStart_459934 baseEnd_459934 := by
    simpa [prefixWord, tailWord_459934, baseEnd_459934] using wordTrace_append hprefix tailTrace_459934
  have hstable : (prefixWord ++ tailWord_459934).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_459934).length < 2 ^ (prefixWord ++ tailWord_459934).sum := by decide
  have hdescent : baseEnd_459934 < baseStart_459934 := by decide
  rcases family_descends (prefixWord ++ tailWord_459934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_459959 : List Nat := [1, 1, 3, 1, 4, 1, 4, 1, 4]
def baseStart_459959 : Nat := 118140960795 + 459959 * 2 ^ 59
def prefixEnd_459959 : Nat := 4983230072969 + 3 ^ 40 * 459959 * 2
def baseEnd_459959 : Nat := 209937820765752126219727

theorem tailTrace_459959 : CollatzResearch.WordTrace tailWord_459959 prefixEnd_459959 209937820765752126219727 := by
  unfold tailWord_459959
  simp only [CollatzResearch.WordTrace]
  refine ⟨16776082940654572588246931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11184055293769715058831287 16776082940654572588246931)
  ·
    refine ⟨25164124410981858882370397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16776082940654572588246931 25164124410981858882370397)
    ·
      refine ⟨9436546654118197080888899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25164124410981858882370397 9436546654118197080888899)
      ·
        refine ⟨14154819981177295621333349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9436546654118197080888899 14154819981177295621333349)
        ·
          refine ⟨2654028746470742929000003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14154819981177295621333349 2654028746470742929000003)
          ·
            refine ⟨3981043119706114393500005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2654028746470742929000003 3981043119706114393500005)
            ·
              refine ⟨746445584944896448781251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3981043119706114393500005 746445584944896448781251)
              ·
                refine ⟨1119668377417344673171877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 746445584944896448781251 1119668377417344673171877)
                ·
                  refine ⟨209937820765752126219727, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1119668377417344673171877 209937820765752126219727)
                  ·
                    rfl

theorem cell20_459959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 4, 1, 4].length) (baseStart_459959 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_459959 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_459959 prefixEnd_459959 := by exact prefixLift 459959
  have htrace : WordTrace (prefixWord ++ tailWord_459959) baseStart_459959 baseEnd_459959 := by
    simpa [prefixWord, tailWord_459959, baseEnd_459959] using wordTrace_append hprefix tailTrace_459959
  have hstable : (prefixWord ++ tailWord_459959).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_459959).length < 2 ^ (prefixWord ++ tailWord_459959).sum := by decide
  have hdescent : baseEnd_459959 < baseStart_459959 := by decide
  rcases family_descends (prefixWord ++ tailWord_459959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_459987 : List Nat := [1, 1, 1, 2, 1, 1, 1, 12]
def baseStart_459987 : Nat := 118140960795 + 459987 * 2 ^ 59
def prefixEnd_459987 : Nat := 4983230072969 + 3 ^ 40 * 459987 * 2
def baseEnd_459987 : Nat := 69983533576236157762093

theorem tailTrace_459987 : CollatzResearch.WordTrace tailWord_459987 prefixEnd_459987 69983533576236157762093 := by
  unfold tailWord_459987
  simp only [CollatzResearch.WordTrace]
  refine ⟨16777104184553133370266215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11184736123035422246844143 16777104184553133370266215)
  ·
    refine ⟨25165656276829700055399323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16777104184553133370266215 25165656276829700055399323)
    ·
      refine ⟨37748484415244550083098985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25165656276829700055399323 37748484415244550083098985)
      ·
        refine ⟨28311363311433412562324239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37748484415244550083098985 28311363311433412562324239)
        ·
          refine ⟨42467044967150118843486359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28311363311433412562324239 42467044967150118843486359)
          ·
            refine ⟨63700567450725178265229539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42467044967150118843486359 63700567450725178265229539)
            ·
              refine ⟨95550851176087767397844309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63700567450725178265229539 95550851176087767397844309)
              ·
                refine ⟨69983533576236157762093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 12 95550851176087767397844309 69983533576236157762093)
                ·
                  rfl

theorem cell20_459987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 12].length) (baseStart_459987 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_459987 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_459987 prefixEnd_459987 := by exact prefixLift 459987
  have htrace : WordTrace (prefixWord ++ tailWord_459987) baseStart_459987 baseEnd_459987 := by
    simpa [prefixWord, tailWord_459987, baseEnd_459987] using wordTrace_append hprefix tailTrace_459987
  have hstable : (prefixWord ++ tailWord_459987).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_459987).length < 2 ^ (prefixWord ++ tailWord_459987).sum := by decide
  have hdescent : baseEnd_459987 < baseStart_459987 := by decide
  rcases family_descends (prefixWord ++ tailWord_459987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_460011 : List Nat := [1, 1, 1, 1, 2, 6, 2, 1, 5]
def baseStart_460011 : Nat := 118140960795 + 460011 * 2 ^ 59
def prefixEnd_460011 : Nat := 4983230072969 + 3 ^ 40 * 460011 * 2
def baseEnd_460011 : Nat := 209961554982671056486181

theorem tailTrace_460011 : CollatzResearch.WordTrace tailWord_460011 prefixEnd_460011 209961554982671056486181 := by
  unfold tailWord_460011
  simp only [CollatzResearch.WordTrace]
  refine ⟨16777979536466185469139887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11185319690977456979426591 16777979536466185469139887)
  ·
    refine ⟨25166969304699278203709831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16777979536466185469139887 25166969304699278203709831)
    ·
      refine ⟨37750453957048917305564747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25166969304699278203709831 37750453957048917305564747)
      ·
        refine ⟨56625680935573375958347121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37750453957048917305564747 56625680935573375958347121)
        ·
          refine ⟨42469260701680031968760341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56625680935573375958347121 42469260701680031968760341)
          ·
            refine ⟨1990746595391251498535641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 42469260701680031968760341 1990746595391251498535641)
            ·
              refine ⟨1493059946543438623901731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1990746595391251498535641 1493059946543438623901731)
              ·
                refine ⟨2239589919815157935852597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1493059946543438623901731 2239589919815157935852597)
                ·
                  refine ⟨209961554982671056486181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2239589919815157935852597 209961554982671056486181)
                  ·
                    rfl

theorem cell20_460011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 2, 1, 5].length) (baseStart_460011 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_460011 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_460011 prefixEnd_460011 := by exact prefixLift 460011
  have htrace : WordTrace (prefixWord ++ tailWord_460011) baseStart_460011 baseEnd_460011 := by
    simpa [prefixWord, tailWord_460011, baseEnd_460011] using wordTrace_append hprefix tailTrace_460011
  have hstable : (prefixWord ++ tailWord_460011).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_460011).length < 2 ^ (prefixWord ++ tailWord_460011).sum := by decide
  have hdescent : baseEnd_460011 < baseStart_460011 := by decide
  rcases family_descends (prefixWord ++ tailWord_460011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_460014 : List Nat := [4, 1, 2, 1, 1, 1, 2, 6, 2]
def baseStart_460014 : Nat := 118140960795 + 460014 * 2 ^ 59
def prefixEnd_460014 : Nat := 4983230072969 + 3 ^ 40 * 460014 * 2
def baseEnd_460014 : Nat := 209962924264416379386169

theorem tailTrace_460014 : CollatzResearch.WordTrace tailWord_460014 prefixEnd_460014 209962924264416379386169 := by
  unfold tailWord_460014
  simp only [CollatzResearch.WordTrace]
  refine ⟨2097261119431914622687387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11185392636970211320999397 2097261119431914622687387)
  ·
    refine ⟨3145891679147871934031081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2097261119431914622687387 3145891679147871934031081)
    ·
      refine ⟨2359418759360903950523311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3145891679147871934031081 2359418759360903950523311)
      ·
        refine ⟨3539128139041355925784967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2359418759360903950523311 3539128139041355925784967)
        ·
          refine ⟨5308692208562033888677451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3539128139041355925784967 5308692208562033888677451)
          ·
            refine ⟨7963038312843050833016177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5308692208562033888677451 7963038312843050833016177)
            ·
              refine ⟨5972278734632288124762133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7963038312843050833016177 5972278734632288124762133)
              ·
                refine ⟨279950565685888505848225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 5972278734632288124762133 279950565685888505848225)
                ·
                  refine ⟨209962924264416379386169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 279950565685888505848225 209962924264416379386169)
                  ·
                    rfl

theorem cell20_460014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 2, 6, 2].length) (baseStart_460014 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_460014 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_460014 prefixEnd_460014 := by exact prefixLift 460014
  have htrace : WordTrace (prefixWord ++ tailWord_460014) baseStart_460014 baseEnd_460014 := by
    simpa [prefixWord, tailWord_460014, baseEnd_460014] using wordTrace_append hprefix tailTrace_460014
  have hstable : (prefixWord ++ tailWord_460014).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_460014).length < 2 ^ (prefixWord ++ tailWord_460014).sum := by decide
  have hdescent : baseEnd_460014 < baseStart_460014 := by decide
  rcases family_descends (prefixWord ++ tailWord_460014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_460063 : List Nat := [1, 1, 2, 4, 12]
def baseStart_460063 : Nat := 118140960795 + 460063 * 2 ^ 59
def prefixEnd_460063 : Nat := 4983230072969 + 3 ^ 40 * 460063 * 2
def baseEnd_460063 : Nat := 2592410977772715885835

theorem tailTrace_460063 : CollatzResearch.WordTrace tailWord_460063 prefixEnd_460063 2592410977772715885835 := by
  unfold tailWord_460063
  simp only [CollatzResearch.WordTrace]
  refine ⟨16779876132277798350032843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11186584088185198900021895 16779876132277798350032843)
  ·
    refine ⟨25169814198416697525049265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16779876132277798350032843 25169814198416697525049265)
    ·
      refine ⟨18877360648812523143786949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25169814198416697525049265 18877360648812523143786949)
      ·
        refine ⟨3539505121652348089460053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18877360648812523143786949 3539505121652348089460053)
        ·
          refine ⟨2592410977772715885835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 12 3539505121652348089460053 2592410977772715885835)
          ·
            rfl

theorem cell20_460063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 12].length) (baseStart_460063 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_460063 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_460063 prefixEnd_460063 := by exact prefixLift 460063
  have htrace : WordTrace (prefixWord ++ tailWord_460063) baseStart_460063 baseEnd_460063 := by
    simpa [prefixWord, tailWord_460063, baseEnd_460063] using wordTrace_append hprefix tailTrace_460063
  have hstable : (prefixWord ++ tailWord_460063).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_460063).length < 2 ^ (prefixWord ++ tailWord_460063).sum := by decide
  have hdescent : baseEnd_460063 < baseStart_460063 := by decide
  rcases family_descends (prefixWord ++ tailWord_460063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_460069 : List Nat := [1, 3, 1, 2, 4, 1, 4, 2, 2]
def baseStart_460069 : Nat := 118140960795 + 460069 * 2 ^ 59
def prefixEnd_460069 : Nat := 4983230072969 + 3 ^ 40 * 460069 * 2
def baseEnd_460069 : Nat := 209988027763080632552611

theorem tailTrace_460069 : CollatzResearch.WordTrace tailWord_460069 prefixEnd_460069 209988027763080632552611 := by
  unfold tailWord_460069
  simp only [CollatzResearch.WordTrace]
  refine ⟨16780094970256061374751261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11186729980170707583167507 16780094970256061374751261)
  ·
    refine ⟨6292535613846023015531723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16780094970256061374751261 6292535613846023015531723)
    ·
      refine ⟨9438803420769034523297585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6292535613846023015531723 9438803420769034523297585)
      ·
        refine ⟨7079102565576775892473189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9438803420769034523297585 7079102565576775892473189)
        ·
          refine ⟨1327331731045645479838723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7079102565576775892473189 1327331731045645479838723)
          ·
            refine ⟨1990997596568468219758085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1327331731045645479838723 1990997596568468219758085)
            ·
              refine ⟨373312049356587791204641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1990997596568468219758085 373312049356587791204641)
              ·
                refine ⟨279984037017440843403481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 373312049356587791204641 279984037017440843403481)
                ·
                  refine ⟨209988027763080632552611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 279984037017440843403481 209988027763080632552611)
                  ·
                    rfl

theorem cell20_460069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 4, 2, 2].length) (baseStart_460069 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_460069 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_460069 prefixEnd_460069 := by exact prefixLift 460069
  have htrace : WordTrace (prefixWord ++ tailWord_460069) baseStart_460069 baseEnd_460069 := by
    simpa [prefixWord, tailWord_460069, baseEnd_460069] using wordTrace_append hprefix tailTrace_460069
  have hstable : (prefixWord ++ tailWord_460069).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_460069).length < 2 ^ (prefixWord ++ tailWord_460069).sum := by decide
  have hdescent : baseEnd_460069 < baseStart_460069 := by decide
  rcases family_descends (prefixWord ++ tailWord_460069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_460101 : List Nat := [1, 3, 1, 1, 1, 2, 1, 10]
def baseStart_460101 : Nat := 118140960795 + 460101 * 2 ^ 59
def prefixEnd_460101 : Nat := 4983230072969 + 3 ^ 40 * 460101 * 2
def baseEnd_460101 : Nat := 70000877811676914495271

theorem tailTrace_460101 : CollatzResearch.WordTrace tailWord_460101 prefixEnd_460101 70000877811676914495271 := by
  unfold tailWord_460101
  simp only [CollatzResearch.WordTrace]
  refine ⟨16781262106140130839916157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11187508070760087226610771 16781262106140130839916157)
  ·
    refine ⟨6292973289802549064968559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16781262106140130839916157 6292973289802549064968559)
    ·
      refine ⟨9439459934703823597452839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6292973289802549064968559 9439459934703823597452839)
      ·
        refine ⟨14159189902055735396179259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9439459934703823597452839 14159189902055735396179259)
        ·
          refine ⟨21238784853083603094268889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14159189902055735396179259 21238784853083603094268889)
          ·
            refine ⟨15929088639812702320701667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21238784853083603094268889 15929088639812702320701667)
            ·
              refine ⟨23893632959719053481052501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15929088639812702320701667 23893632959719053481052501)
              ·
                refine ⟨70000877811676914495271, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 23893632959719053481052501 70000877811676914495271)
                ·
                  rfl

theorem cell20_460101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 10].length) (baseStart_460101 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_460101 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_460101 prefixEnd_460101 := by exact prefixLift 460101
  have htrace : WordTrace (prefixWord ++ tailWord_460101) baseStart_460101 baseEnd_460101 := by
    simpa [prefixWord, tailWord_460101, baseEnd_460101] using wordTrace_append hprefix tailTrace_460101
  have hstable : (prefixWord ++ tailWord_460101).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_460101).length < 2 ^ (prefixWord ++ tailWord_460101).sum := by decide
  have hdescent : baseEnd_460101 < baseStart_460101 := by decide
  rcases family_descends (prefixWord ++ tailWord_460101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_460128 : List Nat := [2, 1, 1, 3, 4, 1, 2, 4, 2]
def baseStart_460128 : Nat := 118140960795 + 460128 * 2 ^ 59
def prefixEnd_460128 : Nat := 4983230072969 + 3 ^ 40 * 460128 * 2
def baseEnd_460128 : Nat := 210014956970738649585703

theorem tailTrace_460128 : CollatzResearch.WordTrace tailWord_460128 prefixEnd_460128 210014956970738649585703 := by
  unfold tailWord_460128
  simp only [CollatzResearch.WordTrace]
  refine ⟨8391123438521157225574519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11188164584694876300766025 8391123438521157225574519)
  ·
    refine ⟨12586685157781735838361779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8391123438521157225574519 12586685157781735838361779)
    ·
      refine ⟨18880027736672603757542669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12586685157781735838361779 18880027736672603757542669)
      ·
        refine ⟨7080010401252226409078501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18880027736672603757542669 7080010401252226409078501)
        ·
          refine ⟨1327501950234792451702219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7080010401252226409078501 1327501950234792451702219)
          ·
            refine ⟨1991252925352188677553329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1327501950234792451702219 1991252925352188677553329)
            ·
              refine ⟨1493439694014141508164997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1991252925352188677553329 1493439694014141508164997)
              ·
                refine ⟨280019942627651532780937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1493439694014141508164997 280019942627651532780937)
                ·
                  refine ⟨210014956970738649585703, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 280019942627651532780937 210014956970738649585703)
                  ·
                    rfl

theorem cell20_460128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 2, 4, 2].length) (baseStart_460128 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_460128 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_460128 prefixEnd_460128 := by exact prefixLift 460128
  have htrace : WordTrace (prefixWord ++ tailWord_460128) baseStart_460128 baseEnd_460128 := by
    simpa [prefixWord, tailWord_460128, baseEnd_460128] using wordTrace_append hprefix tailTrace_460128
  have hstable : (prefixWord ++ tailWord_460128).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_460128).length < 2 ^ (prefixWord ++ tailWord_460128).sum := by decide
  have hdescent : baseEnd_460128 < baseStart_460128 := by decide
  rcases family_descends (prefixWord ++ tailWord_460128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_460138 : List Nat := [3, 1, 3, 3, 2, 1, 3, 1, 3]
def baseStart_460138 : Nat := 118140960795 + 460138 * 2 ^ 59
def prefixEnd_460138 : Nat := 4983230072969 + 3 ^ 40 * 460138 * 2
def baseEnd_460138 : Nat := 210019521243223059252329

theorem tailTrace_460138 : CollatzResearch.WordTrace tailWord_460138 prefixEnd_460138 210019521243223059252329 := by
  unfold tailWord_460138
  simp only [CollatzResearch.WordTrace]
  refine ⟨4195652901751521539753267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11188407738004057439342045 4195652901751521539753267)
  ·
    refine ⟨6293479352627282309629901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4195652901751521539753267 6293479352627282309629901)
    ·
      refine ⟨2360054757235230866111213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6293479352627282309629901 2360054757235230866111213)
      ·
        refine ⟨885020533963211574791705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2360054757235230866111213 885020533963211574791705)
        ·
          refine ⟨663765400472408681093779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 885020533963211574791705 663765400472408681093779)
          ·
            refine ⟨995648100708613021640669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 663765400472408681093779 995648100708613021640669)
            ·
              refine ⟨373368037765729883115251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 995648100708613021640669 373368037765729883115251)
              ·
                refine ⟨560052056648594824672877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 373368037765729883115251 560052056648594824672877)
                ·
                  refine ⟨210019521243223059252329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 560052056648594824672877 210019521243223059252329)
                  ·
                    rfl

theorem cell20_460138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 1, 3, 1, 3].length) (baseStart_460138 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_460138 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_460138 prefixEnd_460138 := by exact prefixLift 460138
  have htrace : WordTrace (prefixWord ++ tailWord_460138) baseStart_460138 baseEnd_460138 := by
    simpa [prefixWord, tailWord_460138, baseEnd_460138] using wordTrace_append hprefix tailTrace_460138
  have hstable : (prefixWord ++ tailWord_460138).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_460138).length < 2 ^ (prefixWord ++ tailWord_460138).sum := by decide
  have hdescent : baseEnd_460138 < baseStart_460138 := by decide
  rcases family_descends (prefixWord ++ tailWord_460138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_460158 : List Nat := [4, 2, 3, 2, 2, 1, 1, 3, 2]
def baseStart_460158 : Nat := 118140960795 + 460158 * 2 ^ 59
def prefixEnd_460158 : Nat := 4983230072969 + 3 ^ 40 * 460158 * 2
def baseEnd_460158 : Nat := 210028649788191878585581

theorem tailTrace_460158 : CollatzResearch.WordTrace tailWord_460158 prefixEnd_460158 210028649788191878585581 := by
  unfold tailWord_460158
  simp only [CollatzResearch.WordTrace]
  refine ⟨2097917633366703696842641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11188894044622419716494085 2097917633366703696842641)
  ·
    refine ⟨1573438225025027772631981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2097917633366703696842641 1573438225025027772631981)
    ·
      refine ⟨590039334384385414736993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1573438225025027772631981 590039334384385414736993)
      ·
        refine ⟨442529500788289061052745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 590039334384385414736993 442529500788289061052745)
        ·
          refine ⟨331897125591216795789559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 442529500788289061052745 331897125591216795789559)
          ·
            refine ⟨497845688386825193684339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 331897125591216795789559 497845688386825193684339)
            ·
              refine ⟨746768532580237790526509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 497845688386825193684339 746768532580237790526509)
              ·
                refine ⟨280038199717589171447441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 746768532580237790526509 280038199717589171447441)
                ·
                  refine ⟨210028649788191878585581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 280038199717589171447441 210028649788191878585581)
                  ·
                    rfl

theorem cell20_460158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 2, 1, 1, 3, 2].length) (baseStart_460158 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_460158 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_460158 prefixEnd_460158 := by exact prefixLift 460158
  have htrace : WordTrace (prefixWord ++ tailWord_460158) baseStart_460158 baseEnd_460158 := by
    simpa [prefixWord, tailWord_460158, baseEnd_460158] using wordTrace_append hprefix tailTrace_460158
  have hstable : (prefixWord ++ tailWord_460158).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_460158).length < 2 ^ (prefixWord ++ tailWord_460158).sum := by decide
  have hdescent : baseEnd_460158 < baseStart_460158 := by decide
  rcases family_descends (prefixWord ++ tailWord_460158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_460162 : List Nat := [3, 4, 2, 1, 1, 1, 3, 3, 2]
def baseStart_460162 : Nat := 118140960795 + 460162 * 2 ^ 59
def prefixEnd_460162 : Nat := 4983230072969 + 3 ^ 40 * 460162 * 2
def baseEnd_460162 : Nat := 210030475497185642452231

theorem tailTrace_460162 : CollatzResearch.WordTrace tailWord_460162 prefixEnd_460162 210030475497185642452231 := by
  unfold tailWord_460162
  simp only [CollatzResearch.WordTrace]
  refine ⟨4195871739729784564471685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11188991305946092171924493 4195871739729784564471685)
  ·
    refine ⟨786725951199334605838441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4195871739729784564471685 786725951199334605838441)
    ·
      refine ⟨590044463399500954378831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 786725951199334605838441 590044463399500954378831)
      ·
        refine ⟨885066695099251431568247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 590044463399500954378831 885066695099251431568247)
        ·
          refine ⟨1327600042648877147352371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 885066695099251431568247 1327600042648877147352371)
          ·
            refine ⟨1991400063973315721028557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1327600042648877147352371 1991400063973315721028557)
            ·
              refine ⟨746775023989993395385709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1991400063973315721028557 746775023989993395385709)
              ·
                refine ⟨280040633996247523269641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 746775023989993395385709 280040633996247523269641)
                ·
                  refine ⟨210030475497185642452231, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 280040633996247523269641 210030475497185642452231)
                  ·
                    rfl

theorem cell20_460162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 3, 3, 2].length) (baseStart_460162 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_460162 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_460162 prefixEnd_460162 := by exact prefixLift 460162
  have htrace : WordTrace (prefixWord ++ tailWord_460162) baseStart_460162 baseEnd_460162 := by
    simpa [prefixWord, tailWord_460162, baseEnd_460162] using wordTrace_append hprefix tailTrace_460162
  have hstable : (prefixWord ++ tailWord_460162).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_460162).length < 2 ^ (prefixWord ++ tailWord_460162).sum := by decide
  have hdescent : baseEnd_460162 < baseStart_460162 := by decide
  rcases family_descends (prefixWord ++ tailWord_460162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_460163 : List Nat := [1, 1, 1, 3, 5, 1, 1, 2, 5]
def baseStart_460163 : Nat := 118140960795 + 460163 * 2 ^ 59
def prefixEnd_460163 : Nat := 4983230072969 + 3 ^ 40 * 460163 * 2
def baseEnd_460163 : Nat := 210030931924434083418893

theorem tailTrace_460163 : CollatzResearch.WordTrace tailWord_460163 prefixEnd_460163 210030931924434083418893 := by
  unfold tailWord_460163
  simp only [CollatzResearch.WordTrace]
  refine ⟨16783523431915515428673143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11189015621277010285782095 16783523431915515428673143)
  ·
    refine ⟨25175285147873273143009715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16783523431915515428673143 25175285147873273143009715)
    ·
      refine ⟨37762927721809909714514573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25175285147873273143009715 37762927721809909714514573)
      ·
        refine ⟨14161097895678716142942965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37762927721809909714514573 14161097895678716142942965)
        ·
          refine ⟨1327602927719879638400903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 14161097895678716142942965 1327602927719879638400903)
          ·
            refine ⟨1991404391579819457601355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1327602927719879638400903 1991404391579819457601355)
            ·
              refine ⟨2987106587369729186402033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1991404391579819457601355 2987106587369729186402033)
              ·
                refine ⟨2240329940527296889801525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2987106587369729186402033 2240329940527296889801525)
                ·
                  refine ⟨210030931924434083418893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2240329940527296889801525 210030931924434083418893)
                  ·
                    rfl

theorem cell20_460163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 1, 2, 5].length) (baseStart_460163 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_460163 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_460163 prefixEnd_460163 := by exact prefixLift 460163
  have htrace : WordTrace (prefixWord ++ tailWord_460163) baseStart_460163 baseEnd_460163 := by
    simpa [prefixWord, tailWord_460163, baseEnd_460163] using wordTrace_append hprefix tailTrace_460163
  have hstable : (prefixWord ++ tailWord_460163).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_460163).length < 2 ^ (prefixWord ++ tailWord_460163).sum := by decide
  have hdescent : baseEnd_460163 < baseStart_460163 := by decide
  rcases family_descends (prefixWord ++ tailWord_460163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_460180 : List Nat := [2, 4, 2, 1, 2, 1, 2, 1, 5]
def baseStart_460180 : Nat := 118140960795 + 460180 * 2 ^ 59
def prefixEnd_460180 : Nat := 4983230072969 + 3 ^ 40 * 460180 * 2
def baseEnd_460180 : Nat := 210038691187657579852157

theorem tailTrace_460180 : CollatzResearch.WordTrace tailWord_460180 prefixEnd_460180 210038691187657579852157 := by
  unfold tailWord_460180
  simp only [CollatzResearch.WordTrace]
  refine ⟨8392071736426963666020997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11189428981902618221361329 8392071736426963666020997)
  ·
    refine ⟨1573513450580055687378937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8392071736426963666020997 1573513450580055687378937)
    ·
      refine ⟨1180135087935041765534203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1573513450580055687378937 1180135087935041765534203)
      ·
        refine ⟨1770202631902562648301305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1180135087935041765534203 1770202631902562648301305)
        ·
          refine ⟨1327651973926921986225979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1770202631902562648301305 1327651973926921986225979)
          ·
            refine ⟨1991477960890382979338969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1327651973926921986225979 1991477960890382979338969)
            ·
              refine ⟨1493608470667787234504227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1991477960890382979338969 1493608470667787234504227)
              ·
                refine ⟨2240412706001680851756341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1493608470667787234504227 2240412706001680851756341)
                ·
                  refine ⟨210038691187657579852157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2240412706001680851756341 210038691187657579852157)
                  ·
                    rfl

theorem cell20_460180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 2, 1, 5].length) (baseStart_460180 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_460180 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_460180 prefixEnd_460180 := by exact prefixLift 460180
  have htrace : WordTrace (prefixWord ++ tailWord_460180) baseStart_460180 baseEnd_460180 := by
    simpa [prefixWord, tailWord_460180, baseEnd_460180] using wordTrace_append hprefix tailTrace_460180
  have hstable : (prefixWord ++ tailWord_460180).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_460180).length < 2 ^ (prefixWord ++ tailWord_460180).sum := by decide
  have hdescent : baseEnd_460180 < baseStart_460180 := by decide
  rcases family_descends (prefixWord ++ tailWord_460180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_460190 : List Nat := [4, 3, 1, 2, 2, 1, 2, 5]
def baseStart_460190 : Nat := 118140960795 + 460190 * 2 ^ 59
def prefixEnd_460190 : Nat := 4983230072969 + 3 ^ 40 * 460190 * 2
def baseEnd_460190 : Nat := 70014418486713996506261

theorem tailTrace_460190 : CollatzResearch.WordTrace tailWord_460190 prefixEnd_460190 70014418486713996506261 := by
  unfold tailWord_460190
  simp only [CollatzResearch.WordTrace]
  refine ⟨2098063525352212379988253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11189672135211799359937349 2098063525352212379988253)
  ·
    refine ⟨786773822007079642495595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2098063525352212379988253 786773822007079642495595)
    ·
      refine ⟨1180160733010619463743393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 786773822007079642495595 1180160733010619463743393)
      ·
        refine ⟨885120549757964597807545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1180160733010619463743393 885120549757964597807545)
        ·
          refine ⟨663840412318473448355659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 885120549757964597807545 663840412318473448355659)
          ·
            refine ⟨995760618477710172533489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 663840412318473448355659 995760618477710172533489)
            ·
              refine ⟨746820463858282629400117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 995760618477710172533489 746820463858282629400117)
              ·
                refine ⟨70014418486713996506261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 746820463858282629400117 70014418486713996506261)
                ·
                  rfl

theorem cell20_460190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 1, 2, 5].length) (baseStart_460190 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_460190 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_460190 prefixEnd_460190 := by exact prefixLift 460190
  have htrace : WordTrace (prefixWord ++ tailWord_460190) baseStart_460190 baseEnd_460190 := by
    simpa [prefixWord, tailWord_460190, baseEnd_460190] using wordTrace_append hprefix tailTrace_460190
  have hstable : (prefixWord ++ tailWord_460190).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_460190).length < 2 ^ (prefixWord ++ tailWord_460190).sum := by decide
  have hdescent : baseEnd_460190 < baseStart_460190 := by decide
  rcases family_descends (prefixWord ++ tailWord_460190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_460194 : List Nat := [3, 3, 1, 2, 1, 2, 1, 7]
def baseStart_460194 : Nat := 118140960795 + 460194 * 2 ^ 59
def prefixEnd_460194 : Nat := 4983230072969 + 3 ^ 40 * 460194 * 2
def baseEnd_460194 : Nat := 70015027056378584461811

theorem tailTrace_460194 : CollatzResearch.WordTrace tailWord_460194 prefixEnd_460194 70015027056378584461811 := by
  unfold tailWord_460194
  simp only [CollatzResearch.WordTrace]
  refine ⟨4196163523700801930762909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11189769396535471815367757 4196163523700801930762909)
  ·
    refine ⟨1573561321387800724036091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4196163523700801930762909 1573561321387800724036091)
    ·
      refine ⟨2360341982081701086054137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1573561321387800724036091 2360341982081701086054137)
      ·
        refine ⟨1770256486561275814540603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2360341982081701086054137 1770256486561275814540603)
        ·
          refine ⟨2655384729841913721810905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1770256486561275814540603 2655384729841913721810905)
          ·
            refine ⟨1991538547381435291358179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2655384729841913721810905 1991538547381435291358179)
            ·
              refine ⟨2987307821072152937037269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1991538547381435291358179 2987307821072152937037269)
              ·
                refine ⟨70015027056378584461811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2987307821072152937037269 70015027056378584461811)
                ·
                  rfl

theorem cell20_460194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 1, 7].length) (baseStart_460194 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_460194 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_460194 prefixEnd_460194 := by exact prefixLift 460194
  have htrace : WordTrace (prefixWord ++ tailWord_460194) baseStart_460194 baseEnd_460194 := by
    simpa [prefixWord, tailWord_460194, baseEnd_460194] using wordTrace_append hprefix tailTrace_460194
  have hstable : (prefixWord ++ tailWord_460194).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_460194).length < 2 ^ (prefixWord ++ tailWord_460194).sum := by decide
  have hdescent : baseEnd_460194 < baseStart_460194 := by decide
  rcases family_descends (prefixWord ++ tailWord_460194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_460215 : List Nat := [1, 1, 3, 1, 3, 2, 1, 8]
def baseStart_460215 : Nat := 118140960795 + 460215 * 2 ^ 59
def prefixEnd_460215 : Nat := 4983230072969 + 3 ^ 40 * 460215 * 2
def baseEnd_460215 : Nat := 70018222047117671228449

theorem tailTrace_460215 : CollatzResearch.WordTrace tailWord_460215 prefixEnd_460215 70018222047117671228449 := by
  unfold tailWord_460215
  simp only [CollatzResearch.WordTrace]
  refine ⟨16785420027727128309566099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11190280018484752206377399 16785420027727128309566099)
  ·
    refine ⟨25178130041590692464349149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16785420027727128309566099 25178130041590692464349149)
    ·
      refine ⟨9441798765596509674130931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25178130041590692464349149 9441798765596509674130931)
      ·
        refine ⟨14162698148394764511196397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9441798765596509674130931 14162698148394764511196397)
        ·
          refine ⟨5311011805648036691698649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14162698148394764511196397 5311011805648036691698649)
          ·
            refine ⟨3983258854236027518773987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5311011805648036691698649 3983258854236027518773987)
            ·
              refine ⟨5974888281354041278160981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3983258854236027518773987 5974888281354041278160981)
              ·
                refine ⟨70018222047117671228449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5974888281354041278160981 70018222047117671228449)
                ·
                  rfl

theorem cell20_460215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 1, 8].length) (baseStart_460215 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_460215 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_460215 prefixEnd_460215 := by exact prefixLift 460215
  have htrace : WordTrace (prefixWord ++ tailWord_460215) baseStart_460215 baseEnd_460215 := by
    simpa [prefixWord, tailWord_460215, baseEnd_460215] using wordTrace_append hprefix tailTrace_460215
  have hstable : (prefixWord ++ tailWord_460215).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_460215).length < 2 ^ (prefixWord ++ tailWord_460215).sum := by decide
  have hdescent : baseEnd_460215 < baseStart_460215 := by decide
  rcases family_descends (prefixWord ++ tailWord_460215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_460239 : List Nat := [1, 1, 2, 1, 1, 4, 3, 4, 3]
def baseStart_460239 : Nat := 118140960795 + 460239 * 2 ^ 59
def prefixEnd_460239 : Nat := 4983230072969 + 3 ^ 40 * 460239 * 2
def baseEnd_460239 : Nat := 210065620395315596885249

theorem tailTrace_460239 : CollatzResearch.WordTrace tailWord_460239 prefixEnd_460239 210065620395315596885249 := by
  unfold tailWord_460239
  simp only [CollatzResearch.WordTrace]
  refine ⟨16786295379640180408439771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11190863586426786938959847 16786295379640180408439771)
  ·
    refine ⟨25179443069460270612659657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16786295379640180408439771 25179443069460270612659657)
    ·
      refine ⟨18884582302095202959494743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25179443069460270612659657 18884582302095202959494743)
      ·
        refine ⟨28326873453142804439242115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18884582302095202959494743 28326873453142804439242115)
        ·
          refine ⟨42490310179714206658863173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28326873453142804439242115 42490310179714206658863173)
          ·
            refine ⟨7966933158696413748536845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 42490310179714206658863173 7966933158696413748536845)
            ·
              refine ⟨2987599934511155155701317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7966933158696413748536845 2987599934511155155701317)
              ·
                refine ⟨560174987720841591693997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2987599934511155155701317 560174987720841591693997)
                ·
                  refine ⟨210065620395315596885249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 560174987720841591693997 210065620395315596885249)
                  ·
                    rfl

theorem cell20_460239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 3, 4, 3].length) (baseStart_460239 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_460239 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_460239 prefixEnd_460239 := by exact prefixLift 460239
  have htrace : WordTrace (prefixWord ++ tailWord_460239) baseStart_460239 baseEnd_460239 := by
    simpa [prefixWord, tailWord_460239, baseEnd_460239] using wordTrace_append hprefix tailTrace_460239
  have hstable : (prefixWord ++ tailWord_460239).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_460239).length < 2 ^ (prefixWord ++ tailWord_460239).sum := by decide
  have hdescent : baseEnd_460239 < baseStart_460239 := by decide
  rcases family_descends (prefixWord ++ tailWord_460239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_460263 : List Nat := [1, 1, 5, 2, 1, 3, 1, 2, 4]
def baseStart_460263 : Nat := 118140960795 + 460263 * 2 ^ 59
def prefixEnd_460263 : Nat := 4983230072969 + 3 ^ 40 * 460263 * 2
def baseEnd_460263 : Nat := 210076574649278180085151

theorem tailTrace_460263 : CollatzResearch.WordTrace tailWord_460263 prefixEnd_460263 210076574649278180085151 := by
  unfold tailWord_460263
  simp only [CollatzResearch.WordTrace]
  refine ⟨16787170731553232507313443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11191447154368821671542295 16787170731553232507313443)
  ·
    refine ⟨25180756097329848760970165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16787170731553232507313443 25180756097329848760970165)
    ·
      refine ⟨2360695884124673321340953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 25180756097329848760970165 2360695884124673321340953)
      ·
        refine ⟨1770521913093504991005715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2360695884124673321340953 1770521913093504991005715)
        ·
          refine ⟨2655782869640257486508573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1770521913093504991005715 2655782869640257486508573)
          ·
            refine ⟨995918576115096557440715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2655782869640257486508573 995918576115096557440715)
            ·
              refine ⟨1493877864172644836161073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 995918576115096557440715 1493877864172644836161073)
              ·
                refine ⟨1120408398129483627120805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1493877864172644836161073 1120408398129483627120805)
                ·
                  refine ⟨210076574649278180085151, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1120408398129483627120805 210076574649278180085151)
                  ·
                    rfl

theorem cell20_460263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 3, 1, 2, 4].length) (baseStart_460263 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_460263 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_460263 prefixEnd_460263 := by exact prefixLift 460263
  have htrace : WordTrace (prefixWord ++ tailWord_460263) baseStart_460263 baseEnd_460263 := by
    simpa [prefixWord, tailWord_460263, baseEnd_460263] using wordTrace_append hprefix tailTrace_460263
  have hstable : (prefixWord ++ tailWord_460263).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_460263).length < 2 ^ (prefixWord ++ tailWord_460263).sum := by decide
  have hdescent : baseEnd_460263 < baseStart_460263 := by decide
  rcases family_descends (prefixWord ++ tailWord_460263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_460280 : List Nat := [2, 1, 2, 1, 1, 6, 2, 3, 2]
def baseStart_460280 : Nat := 118140960795 + 460280 * 2 ^ 59
def prefixEnd_460280 : Nat := 4983230072969 + 3 ^ 40 * 460280 * 2
def baseEnd_460280 : Nat := 210084333912501676518415

theorem tailTrace_460280 : CollatzResearch.WordTrace tailWord_460280 prefixEnd_460280 210084333912501676518415 := by
  unfold tailWord_460280
  simp only [CollatzResearch.WordTrace]
  refine ⟨8393895386245822205341147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11191860514994429607121529 8393895386245822205341147)
  ·
    refine ⟨12590843079368733308011721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8393895386245822205341147 12590843079368733308011721)
    ·
      refine ⟨9443132309526549981008791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12590843079368733308011721 9443132309526549981008791)
      ·
        refine ⟨14164698464289824971513187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9443132309526549981008791 14164698464289824971513187)
        ·
          refine ⟨21247047696434737457269781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14164698464289824971513187 21247047696434737457269781)
          ·
            refine ⟨995955360770378318309521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 21247047696434737457269781 995955360770378318309521)
            ·
              refine ⟨746966520577783738732141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 995955360770378318309521 746966520577783738732141)
              ·
                refine ⟨280112445216668902024553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 746966520577783738732141 280112445216668902024553)
                ·
                  refine ⟨210084333912501676518415, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 280112445216668902024553 210084333912501676518415)
                  ·
                    rfl

theorem cell20_460280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 6, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 6, 2, 3, 2].length) (baseStart_460280 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_460280 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_460280 prefixEnd_460280 := by exact prefixLift 460280
  have htrace : WordTrace (prefixWord ++ tailWord_460280) baseStart_460280 baseEnd_460280 := by
    simpa [prefixWord, tailWord_460280, baseEnd_460280] using wordTrace_append hprefix tailTrace_460280
  have hstable : (prefixWord ++ tailWord_460280).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_460280).length < 2 ^ (prefixWord ++ tailWord_460280).sum := by decide
  have hdescent : baseEnd_460280 < baseStart_460280 := by decide
  rcases family_descends (prefixWord ++ tailWord_460280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_460290 : List Nat := [3, 4, 1, 2, 1, 3, 1, 2, 3]
def baseStart_460290 : Nat := 118140960795 + 460290 * 2 ^ 59
def prefixEnd_460290 : Nat := 4983230072969 + 3 ^ 40 * 460290 * 2
def baseEnd_460290 : Nat := 210088898184986086185041

theorem tailTrace_460290 : CollatzResearch.WordTrace tailWord_460290 prefixEnd_460290 210088898184986086185041 := by
  unfold tailWord_460290
  simp only [CollatzResearch.WordTrace]
  refine ⟨4197038875613854029636581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11192103668303610745697549 4197038875613854029636581)
  ·
    refine ⟨786944789177597630556859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4197038875613854029636581 786944789177597630556859)
    ·
      refine ⟨1180417183766396445835289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 786944789177597630556859 1180417183766396445835289)
      ·
        refine ⟨885312887824797334376467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1180417183766396445835289 885312887824797334376467)
        ·
          refine ⟨1327969331737196001564701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 885312887824797334376467 1327969331737196001564701)
          ·
            refine ⟨497988499401448500586763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1327969331737196001564701 497988499401448500586763)
            ·
              refine ⟨746982749102172750880145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 497988499401448500586763 746982749102172750880145)
              ·
                refine ⟨560237061826629563160109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 746982749102172750880145 560237061826629563160109)
                ·
                  refine ⟨210088898184986086185041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 560237061826629563160109 210088898184986086185041)
                  ·
                    rfl

theorem cell20_460290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 3, 1, 2, 3].length) (baseStart_460290 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_460290 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_460290 prefixEnd_460290 := by exact prefixLift 460290
  have htrace : WordTrace (prefixWord ++ tailWord_460290) baseStart_460290 baseEnd_460290 := by
    simpa [prefixWord, tailWord_460290, baseEnd_460290] using wordTrace_append hprefix tailTrace_460290
  have hstable : (prefixWord ++ tailWord_460290).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_460290).length < 2 ^ (prefixWord ++ tailWord_460290).sum := by decide
  have hdescent : baseEnd_460290 < baseStart_460290 := by decide
  rcases family_descends (prefixWord ++ tailWord_460290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_460342 : List Nat := [5, 1, 2, 1, 4, 1, 6]
def baseStart_460342 : Nat := 118140960795 + 460342 * 2 ^ 59
def prefixEnd_460342 : Nat := 4983230072969 + 3 ^ 40 * 460342 * 2
def baseEnd_460342 : Nat := 23345848044656112939055

theorem tailTrace_460342 : CollatzResearch.WordTrace tailWord_460342 prefixEnd_460342 23345848044656112939055 := by
  unfold tailWord_460342
  simp only [CollatzResearch.WordTrace]
  refine ⟨1049378256141689312464955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 11193368065511352666292853 1049378256141689312464955)
  ·
    refine ⟨1574067384212533968697433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1049378256141689312464955 1574067384212533968697433)
    ·
      refine ⟨1180550538159400476523075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1574067384212533968697433 1180550538159400476523075)
      ·
        refine ⟨1770825807239100714784613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1180550538159400476523075 1770825807239100714784613)
        ·
          refine ⟨332029838857331384022115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1770825807239100714784613 332029838857331384022115)
          ·
            refine ⟨498044758285997076033173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 332029838857331384022115 498044758285997076033173)
            ·
              refine ⟨23345848044656112939055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 498044758285997076033173 23345848044656112939055)
              ·
                rfl

theorem cell20_460342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 4, 1, 6].length) (baseStart_460342 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_460342 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_460342 prefixEnd_460342 := by exact prefixLift 460342
  have htrace : WordTrace (prefixWord ++ tailWord_460342) baseStart_460342 baseEnd_460342 := by
    simpa [prefixWord, tailWord_460342, baseEnd_460342] using wordTrace_append hprefix tailTrace_460342
  have hstable : (prefixWord ++ tailWord_460342).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_460342).length < 2 ^ (prefixWord ++ tailWord_460342).sum := by decide
  have hdescent : baseEnd_460342 < baseStart_460342 := by decide
  rcases family_descends (prefixWord ++ tailWord_460342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_460353 : List Nat := [1, 2, 5, 1, 1, 1, 1, 3, 5]
def baseStart_460353 : Nat := 118140960795 + 460353 * 2 ^ 59
def prefixEnd_460353 : Nat := 4983230072969 + 3 ^ 40 * 460353 * 2
def baseEnd_460353 : Nat := 210117653101637867084783

theorem tailTrace_460353 : CollatzResearch.WordTrace tailWord_460353 prefixEnd_460353 210117653101637867084783 := by
  unfold tailWord_460353
  simp only [CollatzResearch.WordTrace]
  refine ⟨16790453301227177878089713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11193635534151451918726475 16790453301227177878089713)
  ·
    refine ⟨12592839975920383408567285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16790453301227177878089713 12592839975920383408567285)
    ·
      refine ⟨1180578747742535944553183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 12592839975920383408567285 1180578747742535944553183)
      ·
        refine ⟨1770868121613803916829775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1180578747742535944553183 1770868121613803916829775)
        ·
          refine ⟨2656302182420705875244663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1770868121613803916829775 2656302182420705875244663)
          ·
            refine ⟨3984453273631058812866995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2656302182420705875244663 3984453273631058812866995)
            ·
              refine ⟨5976679910446588219300493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3984453273631058812866995 5976679910446588219300493)
              ·
                refine ⟨2241254966417470582237685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5976679910446588219300493 2241254966417470582237685)
                ·
                  refine ⟨210117653101637867084783, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2241254966417470582237685 210117653101637867084783)
                  ·
                    rfl

theorem cell20_460353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 1, 3, 5].length) (baseStart_460353 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_460353 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_460353 prefixEnd_460353 := by exact prefixLift 460353
  have htrace : WordTrace (prefixWord ++ tailWord_460353) baseStart_460353 baseEnd_460353 := by
    simpa [prefixWord, tailWord_460353, baseEnd_460353] using wordTrace_append hprefix tailTrace_460353
  have hstable : (prefixWord ++ tailWord_460353).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_460353).length < 2 ^ (prefixWord ++ tailWord_460353).sum := by decide
  have hdescent : baseEnd_460353 < baseStart_460353 := by decide
  rcases family_descends (prefixWord ++ tailWord_460353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_460370 : List Nat := [3, 2, 2, 1, 2, 3, 1, 3, 3]
def baseStart_460370 : Nat := 118140960795 + 460370 * 2 ^ 59
def prefixEnd_460370 : Nat := 4983230072969 + 3 ^ 40 * 460370 * 2
def baseEnd_460370 : Nat := 210125412364861363518047

theorem tailTrace_460370 : CollatzResearch.WordTrace tailWord_460370 prefixEnd_460370 210125412364861363518047 := by
  unfold tailWord_460370
  simp only [CollatzResearch.WordTrace]
  refine ⟨4197768335541397445364641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11194048894777059854305709 4197768335541397445364641)
  ·
    refine ⟨3148326251656048084023481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4197768335541397445364641 3148326251656048084023481)
    ·
      refine ⟨2361244688742036063017611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3148326251656048084023481 2361244688742036063017611)
      ·
        refine ⟨3541867033113054094526417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2361244688742036063017611 3541867033113054094526417)
        ·
          refine ⟨2656400274834790570894813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3541867033113054094526417 2656400274834790570894813)
          ·
            refine ⟨996150103063046464085555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2656400274834790570894813 996150103063046464085555)
            ·
              refine ⟨1494225154594569696128333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 996150103063046464085555 1494225154594569696128333)
              ·
                refine ⟨560334432972963636048125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1494225154594569696128333 560334432972963636048125)
                ·
                  refine ⟨210125412364861363518047, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 560334432972963636048125 210125412364861363518047)
                  ·
                    rfl

theorem cell20_460370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 3, 1, 3, 3].length) (baseStart_460370 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_460370 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_460370 prefixEnd_460370 := by exact prefixLift 460370
  have htrace : WordTrace (prefixWord ++ tailWord_460370) baseStart_460370 baseEnd_460370 := by
    simpa [prefixWord, tailWord_460370, baseEnd_460370] using wordTrace_append hprefix tailTrace_460370
  have hstable : (prefixWord ++ tailWord_460370).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_460370).length < 2 ^ (prefixWord ++ tailWord_460370).sum := by decide
  have hdescent : baseEnd_460370 < baseStart_460370 := by decide
  rcases family_descends (prefixWord ++ tailWord_460370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_460453 : List Nat := [1, 3, 1, 2, 1, 2, 3, 5, 2]
def baseStart_460453 : Nat := 118140960795 + 460453 * 2 ^ 59
def prefixEnd_460453 : Nat := 4983230072969 + 3 ^ 40 * 460453 * 2
def baseEnd_460453 : Nat := 210163295826481963751041

theorem tailTrace_460453 : CollatzResearch.WordTrace tailWord_460453 prefixEnd_460453 210163295826481963751041 := by
  unfold tailWord_460453
  simp only [CollatzResearch.WordTrace]
  refine ⟨16794100600864894956730013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11196067067243263304486675 16794100600864894956730013)
  ·
    refine ⟨6297787725324335608773755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16794100600864894956730013 6297787725324335608773755)
    ·
      refine ⟨9446681587986503413160633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6297787725324335608773755 9446681587986503413160633)
      ·
        refine ⟨7085011190989877559870475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9446681587986503413160633 7085011190989877559870475)
        ·
          refine ⟨10627516786484816339805713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7085011190989877559870475 10627516786484816339805713)
          ·
            refine ⟨7970637589863612254854285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10627516786484816339805713 7970637589863612254854285)
            ·
              refine ⟨2988989096198854595570357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7970637589863612254854285 2988989096198854595570357)
              ·
                refine ⟨280217727768642618334721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2988989096198854595570357 280217727768642618334721)
                ·
                  refine ⟨210163295826481963751041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 280217727768642618334721 210163295826481963751041)
                  ·
                    rfl

theorem cell20_460453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 3, 5, 2].length) (baseStart_460453 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_460453 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_460453 prefixEnd_460453 := by exact prefixLift 460453
  have htrace : WordTrace (prefixWord ++ tailWord_460453) baseStart_460453 baseEnd_460453 := by
    simpa [prefixWord, tailWord_460453, baseEnd_460453] using wordTrace_append hprefix tailTrace_460453
  have hstable : (prefixWord ++ tailWord_460453).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_460453).length < 2 ^ (prefixWord ++ tailWord_460453).sum := by decide
  have hdescent : baseEnd_460453 < baseStart_460453 := by decide
  rcases family_descends (prefixWord ++ tailWord_460453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_460456 : List Nat := [2, 1, 7, 1, 1, 1, 7]
def baseStart_460456 : Nat := 118140960795 + 460456 * 2 ^ 59
def prefixEnd_460456 : Nat := 4983230072969 + 3 ^ 40 * 460456 * 2
def baseEnd_460456 : Nat := 23351629456469698516781

theorem tailTrace_460456 : CollatzResearch.WordTrace tailWord_460456 prefixEnd_460456 23351629456469698516781 := by
  unfold tailWord_460456
  simp only [CollatzResearch.WordTrace]
  refine ⟨8397105009927013234544611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11196140013236017646059481 8397105009927013234544611)
  ·
    refine ⟨12595657514890519851816917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8397105009927013234544611 12595657514890519851816917)
    ·
      refine ⟨295210723005246559026959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 12595657514890519851816917 295210723005246559026959)
      ·
        refine ⟨442816084507869838540439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 295210723005246559026959 442816084507869838540439)
        ·
          refine ⟨664224126761804757810659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 442816084507869838540439 664224126761804757810659)
          ·
            refine ⟨996336190142707136715989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 664224126761804757810659 996336190142707136715989)
            ·
              refine ⟨23351629456469698516781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 996336190142707136715989 23351629456469698516781)
              ·
                rfl

theorem cell20_460456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 1, 7].length) (baseStart_460456 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_460456 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_460456 prefixEnd_460456 := by exact prefixLift 460456
  have htrace : WordTrace (prefixWord ++ tailWord_460456) baseStart_460456 baseEnd_460456 := by
    simpa [prefixWord, tailWord_460456, baseEnd_460456] using wordTrace_append hprefix tailTrace_460456
  have hstable : (prefixWord ++ tailWord_460456).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_460456).length < 2 ^ (prefixWord ++ tailWord_460456).sum := by decide
  have hdescent : baseEnd_460456 < baseStart_460456 := by decide
  rcases family_descends (prefixWord ++ tailWord_460456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_460470 : List Nat := [5, 1, 3, 1, 1, 1, 1, 3, 4]
def baseStart_460470 : Nat := 118140960795 + 460470 * 2 ^ 59
def prefixEnd_460470 : Nat := 4983230072969 + 3 ^ 40 * 460470 * 2
def baseEnd_460470 : Nat := 210171055089705460184305

theorem tailTrace_460470 : CollatzResearch.WordTrace tailWord_460470 prefixEnd_460470 210171055089705460184305 := by
  unfold tailWord_460470
  simp only [CollatzResearch.WordTrace]
  refine ⟨1049670040112706678756179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 11196480427868871240065909 1049670040112706678756179)
  ·
    refine ⟨1574505060169060018134269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1049670040112706678756179 1574505060169060018134269)
    ·
      refine ⟨590439397563397506800351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1574505060169060018134269 590439397563397506800351)
      ·
        refine ⟨885659096345096260200527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 590439397563397506800351 885659096345096260200527)
        ·
          refine ⟨1328488644517644390300791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 885659096345096260200527 1328488644517644390300791)
          ·
            refine ⟨1992732966776466585451187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1328488644517644390300791 1992732966776466585451187)
            ·
              refine ⟨2989099450164699878176781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1992732966776466585451187 2989099450164699878176781)
              ·
                refine ⟨1120912293811762454316293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2989099450164699878176781 1120912293811762454316293)
                ·
                  refine ⟨210171055089705460184305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1120912293811762454316293 210171055089705460184305)
                  ·
                    rfl

theorem cell20_460470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 1, 3, 4].length) (baseStart_460470 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_460470 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_460470 prefixEnd_460470 := by exact prefixLift 460470
  have htrace : WordTrace (prefixWord ++ tailWord_460470) baseStart_460470 baseEnd_460470 := by
    simpa [prefixWord, tailWord_460470, baseEnd_460470] using wordTrace_append hprefix tailTrace_460470
  have hstable : (prefixWord ++ tailWord_460470).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_460470).length < 2 ^ (prefixWord ++ tailWord_460470).sum := by decide
  have hdescent : baseEnd_460470 < baseStart_460470 := by decide
  rcases family_descends (prefixWord ++ tailWord_460470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_460474 : List Nat := [3, 1, 1, 1, 2, 4, 1, 3, 4]
def baseStart_460474 : Nat := 118140960795 + 460474 * 2 ^ 59
def prefixEnd_460474 : Nat := 4983230072969 + 3 ^ 40 * 460474 * 2
def baseEnd_460474 : Nat := 210172880798699224050955

theorem tailTrace_460474 : CollatzResearch.WordTrace tailWord_460474 prefixEnd_460474 210172880798699224050955 := by
  unfold tailWord_460474
  simp only [CollatzResearch.WordTrace]
  refine ⟨4198716633447203885811119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11196577689192543695496317 4198716633447203885811119)
  ·
    refine ⟨6298074950170805828716679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4198716633447203885811119 6298074950170805828716679)
    ·
      refine ⟨9447112425256208743075019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6298074950170805828716679 9447112425256208743075019)
      ·
        refine ⟨14170668637884313114612529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9447112425256208743075019 14170668637884313114612529)
        ·
          refine ⟨10628001478413234835959397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14170668637884313114612529 10628001478413234835959397)
          ·
            refine ⟨1992750277202481531742387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10628001478413234835959397 1992750277202481531742387)
            ·
              refine ⟨2989125415803722297613581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1992750277202481531742387 2989125415803722297613581)
              ·
                refine ⟨1120922030926395861605093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2989125415803722297613581 1120922030926395861605093)
                ·
                  refine ⟨210172880798699224050955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1120922030926395861605093 210172880798699224050955)
                  ·
                    rfl

theorem cell20_460474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 1, 3, 4].length) (baseStart_460474 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_460474 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_460474 prefixEnd_460474 := by exact prefixLift 460474
  have htrace : WordTrace (prefixWord ++ tailWord_460474) baseStart_460474 baseEnd_460474 := by
    simpa [prefixWord, tailWord_460474, baseEnd_460474] using wordTrace_append hprefix tailTrace_460474
  have hstable : (prefixWord ++ tailWord_460474).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_460474).length < 2 ^ (prefixWord ++ tailWord_460474).sum := by decide
  have hdescent : baseEnd_460474 < baseStart_460474 := by decide
  rcases family_descends (prefixWord ++ tailWord_460474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_460498 : List Nat := [3, 2, 2, 2, 2, 2, 1, 6]
def baseStart_460498 : Nat := 118140960795 + 460498 * 2 ^ 59
def prefixEnd_460498 : Nat := 4983230072969 + 3 ^ 40 * 460498 * 2
def baseEnd_460498 : Nat := 70061278350887269083619

theorem tailTrace_460498 : CollatzResearch.WordTrace tailWord_460498 prefixEnd_460498 70061278350887269083619 := by
  unfold tailWord_460498
  simp only [CollatzResearch.WordTrace]
  refine ⟨4198935471425466910529537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11197161257134578428078765 4198935471425466910529537)
  ·
    refine ⟨3149201603569100182897153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4198935471425466910529537 3149201603569100182897153)
    ·
      refine ⟨2361901202676825137172865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3149201603569100182897153 2361901202676825137172865)
      ·
        refine ⟨1771425902007618852879649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2361901202676825137172865 1771425902007618852879649)
        ·
          refine ⟨1328569426505714139659737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1771425902007618852879649 1328569426505714139659737)
          ·
            refine ⟨996427069879285604744803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1328569426505714139659737 996427069879285604744803)
            ·
              refine ⟨1494640604818928407117205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 996427069879285604744803 1494640604818928407117205)
              ·
                refine ⟨70061278350887269083619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1494640604818928407117205 70061278350887269083619)
                ·
                  rfl

theorem cell20_460498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 2, 1, 6].length) (baseStart_460498 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_460498 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_460498 prefixEnd_460498 := by exact prefixLift 460498
  have htrace : WordTrace (prefixWord ++ tailWord_460498) baseStart_460498 baseEnd_460498 := by
    simpa [prefixWord, tailWord_460498, baseEnd_460498] using wordTrace_append hprefix tailTrace_460498
  have hstable : (prefixWord ++ tailWord_460498).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_460498).length < 2 ^ (prefixWord ++ tailWord_460498).sum := by decide
  have hdescent : baseEnd_460498 < baseStart_460498 := by decide
  rcases family_descends (prefixWord ++ tailWord_460498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_460515 : List Nat := [1, 1, 1, 7, 3, 1, 6]
def baseStart_460515 : Nat := 118140960795 + 460515 * 2 ^ 59
def prefixEnd_460515 : Nat := 4983230072969 + 3 ^ 40 * 460515 * 2
def baseEnd_460515 : Nat := 23354621590653922631569

theorem tailTrace_460515 : CollatzResearch.WordTrace tailWord_460515 prefixEnd_460515 23354621590653922631569 := by
  unfold tailWord_460515
  simp only [CollatzResearch.WordTrace]
  refine ⟨16796361926640279545486999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11197574617760186363657999 16796361926640279545486999)
  ·
    refine ⟨25194542889960419318230499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16796361926640279545486999 25194542889960419318230499)
    ·
      refine ⟨37791814334940628977345749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25194542889960419318230499 37791814334940628977345749)
      ·
        refine ⟨885745648475170991656541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 37791814334940628977345749 885745648475170991656541)
        ·
          refine ⟨332154618178189121871203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 885745648475170991656541 332154618178189121871203)
          ·
            refine ⟨498231927267283682806805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 332154618178189121871203 498231927267283682806805)
            ·
              refine ⟨23354621590653922631569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 498231927267283682806805 23354621590653922631569)
              ·
                rfl

theorem cell20_460515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 3, 1, 6].length) (baseStart_460515 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_460515 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_460515 prefixEnd_460515 := by exact prefixLift 460515
  have htrace : WordTrace (prefixWord ++ tailWord_460515) baseStart_460515 baseEnd_460515 := by
    simpa [prefixWord, tailWord_460515, baseEnd_460515] using wordTrace_append hprefix tailTrace_460515
  have hstable : (prefixWord ++ tailWord_460515).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_460515).length < 2 ^ (prefixWord ++ tailWord_460515).sum := by decide
  have hdescent : baseEnd_460515 < baseStart_460515 := by decide
  rcases family_descends (prefixWord ++ tailWord_460515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_460525 : List Nat := [1, 5, 1, 2, 1, 3, 3, 2, 2]
def baseStart_460525 : Nat := 118140960795 + 460525 * 2 ^ 59
def prefixEnd_460525 : Nat := 4983230072969 + 3 ^ 40 * 460525 * 2
def baseEnd_460525 : Nat := 210196158588369713350747

theorem tailTrace_460525 : CollatzResearch.WordTrace tailWord_460525 prefixEnd_460525 210196158588369713350747 := by
  unfold tailWord_460525
  simp only [CollatzResearch.WordTrace]
  refine ⟨16796726656604051253351029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11197817771069367502234019 16796726656604051253351029)
  ·
    refine ⟨1574693124056629805001659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 16796726656604051253351029 1574693124056629805001659)
    ·
      refine ⟨2362039686084944707502489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1574693124056629805001659 2362039686084944707502489)
      ·
        refine ⟨1771529764563708530626867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2362039686084944707502489 1771529764563708530626867)
        ·
          refine ⟨2657294646845562795940301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1771529764563708530626867 2657294646845562795940301)
          ·
            refine ⟨996485492567086048477613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2657294646845562795940301 996485492567086048477613)
            ·
              refine ⟨373682059712657268179105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 996485492567086048477613 373682059712657268179105)
              ·
                refine ⟨280261544784492951134329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 373682059712657268179105 280261544784492951134329)
                ·
                  refine ⟨210196158588369713350747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 280261544784492951134329 210196158588369713350747)
                  ·
                    rfl

theorem cell20_460525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 3, 3, 2, 2].length) (baseStart_460525 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_460525 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_460525 prefixEnd_460525 := by exact prefixLift 460525
  have htrace : WordTrace (prefixWord ++ tailWord_460525) baseStart_460525 baseEnd_460525 := by
    simpa [prefixWord, tailWord_460525, baseEnd_460525] using wordTrace_append hprefix tailTrace_460525
  have hstable : (prefixWord ++ tailWord_460525).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_460525).length < 2 ^ (prefixWord ++ tailWord_460525).sum := by decide
  have hdescent : baseEnd_460525 < baseStart_460525 := by decide
  rcases family_descends (prefixWord ++ tailWord_460525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_460529 : List Nat := [1, 2, 2, 2, 2, 5, 1, 1, 4]
def baseStart_460529 : Nat := 118140960795 + 460529 * 2 ^ 59
def prefixEnd_460529 : Nat := 4983230072969 + 3 ^ 40 * 460529 * 2
def baseEnd_460529 : Nat := 210197984297363477217397

theorem tailTrace_460529 : CollatzResearch.WordTrace tailWord_460529 prefixEnd_460529 210197984297363477217397 := by
  unfold tailWord_460529
  simp only [CollatzResearch.WordTrace]
  refine ⟨16796872548589559936496641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11197915032393039957664427 16796872548589559936496641)
  ·
    refine ⟨12597654411442169952372481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16796872548589559936496641 12597654411442169952372481)
    ·
      refine ⟨9448240808581627464279361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12597654411442169952372481 9448240808581627464279361)
      ·
        refine ⟨7086180606436220598209521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9448240808581627464279361 7086180606436220598209521)
        ·
          refine ⟨5314635454827165448657141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7086180606436220598209521 5314635454827165448657141)
          ·
            refine ⟨498247073890046760811607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 5314635454827165448657141 498247073890046760811607)
            ·
              refine ⟨747370610835070141217411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 498247073890046760811607 747370610835070141217411)
              ·
                refine ⟨1121055916252605211826117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 747370610835070141217411 1121055916252605211826117)
                ·
                  refine ⟨210197984297363477217397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1121055916252605211826117 210197984297363477217397)
                  ·
                    rfl

theorem cell20_460529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 5, 1, 1, 4].length) (baseStart_460529 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_460529 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_460529 prefixEnd_460529 := by exact prefixLift 460529
  have htrace : WordTrace (prefixWord ++ tailWord_460529) baseStart_460529 baseEnd_460529 := by
    simpa [prefixWord, tailWord_460529, baseEnd_460529] using wordTrace_append hprefix tailTrace_460529
  have hstable : (prefixWord ++ tailWord_460529).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_460529).length < 2 ^ (prefixWord ++ tailWord_460529).sum := by decide
  have hdescent : baseEnd_460529 < baseStart_460529 := by decide
  rcases family_descends (prefixWord ++ tailWord_460529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_460532 : List Nat := [2, 6, 1, 1, 1, 2, 2, 5]
def baseStart_460532 : Nat := 118140960795 + 460532 * 2 ^ 59
def prefixEnd_460532 : Nat := 4983230072969 + 3 ^ 40 * 460532 * 2
def baseEnd_460532 : Nat := 70066451193036266705795

theorem tailTrace_460532 : CollatzResearch.WordTrace tailWord_460532 prefixEnd_460532 70066451193036266705795 := by
  unfold tailWord_460532
  simp only [CollatzResearch.WordTrace]
  refine ⟨8398490983789345724427925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11197987978385794299237233 8398490983789345724427925)
  ·
    refine ⟨393679264865125580832559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 8398490983789345724427925 393679264865125580832559)
    ·
      refine ⟨590518897297688371248839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 393679264865125580832559 590518897297688371248839)
      ·
        refine ⟨885778345946532556873259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 590518897297688371248839 885778345946532556873259)
        ·
          refine ⟨1328667518919798835309889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 885778345946532556873259 1328667518919798835309889)
          ·
            refine ⟨996500639189849126482417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1328667518919798835309889 996500639189849126482417)
            ·
              refine ⟨747375479392386844861813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 996500639189849126482417 747375479392386844861813)
              ·
                refine ⟨70066451193036266705795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 747375479392386844861813 70066451193036266705795)
                ·
                  rfl

theorem cell20_460532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 2, 2, 5].length) (baseStart_460532 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_460532 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_460532 prefixEnd_460532 := by exact prefixLift 460532
  have htrace : WordTrace (prefixWord ++ tailWord_460532) baseStart_460532 baseEnd_460532 := by
    simpa [prefixWord, tailWord_460532, baseEnd_460532] using wordTrace_append hprefix tailTrace_460532
  have hstable : (prefixWord ++ tailWord_460532).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_460532).length < 2 ^ (prefixWord ++ tailWord_460532).sum := by decide
  have hdescent : baseEnd_460532 < baseStart_460532 := by decide
  rcases family_descends (prefixWord ++ tailWord_460532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_460571 : List Nat := [1, 1, 1, 1, 1, 1, 4, 4, 6]
def baseStart_460571 : Nat := 118140960795 + 460571 * 2 ^ 59
def prefixEnd_460571 : Nat := 4983230072969 + 3 ^ 40 * 460571 * 2
def baseEnd_460571 : Nat := 210217154241797997817225

theorem tailTrace_460571 : CollatzResearch.WordTrace tailWord_460571 prefixEnd_460571 210217154241797997817225 := by
  unfold tailWord_460571
  simp only [CollatzResearch.WordTrace]
  refine ⟨16798404414437401109525567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11198936276291600739683711 16798404414437401109525567)
  ·
    refine ⟨25197606621656101664288351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16798404414437401109525567 25197606621656101664288351)
    ·
      refine ⟨37796409932484152496432527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25197606621656101664288351 37796409932484152496432527)
      ·
        refine ⟨56694614898726228744648791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37796409932484152496432527 56694614898726228744648791)
        ·
          refine ⟨85041922348089343116973187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56694614898726228744648791 85041922348089343116973187)
          ·
            refine ⟨127562883522134014675459781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85041922348089343116973187 127562883522134014675459781)
            ·
              refine ⟨23918040660400127751648709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 127562883522134014675459781 23918040660400127751648709)
              ·
                refine ⟨4484632623825023953434133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23918040660400127751648709 4484632623825023953434133)
                ·
                  refine ⟨210217154241797997817225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4484632623825023953434133 210217154241797997817225)
                  ·
                    rfl

theorem cell20_460571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 4, 6].length) (baseStart_460571 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_460571 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_460571 prefixEnd_460571 := by exact prefixLift 460571
  have htrace : WordTrace (prefixWord ++ tailWord_460571) baseStart_460571 baseEnd_460571 := by
    simpa [prefixWord, tailWord_460571, baseEnd_460571] using wordTrace_append hprefix tailTrace_460571
  have hstable : (prefixWord ++ tailWord_460571).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_460571).length < 2 ^ (prefixWord ++ tailWord_460571).sum := by decide
  have hdescent : baseEnd_460571 < baseStart_460571 := by decide
  rcases family_descends (prefixWord ++ tailWord_460571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_460581 : List Nat := [1, 3, 1, 2, 3, 2, 1, 4, 3]
def baseStart_460581 : Nat := 118140960795 + 460581 * 2 ^ 59
def prefixEnd_460581 : Nat := 4983230072969 + 3 ^ 40 * 460581 * 2
def baseEnd_460581 : Nat := 210221718514282407483851

theorem tailTrace_460581 : CollatzResearch.WordTrace tailWord_460581 prefixEnd_460581 210221718514282407483851 := by
  unfold tailWord_460581
  simp only [CollatzResearch.WordTrace]
  refine ⟨16798769144401172817389597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11199179429600781878259731 16798769144401172817389597)
  ·
    refine ⟨6299538429150439806521099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16798769144401172817389597 6299538429150439806521099)
    ·
      refine ⟨9449307643725659709781649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6299538429150439806521099 9449307643725659709781649)
      ·
        refine ⟨7086980732794244782336237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9449307643725659709781649 7086980732794244782336237)
        ·
          refine ⟨2657617774797841793376089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7086980732794244782336237 2657617774797841793376089)
          ·
            refine ⟨1993213331098381345032067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2657617774797841793376089 1993213331098381345032067)
            ·
              refine ⟨2989819996647572017548101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1993213331098381345032067 2989819996647572017548101)
              ·
                refine ⟨560591249371419753290269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2989819996647572017548101 560591249371419753290269)
                ·
                  refine ⟨210221718514282407483851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 560591249371419753290269 210221718514282407483851)
                  ·
                    rfl

theorem cell20_460581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 1, 4, 3].length) (baseStart_460581 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_460581 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_460581 prefixEnd_460581 := by exact prefixLift 460581
  have htrace : WordTrace (prefixWord ++ tailWord_460581) baseStart_460581 baseEnd_460581 := by
    simpa [prefixWord, tailWord_460581, baseEnd_460581] using wordTrace_append hprefix tailTrace_460581
  have hstable : (prefixWord ++ tailWord_460581).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_460581).length < 2 ^ (prefixWord ++ tailWord_460581).sum := by decide
  have hdescent : baseEnd_460581 < baseStart_460581 := by decide
  rcases family_descends (prefixWord ++ tailWord_460581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_460584 : List Nat := [2, 1, 5, 1, 1, 3, 1, 4, 2]
def baseStart_460584 : Nat := 118140960795 + 460584 * 2 ^ 59
def prefixEnd_460584 : Nat := 4983230072969 + 3 ^ 40 * 460584 * 2
def baseEnd_460584 : Nat := 210223087796027730383839

theorem tailTrace_460584 : CollatzResearch.WordTrace tailWord_460584 prefixEnd_460584 210223087796027730383839 := by
  unfold tailWord_460584
  simp only [CollatzResearch.WordTrace]
  refine ⟨8399439281695152164874403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11199252375593536219832537 8399439281695152164874403)
  ·
    refine ⟨12599158922542728247311605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8399439281695152164874403 12599158922542728247311605)
    ·
      refine ⟨1181171148988380773185463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 12599158922542728247311605 1181171148988380773185463)
      ·
        refine ⟨1771756723482571159778195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1181171148988380773185463 1771756723482571159778195)
        ·
          refine ⟨2657635085223856739667293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1771756723482571159778195 2657635085223856739667293)
          ·
            refine ⟨996613156958946277375235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2657635085223856739667293 996613156958946277375235)
            ·
              refine ⟨1494919735438419416062853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 996613156958946277375235 1494919735438419416062853)
              ·
                refine ⟨280297450394703640511785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1494919735438419416062853 280297450394703640511785)
                ·
                  refine ⟨210223087796027730383839, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 280297450394703640511785 210223087796027730383839)
                  ·
                    rfl

theorem cell20_460584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 3, 1, 4, 2].length) (baseStart_460584 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_460584 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_460584 prefixEnd_460584 := by exact prefixLift 460584
  have htrace : WordTrace (prefixWord ++ tailWord_460584) baseStart_460584 baseEnd_460584 := by
    simpa [prefixWord, tailWord_460584, baseEnd_460584] using wordTrace_append hprefix tailTrace_460584
  have hstable : (prefixWord ++ tailWord_460584).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_460584).length < 2 ^ (prefixWord ++ tailWord_460584).sum := by decide
  have hdescent : baseEnd_460584 < baseStart_460584 := by decide
  rcases family_descends (prefixWord ++ tailWord_460584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_460605 : List Nat := [1, 4, 1, 4, 1, 2, 1, 2, 4]
def baseStart_460605 : Nat := 118140960795 + 460605 * 2 ^ 59
def prefixEnd_460605 : Nat := 4983230072969 + 3 ^ 40 * 460605 * 2
def baseEnd_460605 : Nat := 210232672768244990683753

theorem tailTrace_460605 : CollatzResearch.WordTrace tailWord_460605 prefixEnd_460605 210232672768244990683753 := by
  unfold tailWord_460605
  simp only [CollatzResearch.WordTrace]
  refine ⟨16799644496314224916263269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11199762997542816610842179 16799644496314224916263269)
  ·
    refine ⟨3149933343058917171799363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16799644496314224916263269 3149933343058917171799363)
    ·
      refine ⟨4724900014588375757699045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3149933343058917171799363 4724900014588375757699045)
      ·
        refine ⟨885918752735320454568571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4724900014588375757699045 885918752735320454568571)
        ·
          refine ⟨1328878129102980681852857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 885918752735320454568571 1328878129102980681852857)
          ·
            refine ⟨996658596827235511389643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1328878129102980681852857 996658596827235511389643)
            ·
              refine ⟨1494987895240853267084465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 996658596827235511389643 1494987895240853267084465)
              ·
                refine ⟨1121240921430639950313349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1494987895240853267084465 1121240921430639950313349)
                ·
                  refine ⟨210232672768244990683753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1121240921430639950313349 210232672768244990683753)
                  ·
                    rfl

theorem cell20_460605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 2, 1, 2, 4].length) (baseStart_460605 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_460605 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_460605 prefixEnd_460605 := by exact prefixLift 460605
  have htrace : WordTrace (prefixWord ++ tailWord_460605) baseStart_460605 baseEnd_460605 := by
    simpa [prefixWord, tailWord_460605, baseEnd_460605] using wordTrace_append hprefix tailTrace_460605
  have hstable : (prefixWord ++ tailWord_460605).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_460605).length < 2 ^ (prefixWord ++ tailWord_460605).sum := by decide
  have hdescent : baseEnd_460605 < baseStart_460605 := by decide
  rcases family_descends (prefixWord ++ tailWord_460605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_460636 : List Nat := [2, 2, 4, 2, 2, 1, 1, 1, 5]
def baseStart_460636 : Nat := 118140960795 + 460636 * 2 ^ 59
def prefixEnd_460636 : Nat := 4983230072969 + 3 ^ 40 * 460636 * 2
def baseEnd_460636 : Nat := 210246822012946660650293

theorem tailTrace_460636 : CollatzResearch.WordTrace tailWord_460636 prefixEnd_460636 210246822012946660650293 := by
  unfold tailWord_460636
  simp only [CollatzResearch.WordTrace]
  refine ⟨8400387579600958605320881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11200516772801278140427841 8400387579600958605320881)
  ·
    refine ⟨6300290684700718953990661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8400387579600958605320881 6300290684700718953990661)
    ·
      refine ⟨1181304503381384803873249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6300290684700718953990661 1181304503381384803873249)
      ·
        refine ⟨885978377536038602904937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1181304503381384803873249 885978377536038602904937)
        ·
          refine ⟨664483783152028952178703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 885978377536038602904937 664483783152028952178703)
          ·
            refine ⟨996725674728043428268055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 664483783152028952178703 996725674728043428268055)
            ·
              refine ⟨1495088512092065142402083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 996725674728043428268055 1495088512092065142402083)
              ·
                refine ⟨2242632768138097713603125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1495088512092065142402083 2242632768138097713603125)
                ·
                  refine ⟨210246822012946660650293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2242632768138097713603125 210246822012946660650293)
                  ·
                    rfl

theorem cell20_460636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 1, 1, 1, 5].length) (baseStart_460636 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_460636 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_460636 prefixEnd_460636 := by exact prefixLift 460636
  have htrace : WordTrace (prefixWord ++ tailWord_460636) baseStart_460636 baseEnd_460636 := by
    simpa [prefixWord, tailWord_460636, baseEnd_460636] using wordTrace_append hprefix tailTrace_460636
  have hstable : (prefixWord ++ tailWord_460636).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_460636).length < 2 ^ (prefixWord ++ tailWord_460636).sum := by decide
  have hdescent : baseEnd_460636 < baseStart_460636 := by decide
  rcases family_descends (prefixWord ++ tailWord_460636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_460643 : List Nat := [1, 1, 1, 5, 4, 1, 2, 1, 4]
def baseStart_460643 : Nat := 118140960795 + 460643 * 2 ^ 59
def prefixEnd_460643 : Nat := 4983230072969 + 3 ^ 40 * 460643 * 2
def baseEnd_460643 : Nat := 210250017003685747416931

theorem tailTrace_460643 : CollatzResearch.WordTrace tailWord_460643 prefixEnd_460643 210250017003685747416931 := by
  unfold tailWord_460643
  simp only [CollatzResearch.WordTrace]
  refine ⟨16801030470176557406146583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11200686980117704937431055 16801030470176557406146583)
  ·
    refine ⟨25201545705264836109219875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16801030470176557406146583 25201545705264836109219875)
    ·
      refine ⟨37802318557897254163829813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25201545705264836109219875 37802318557897254163829813)
      ·
        refine ⟨3543967364802867577859045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 37802318557897254163829813 3543967364802867577859045)
        ·
          refine ⟨664493880900537670848571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3543967364802867577859045 664493880900537670848571)
          ·
            refine ⟨996740821350806506272857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 664493880900537670848571 996740821350806506272857)
            ·
              refine ⟨747555616013104879704643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 996740821350806506272857 747555616013104879704643)
              ·
                refine ⟨1121333424019657319556965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 747555616013104879704643 1121333424019657319556965)
                ·
                  refine ⟨210250017003685747416931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1121333424019657319556965 210250017003685747416931)
                  ·
                    rfl

theorem cell20_460643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 1, 2, 1, 4].length) (baseStart_460643 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_460643 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_460643 prefixEnd_460643 := by exact prefixLift 460643
  have htrace : WordTrace (prefixWord ++ tailWord_460643) baseStart_460643 baseEnd_460643 := by
    simpa [prefixWord, tailWord_460643, baseEnd_460643] using wordTrace_append hprefix tailTrace_460643
  have hstable : (prefixWord ++ tailWord_460643).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_460643).length < 2 ^ (prefixWord ++ tailWord_460643).sum := by decide
  have hdescent : baseEnd_460643 < baseStart_460643 := by decide
  rcases family_descends (prefixWord ++ tailWord_460643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_460694 : List Nat := [5, 3, 1, 1, 2, 2, 1, 1, 4]
def baseStart_460694 : Nat := 118140960795 + 460694 * 2 ^ 59
def prefixEnd_460694 : Nat := 4983230072969 + 3 ^ 40 * 460694 * 2
def baseEnd_460694 : Nat := 210273294793356236716723

theorem tailTrace_460694 : CollatzResearch.WordTrace tailWord_460694 prefixEnd_460694 210273294793356236716723 := by
  unfold tailWord_460694
  simp only [CollatzResearch.WordTrace]
  refine ⟨1050180662061987069765821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 11201927061994528744168757 1050180662061987069765821)
  ·
    refine ⟨393817748273245151162183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1050180662061987069765821 393817748273245151162183)
    ·
      refine ⟨590726622409867726743275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 393817748273245151162183 590726622409867726743275)
      ·
        refine ⟨886089933614801590114913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 590726622409867726743275 886089933614801590114913)
        ·
          refine ⟨664567450211101192586185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 886089933614801590114913 664567450211101192586185)
          ·
            refine ⟨498425587658325894439639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 664567450211101192586185 498425587658325894439639)
            ·
              refine ⟨747638381487488841659459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 498425587658325894439639 747638381487488841659459)
              ·
                refine ⟨1121457572231233262489189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 747638381487488841659459 1121457572231233262489189)
                ·
                  refine ⟨210273294793356236716723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1121457572231233262489189 210273294793356236716723)
                  ·
                    rfl

theorem cell20_460694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 2, 1, 1, 4].length) (baseStart_460694 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_460694 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_460694 prefixEnd_460694 := by exact prefixLift 460694
  have htrace : WordTrace (prefixWord ++ tailWord_460694) baseStart_460694 baseEnd_460694 := by
    simpa [prefixWord, tailWord_460694, baseEnd_460694] using wordTrace_append hprefix tailTrace_460694
  have hstable : (prefixWord ++ tailWord_460694).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_460694).length < 2 ^ (prefixWord ++ tailWord_460694).sum := by decide
  have hdescent : baseEnd_460694 < baseStart_460694 := by decide
  rcases family_descends (prefixWord ++ tailWord_460694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_460723 : List Nat := [1, 1, 1, 2, 3, 1, 4, 1, 6]
def baseStart_460723 : Nat := 118140960795 + 460723 * 2 ^ 59
def prefixEnd_460723 : Nat := 4983230072969 + 3 ^ 40 * 460723 * 2
def baseEnd_460723 : Nat := 210286531183561024749937

theorem tailTrace_460723 : CollatzResearch.WordTrace tailWord_460723 prefixEnd_460723 210286531183561024749937 := by
  unfold tailWord_460723
  simp only [CollatzResearch.WordTrace]
  refine ⟨16803948309886731069058823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11202632206591154046039215 16803948309886731069058823)
  ·
    refine ⟨25205922464830096603588235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16803948309886731069058823 25205922464830096603588235)
    ·
      refine ⟨37808883697245144905382353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25205922464830096603588235 37808883697245144905382353)
      ·
        refine ⟨28356662772933858679036765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37808883697245144905382353 28356662772933858679036765)
        ·
          refine ⟨10633748539850197004638787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28356662772933858679036765 10633748539850197004638787)
          ·
            refine ⟨15950622809775295506958181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10633748539850197004638787 15950622809775295506958181)
            ·
              refine ⟨2990741776832867907554659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15950622809775295506958181 2990741776832867907554659)
              ·
                refine ⟨4486112665249301861331989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2990741776832867907554659 4486112665249301861331989)
                ·
                  refine ⟨210286531183561024749937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4486112665249301861331989 210286531183561024749937)
                  ·
                    rfl

theorem cell20_460723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 4, 1, 6].length) (baseStart_460723 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_460723 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_460723 prefixEnd_460723 := by exact prefixLift 460723
  have htrace : WordTrace (prefixWord ++ tailWord_460723) baseStart_460723 baseEnd_460723 := by
    simpa [prefixWord, tailWord_460723, baseEnd_460723] using wordTrace_append hprefix tailTrace_460723
  have hstable : (prefixWord ++ tailWord_460723).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_460723).length < 2 ^ (prefixWord ++ tailWord_460723).sum := by decide
  have hdescent : baseEnd_460723 < baseStart_460723 := by decide
  rcases family_descends (prefixWord ++ tailWord_460723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_460771 : List Nat := [1, 1, 1, 6, 1, 2, 2, 3, 3]
def baseStart_460771 : Nat := 118140960795 + 460771 * 2 ^ 59
def prefixEnd_460771 : Nat := 4983230072969 + 3 ^ 40 * 460771 * 2
def baseEnd_460771 : Nat := 210308439691486191149741

theorem tailTrace_460771 : CollatzResearch.WordTrace tailWord_460771 prefixEnd_460771 210308439691486191149741 := by
  unfold tailWord_460771
  simp only [CollatzResearch.WordTrace]
  refine ⟨16805699013712835266806167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11203799342475223511204111 16805699013712835266806167)
  ·
    refine ⟨25208548520569252900209251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16805699013712835266806167 25208548520569252900209251)
    ·
      refine ⟨37812822780853879350313877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25208548520569252900209251 37812822780853879350313877)
      ·
        refine ⟨1772476067852525594545963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 37812822780853879350313877 1772476067852525594545963)
        ·
          refine ⟨2658714101778788391818945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1772476067852525594545963 2658714101778788391818945)
          ·
            refine ⟨1994035576334091293864209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2658714101778788391818945 1994035576334091293864209)
            ·
              refine ⟨1495526682250568470398157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1994035576334091293864209 1495526682250568470398157)
              ·
                refine ⟨560822505843963176399309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1495526682250568470398157 560822505843963176399309)
                ·
                  refine ⟨210308439691486191149741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 560822505843963176399309 210308439691486191149741)
                  ·
                    rfl

theorem cell20_460771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 2, 3, 3].length) (baseStart_460771 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_460771 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_460771 prefixEnd_460771 := by exact prefixLift 460771
  have htrace : WordTrace (prefixWord ++ tailWord_460771) baseStart_460771 baseEnd_460771 := by
    simpa [prefixWord, tailWord_460771, baseEnd_460771] using wordTrace_append hprefix tailTrace_460771
  have hstable : (prefixWord ++ tailWord_460771).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_460771).length < 2 ^ (prefixWord ++ tailWord_460771).sum := by decide
  have hdescent : baseEnd_460771 < baseStart_460771 := by decide
  rcases family_descends (prefixWord ++ tailWord_460771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_460778 : List Nat := [3, 1, 3, 1, 2, 1, 3, 2, 4]
def baseStart_460778 : Nat := 118140960795 + 460778 * 2 ^ 59
def prefixEnd_460778 : Nat := 4983230072969 + 3 ^ 40 * 460778 * 2
def baseEnd_460778 : Nat := 210311634682225277916379

theorem tailTrace_460778 : CollatzResearch.WordTrace tailWord_460778 prefixEnd_460778 210311634682225277916379 := by
  unfold tailWord_460778
  simp only [CollatzResearch.WordTrace]
  refine ⟨4201488581171868865577747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11203969549791650308207325 4201488581171868865577747)
  ·
    refine ⟨6302232871757803298366621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4201488581171868865577747 6302232871757803298366621)
    ·
      refine ⟨2363337326909176236887483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6302232871757803298366621 2363337326909176236887483)
      ·
        refine ⟨3545005990363764355331225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2363337326909176236887483 3545005990363764355331225)
        ·
          refine ⟨2658754492772823266498419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3545005990363764355331225 2658754492772823266498419)
          ·
            refine ⟨3988131739159234899747629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2658754492772823266498419 3988131739159234899747629)
            ·
              refine ⟨1495549402184713087405361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3988131739159234899747629 1495549402184713087405361)
              ·
                refine ⟨1121662051638534815554021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1495549402184713087405361 1121662051638534815554021)
                ·
                  refine ⟨210311634682225277916379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1121662051638534815554021 210311634682225277916379)
                  ·
                    rfl

theorem cell20_460778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 3, 2, 4].length) (baseStart_460778 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_460778 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_460778 prefixEnd_460778 := by exact prefixLift 460778
  have htrace : WordTrace (prefixWord ++ tailWord_460778) baseStart_460778 baseEnd_460778 := by
    simpa [prefixWord, tailWord_460778, baseEnd_460778] using wordTrace_append hprefix tailTrace_460778
  have hstable : (prefixWord ++ tailWord_460778).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_460778).length < 2 ^ (prefixWord ++ tailWord_460778).sum := by decide
  have hdescent : baseEnd_460778 < baseStart_460778 := by decide
  rcases family_descends (prefixWord ++ tailWord_460778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_460826 : List Nat := [3, 1, 1, 3, 1, 4, 3, 1, 3]
def baseStart_460826 : Nat := 118140960795 + 460826 * 2 ^ 59
def prefixEnd_460826 : Nat := 4983230072969 + 3 ^ 40 * 460826 * 2
def baseEnd_460826 : Nat := 210333543190150444316183

theorem tailTrace_460826 : CollatzResearch.WordTrace tailWord_460826 prefixEnd_460826 210333543190150444316183 := by
  unfold tailWord_460826
  simp only [CollatzResearch.WordTrace]
  refine ⟨4201926257128394915014583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11205136685675719773372221 4201926257128394915014583)
  ·
    refine ⟨6302889385692592372521875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4201926257128394915014583 6302889385692592372521875)
    ·
      refine ⟨9454334078538888558782813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6302889385692592372521875 9454334078538888558782813)
      ·
        refine ⟨3545375279452083209543555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9454334078538888558782813 3545375279452083209543555)
        ·
          refine ⟨5318062919178124814315333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3545375279452083209543555 5318062919178124814315333)
          ·
            refine ⟨997136797345898402684125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5318062919178124814315333 997136797345898402684125)
            ·
              refine ⟨373926299004711901006547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 997136797345898402684125 373926299004711901006547)
              ·
                refine ⟨560889448507067851509821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 373926299004711901006547 560889448507067851509821)
                ·
                  refine ⟨210333543190150444316183, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 560889448507067851509821 210333543190150444316183)
                  ·
                    rfl

theorem cell20_460826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 4, 3, 1, 3].length) (baseStart_460826 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_460826 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_460826 prefixEnd_460826 := by exact prefixLift 460826
  have htrace : WordTrace (prefixWord ++ tailWord_460826) baseStart_460826 baseEnd_460826 := by
    simpa [prefixWord, tailWord_460826, baseEnd_460826] using wordTrace_append hprefix tailTrace_460826
  have hstable : (prefixWord ++ tailWord_460826).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_460826).length < 2 ^ (prefixWord ++ tailWord_460826).sum := by decide
  have hdescent : baseEnd_460826 < baseStart_460826 := by decide
  rcases family_descends (prefixWord ++ tailWord_460826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_460836 : List Nat := [2, 3, 1, 4, 3, 1, 2, 4]
def baseStart_460836 : Nat := 118140960795 + 460836 * 2 ^ 59
def prefixEnd_460836 : Nat := 4983230072969 + 3 ^ 40 * 460836 * 2
def baseEnd_460836 : Nat := 70112702487544951327603

theorem tailTrace_460836 : CollatzResearch.WordTrace tailWord_460836 prefixEnd_460836 70112702487544951327603 := by
  unfold tailWord_460836
  simp only [CollatzResearch.WordTrace]
  refine ⟨8404034879238675683961181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11205379838984900911948241 8404034879238675683961181)
  ·
    refine ⟨3151513079714503381485443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8404034879238675683961181 3151513079714503381485443)
    ·
      refine ⟨4727269619571755072228165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3151513079714503381485443 4727269619571755072228165)
      ·
        refine ⟨886363053669704076042781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4727269619571755072228165 886363053669704076042781)
        ·
          refine ⟨332386145126139028516043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 886363053669704076042781 332386145126139028516043)
          ·
            refine ⟨498579217689208542774065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 332386145126139028516043 498579217689208542774065)
            ·
              refine ⟨373934413266906407080549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 498579217689208542774065 373934413266906407080549)
              ·
                refine ⟨70112702487544951327603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 373934413266906407080549 70112702487544951327603)
                ·
                  rfl

theorem cell20_460836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 3, 1, 2, 4].length) (baseStart_460836 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_460836 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_460836 prefixEnd_460836 := by exact prefixLift 460836
  have htrace : WordTrace (prefixWord ++ tailWord_460836) baseStart_460836 baseEnd_460836 := by
    simpa [prefixWord, tailWord_460836, baseEnd_460836] using wordTrace_append hprefix tailTrace_460836
  have hstable : (prefixWord ++ tailWord_460836).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_460836).length < 2 ^ (prefixWord ++ tailWord_460836).sum := by decide
  have hdescent : baseEnd_460836 < baseStart_460836 := by decide
  rcases family_descends (prefixWord ++ tailWord_460836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_460850 : List Nat := [3, 2, 1, 1, 2, 5, 1, 3, 2]
def baseStart_460850 : Nat := 118140960795 + 460850 * 2 ^ 59
def prefixEnd_460850 : Nat := 4983230072969 + 3 ^ 40 * 460850 * 2
def baseEnd_460850 : Nat := 210344497444113027516085

theorem tailTrace_460850 : CollatzResearch.WordTrace tailWord_460850 prefixEnd_460850 210344497444113027516085 := by
  unfold tailWord_460850
  simp only [CollatzResearch.WordTrace]
  refine ⟨4202145095106657939733001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11205720253617754505954669 4202145095106657939733001)
  ·
    refine ⟨3151608821329993454799751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4202145095106657939733001 3151608821329993454799751)
    ·
      refine ⟨4727413231994990182199627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3151608821329993454799751 4727413231994990182199627)
      ·
        refine ⟨7091119847992485273299441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4727413231994990182199627 7091119847992485273299441)
        ·
          refine ⟨5318339885994363954974581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7091119847992485273299441 5318339885994363954974581)
          ·
            refine ⟨498594364311971620778867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 5318339885994363954974581 498594364311971620778867)
            ·
              refine ⟨747891546467957431168301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 498594364311971620778867 747891546467957431168301)
              ·
                refine ⟨280459329925484036688113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 747891546467957431168301 280459329925484036688113)
                ·
                  refine ⟨210344497444113027516085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 280459329925484036688113 210344497444113027516085)
                  ·
                    rfl

theorem cell20_460850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 5, 1, 3, 2].length) (baseStart_460850 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_460850 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_460850 prefixEnd_460850 := by exact prefixLift 460850
  have htrace : WordTrace (prefixWord ++ tailWord_460850) baseStart_460850 baseEnd_460850 := by
    simpa [prefixWord, tailWord_460850, baseEnd_460850] using wordTrace_append hprefix tailTrace_460850
  have hstable : (prefixWord ++ tailWord_460850).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_460850).length < 2 ^ (prefixWord ++ tailWord_460850).sum := by decide
  have hdescent : baseEnd_460850 < baseStart_460850 := by decide
  rcases family_descends (prefixWord ++ tailWord_460850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_460885 : List Nat := [1, 3, 2, 2, 1, 4, 1, 3, 3]
def baseStart_460885 : Nat := 118140960795 + 460885 * 2 ^ 59
def prefixEnd_460885 : Nat := 4983230072969 + 3 ^ 40 * 460885 * 2
def baseEnd_460885 : Nat := 210360472397808461349275

theorem tailTrace_460885 : CollatzResearch.WordTrace tailWord_460885 prefixEnd_460885 210360472397808461349275 := by
  unfold tailWord_460885
  simp only [CollatzResearch.WordTrace]
  refine ⟨16809856935299832736456109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11206571290199888490970739 16809856935299832736456109)
  ·
    refine ⟨6303696350737437276171041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16809856935299832736456109 6303696350737437276171041)
    ·
      refine ⟨4727772263053077957128281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6303696350737437276171041 4727772263053077957128281)
      ·
        refine ⟨3545829197289808467846211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4727772263053077957128281 3545829197289808467846211)
        ·
          refine ⟨5318743795934712701769317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3545829197289808467846211 5318743795934712701769317)
          ·
            refine ⟨997264461737758631581747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5318743795934712701769317 997264461737758631581747)
            ·
              refine ⟨1495896692606637947372621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 997264461737758631581747 1495896692606637947372621)
              ·
                refine ⟨560961259727489230264733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1495896692606637947372621 560961259727489230264733)
                ·
                  refine ⟨210360472397808461349275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 560961259727489230264733 210360472397808461349275)
                  ·
                    rfl

theorem cell20_460885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 4, 1, 3, 3].length) (baseStart_460885 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_460885 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_460885 prefixEnd_460885 := by exact prefixLift 460885
  have htrace : WordTrace (prefixWord ++ tailWord_460885) baseStart_460885 baseEnd_460885 := by
    simpa [prefixWord, tailWord_460885, baseEnd_460885] using wordTrace_append hprefix tailTrace_460885
  have hstable : (prefixWord ++ tailWord_460885).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_460885).length < 2 ^ (prefixWord ++ tailWord_460885).sum := by decide
  have hdescent : baseEnd_460885 < baseStart_460885 := by decide
  rcases family_descends (prefixWord ++ tailWord_460885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_460909 : List Nat := [1, 5, 1, 1, 2, 1, 2, 5, 2]
def baseStart_460909 : Nat := 118140960795 + 460909 * 2 ^ 59
def prefixEnd_460909 : Nat := 4983230072969 + 3 ^ 40 * 460909 * 2
def baseEnd_460909 : Nat := 210371426651771044549177

theorem tailTrace_460909 : CollatzResearch.WordTrace tailWord_460909 prefixEnd_460909 210371426651771044549177 := by
  unfold tailWord_460909
  simp only [CollatzResearch.WordTrace]
  refine ⟨16810732287212884835329781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11207154858141923223553187 16810732287212884835329781)
  ·
    refine ⟨1576006151926207953312167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 16810732287212884835329781 1576006151926207953312167)
    ·
      refine ⟨2364009227889311929968251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1576006151926207953312167 2364009227889311929968251)
      ·
        refine ⟨3546013841833967894952377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2364009227889311929968251 3546013841833967894952377)
        ·
          refine ⟨2659510381375475921214283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3546013841833967894952377 2659510381375475921214283)
          ·
            refine ⟨3989265572063213881821425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2659510381375475921214283 3989265572063213881821425)
            ·
              refine ⟨2991949179047410411366069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3989265572063213881821425 2991949179047410411366069)
              ·
                refine ⟨280495235535694726065569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2991949179047410411366069 280495235535694726065569)
                ·
                  refine ⟨210371426651771044549177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 280495235535694726065569 210371426651771044549177)
                  ·
                    rfl

theorem cell20_460909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 2, 5, 2].length) (baseStart_460909 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_460909 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_460909 prefixEnd_460909 := by exact prefixLift 460909
  have htrace : WordTrace (prefixWord ++ tailWord_460909) baseStart_460909 baseEnd_460909 := by
    simpa [prefixWord, tailWord_460909, baseEnd_460909] using wordTrace_append hprefix tailTrace_460909
  have hstable : (prefixWord ++ tailWord_460909).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_460909).length < 2 ^ (prefixWord ++ tailWord_460909).sum := by decide
  have hdescent : baseEnd_460909 < baseStart_460909 := by decide
  rcases family_descends (prefixWord ++ tailWord_460909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_460944 : List Nat := [2, 1, 1, 1, 1, 1, 5, 5, 3]
def baseStart_460944 : Nat := 118140960795 + 460944 * 2 ^ 59
def prefixEnd_460944 : Nat := 4983230072969 + 3 ^ 40 * 460944 * 2
def baseEnd_460944 : Nat := 210387401605466478382367

theorem tailTrace_460944 : CollatzResearch.WordTrace tailWord_460944 prefixEnd_460944 210387401605466478382367 := by
  unfold tailWord_460944
  simp only [CollatzResearch.WordTrace]
  refine ⟨8406004421043042906426943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11208005894724057208569257 8406004421043042906426943)
  ·
    refine ⟨12609006631564564359640415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8406004421043042906426943 12609006631564564359640415)
    ·
      refine ⟨18913509947346846539460623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12609006631564564359640415 18913509947346846539460623)
      ·
        refine ⟨28370264921020269809190935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18913509947346846539460623 28370264921020269809190935)
        ·
          refine ⟨42555397381530404713786403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28370264921020269809190935 42555397381530404713786403)
          ·
            refine ⟨63833096072295607070679605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42555397381530404713786403 63833096072295607070679605)
            ·
              refine ⟨5984352756777713162876213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 63833096072295607070679605 5984352756777713162876213)
              ·
                refine ⟨561033070947910609019645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5984352756777713162876213 561033070947910609019645)
                ·
                  refine ⟨210387401605466478382367, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 561033070947910609019645 210387401605466478382367)
                  ·
                    rfl

theorem cell20_460944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 5, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 5, 5, 3].length) (baseStart_460944 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_460944 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_460944 prefixEnd_460944 := by exact prefixLift 460944
  have htrace : WordTrace (prefixWord ++ tailWord_460944) baseStart_460944 baseEnd_460944 := by
    simpa [prefixWord, tailWord_460944, baseEnd_460944] using wordTrace_append hprefix tailTrace_460944
  have hstable : (prefixWord ++ tailWord_460944).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_460944).length < 2 ^ (prefixWord ++ tailWord_460944).sum := by decide
  have hdescent : baseEnd_460944 < baseStart_460944 := by decide
  rcases family_descends (prefixWord ++ tailWord_460944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_460964 : List Nat := [2, 3, 1, 2, 4, 1, 2, 3, 2]
def baseStart_460964 : Nat := 118140960795 + 460964 * 2 ^ 59
def prefixEnd_460964 : Nat := 4983230072969 + 3 ^ 40 * 460964 * 2
def baseEnd_460964 : Nat := 210396530150435297715619

theorem tailTrace_460964 : CollatzResearch.WordTrace tailWord_460964 prefixEnd_460964 210396530150435297715619 := by
  unfold tailWord_460964
  simp only [CollatzResearch.WordTrace]
  refine ⟨8406369151006814614290973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11208492201342419485721297 8406369151006814614290973)
  ·
    refine ⟨3152388431627555480359115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8406369151006814614290973 3152388431627555480359115)
    ·
      refine ⟨4728582647441333220538673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3152388431627555480359115 4728582647441333220538673)
      ·
        refine ⟨3546436985580999915404005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4728582647441333220538673 3546436985580999915404005)
        ·
          refine ⟨664956934796437484138251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3546436985580999915404005 664956934796437484138251)
          ·
            refine ⟨997435402194656226207377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 664956934796437484138251 997435402194656226207377)
            ·
              refine ⟨748076551645992169655533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 997435402194656226207377 748076551645992169655533)
              ·
                refine ⟨280528706867247063620825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 748076551645992169655533 280528706867247063620825)
                ·
                  refine ⟨210396530150435297715619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 280528706867247063620825 210396530150435297715619)
                  ·
                    rfl

theorem cell20_460964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 1, 2, 3, 2].length) (baseStart_460964 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_460964 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_460964 prefixEnd_460964 := by exact prefixLift 460964
  have htrace : WordTrace (prefixWord ++ tailWord_460964) baseStart_460964 baseEnd_460964 := by
    simpa [prefixWord, tailWord_460964, baseEnd_460964] using wordTrace_append hprefix tailTrace_460964
  have hstable : (prefixWord ++ tailWord_460964).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_460964).length < 2 ^ (prefixWord ++ tailWord_460964).sum := by decide
  have hdescent : baseEnd_460964 < baseStart_460964 := by decide
  rcases family_descends (prefixWord ++ tailWord_460964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_460974 : List Nat := [4, 1, 4, 2, 1, 2, 1, 2, 3]
def baseStart_460974 : Nat := 118140960795 + 460974 * 2 ^ 59
def prefixEnd_460974 : Nat := 4983230072969 + 3 ^ 40 * 460974 * 2
def baseEnd_460974 : Nat := 210401094422919707382245

theorem tailTrace_460974 : CollatzResearch.WordTrace tailWord_460974 prefixEnd_460974 210401094422919707382245 := by
  unfold tailWord_460974
  simp only [CollatzResearch.WordTrace]
  refine ⟨2101637878997175117055747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11208735354651600624297317 2101637878997175117055747)
  ·
    refine ⟨3152456818495762675583621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2101637878997175117055747 3152456818495762675583621)
    ·
      refine ⟨591085653467955501671929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3152456818495762675583621 591085653467955501671929)
      ·
        refine ⟨443314240100966626253947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 591085653467955501671929 443314240100966626253947)
        ·
          refine ⟨664971360151449939380921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 443314240100966626253947 664971360151449939380921)
          ·
            refine ⟨498728520113587454535691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 664971360151449939380921 498728520113587454535691)
            ·
              refine ⟨748092780170381181803537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 498728520113587454535691 748092780170381181803537)
              ·
                refine ⟨561069585127785886352653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 748092780170381181803537 561069585127785886352653)
                ·
                  refine ⟨210401094422919707382245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 561069585127785886352653 210401094422919707382245)
                  ·
                    rfl

theorem cell20_460974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 2, 1, 2, 3].length) (baseStart_460974 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_460974 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_460974 prefixEnd_460974 := by exact prefixLift 460974
  have htrace : WordTrace (prefixWord ++ tailWord_460974) baseStart_460974 baseEnd_460974 := by
    simpa [prefixWord, tailWord_460974, baseEnd_460974] using wordTrace_append hprefix tailTrace_460974
  have hstable : (prefixWord ++ tailWord_460974).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_460974).length < 2 ^ (prefixWord ++ tailWord_460974).sum := by decide
  have hdescent : baseEnd_460974 < baseStart_460974 := by decide
  rcases family_descends (prefixWord ++ tailWord_460974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_461006 : List Nat := [4, 1, 1, 1, 4, 1, 2, 2, 4]
def baseStart_461006 : Nat := 118140960795 + 461006 * 2 ^ 59
def prefixEnd_461006 : Nat := 4983230072969 + 3 ^ 40 * 461006 * 2
def baseEnd_461006 : Nat := 210415700094869818315447

theorem tailTrace_461006 : CollatzResearch.WordTrace tailWord_461006 prefixEnd_461006 210415700094869818315447 := by
  unfold tailWord_461006
  simp only [CollatzResearch.WordTrace]
  refine ⟨2101783770982683800201359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11209513445240980267740581 2101783770982683800201359)
  ·
    refine ⟨3152675656474025700302039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2101783770982683800201359 3152675656474025700302039)
    ·
      refine ⟨4729013484711038550453059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3152675656474025700302039 4729013484711038550453059)
      ·
        refine ⟨7093520227066557825679589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4729013484711038550453059 7093520227066557825679589)
        ·
          refine ⟨1330035042574979592314923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7093520227066557825679589 1330035042574979592314923)
          ·
            refine ⟨1995052563862469388472385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1330035042574979592314923 1995052563862469388472385)
            ·
              refine ⟨1496289422896852041354289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1995052563862469388472385 1496289422896852041354289)
              ·
                refine ⟨1122217067172639031015717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1496289422896852041354289 1122217067172639031015717)
                ·
                  refine ⟨210415700094869818315447, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1122217067172639031015717 210415700094869818315447)
                  ·
                    rfl

theorem cell20_461006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 2, 2, 4].length) (baseStart_461006 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_461006 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_461006 prefixEnd_461006 := by exact prefixLift 461006
  have htrace : WordTrace (prefixWord ++ tailWord_461006) baseStart_461006 baseEnd_461006 := by
    simpa [prefixWord, tailWord_461006, baseEnd_461006] using wordTrace_append hprefix tailTrace_461006
  have hstable : (prefixWord ++ tailWord_461006).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_461006).length < 2 ^ (prefixWord ++ tailWord_461006).sum := by decide
  have hdescent : baseEnd_461006 < baseStart_461006 := by decide
  rcases family_descends (prefixWord ++ tailWord_461006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_461026 : List Nat := [3, 3, 4, 1, 1, 2, 6]
def baseStart_461026 : Nat := 118140960795 + 461026 * 2 ^ 59
def prefixEnd_461026 : Nat := 4983230072969 + 3 ^ 40 * 461026 * 2
def baseEnd_461026 : Nat := 23380536515537626405411

theorem tailTrace_461026 : CollatzResearch.WordTrace tailWord_461026 prefixEnd_461026 23380536515537626405411 := by
  unfold tailWord_461026
  simp only [CollatzResearch.WordTrace]
  refine ⟨4203749906947253454334733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11209999751859342544892621 4203749906947253454334733)
  ·
    refine ⟨1576406215105220045375525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4203749906947253454334733 1576406215105220045375525)
    ·
      refine ⟨295576165332228758507911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1576406215105220045375525 295576165332228758507911)
      ·
        refine ⟨443364247998343137761867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 295576165332228758507911 443364247998343137761867)
        ·
          refine ⟨665046371997514706642801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 443364247998343137761867 665046371997514706642801)
          ·
            refine ⟨498784778998136029982101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 665046371997514706642801 498784778998136029982101)
            ·
              refine ⟨23380536515537626405411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 498784778998136029982101 23380536515537626405411)
              ·
                rfl

theorem cell20_461026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 2, 6].length) (baseStart_461026 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_461026 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_461026 prefixEnd_461026 := by exact prefixLift 461026
  have htrace : WordTrace (prefixWord ++ tailWord_461026) baseStart_461026 baseEnd_461026 := by
    simpa [prefixWord, tailWord_461026, baseEnd_461026] using wordTrace_append hprefix tailTrace_461026
  have hstable : (prefixWord ++ tailWord_461026).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_461026).length < 2 ^ (prefixWord ++ tailWord_461026).sum := by decide
  have hdescent : baseEnd_461026 < baseStart_461026 := by decide
  rcases family_descends (prefixWord ++ tailWord_461026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_461102 : List Nat := [4, 1, 3, 3, 2, 1, 1, 5]
def baseStart_461102 : Nat := 118140960795 + 461102 * 2 ^ 59
def prefixEnd_461102 : Nat := 4983230072969 + 3 ^ 40 * 461102 * 2
def baseEnd_461102 : Nat := 70153172370240050371685

theorem tailTrace_461102 : CollatzResearch.WordTrace tailWord_461102 prefixEnd_461102 70153172370240050371685 := by
  unfold tailWord_461102
  simp only [CollatzResearch.WordTrace]
  refine ⟨2102221446939209849638195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11211847717009119198070373 2102221446939209849638195)
  ·
    refine ⟨3153332170408814774457293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2102221446939209849638195 3153332170408814774457293)
    ·
      refine ⟨1182499563903305540421485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3153332170408814774457293 1182499563903305540421485)
      ·
        refine ⟨443437336463739577658057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1182499563903305540421485 443437336463739577658057)
        ·
          refine ⟨332578002347804683243543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 443437336463739577658057 332578002347804683243543)
          ·
            refine ⟨498867003521707024865315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 332578002347804683243543 498867003521707024865315)
            ·
              refine ⟨748300505282560537297973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 498867003521707024865315 748300505282560537297973)
              ·
                refine ⟨70153172370240050371685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 748300505282560537297973 70153172370240050371685)
                ·
                  rfl

theorem cell20_461102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 2, 1, 1, 5].length) (baseStart_461102 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_461102 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_461102 prefixEnd_461102 := by exact prefixLift 461102
  have htrace : WordTrace (prefixWord ++ tailWord_461102) baseStart_461102 baseEnd_461102 := by
    simpa [prefixWord, tailWord_461102, baseEnd_461102] using wordTrace_append hprefix tailTrace_461102
  have hstable : (prefixWord ++ tailWord_461102).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_461102).length < 2 ^ (prefixWord ++ tailWord_461102).sum := by decide
  have hdescent : baseEnd_461102 < baseStart_461102 := by decide
  rcases family_descends (prefixWord ++ tailWord_461102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_461106 : List Nat := [3, 2, 1, 1, 5, 2, 1, 5]
def baseStart_461106 : Nat := 118140960795 + 461106 * 2 ^ 59
def prefixEnd_461106 : Nat := 4983230072969 + 3 ^ 40 * 461106 * 2
def baseEnd_461106 : Nat := 70153780939904638327235

theorem tailTrace_461106 : CollatzResearch.WordTrace tailWord_461106 prefixEnd_461106 70153780939904638327235 := by
  unfold tailWord_461106
  simp only [CollatzResearch.WordTrace]
  refine ⟨4204479366874796870062793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11211944978332791653500781 4204479366874796870062793)
  ·
    refine ⟨3153359525156097652547095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4204479366874796870062793 3153359525156097652547095)
    ·
      refine ⟨4730039287734146478820643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3153359525156097652547095 4730039287734146478820643)
      ·
        refine ⟨7095058931601219718230965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4730039287734146478820643 7095058931601219718230965)
        ·
          refine ⟨665161774837614348584153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 7095058931601219718230965 665161774837614348584153)
          ·
            refine ⟨498871331128210761438115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 665161774837614348584153 498871331128210761438115)
            ·
              refine ⟨748306996692316142157173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 498871331128210761438115 748306996692316142157173)
              ·
                refine ⟨70153780939904638327235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 748306996692316142157173 70153780939904638327235)
                ·
                  rfl

theorem cell20_461106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 2, 1, 5].length) (baseStart_461106 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_461106 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_461106 prefixEnd_461106 := by exact prefixLift 461106
  have htrace : WordTrace (prefixWord ++ tailWord_461106) baseStart_461106 baseEnd_461106 := by
    simpa [prefixWord, tailWord_461106, baseEnd_461106] using wordTrace_append hprefix tailTrace_461106
  have hstable : (prefixWord ++ tailWord_461106).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_461106).length < 2 ^ (prefixWord ++ tailWord_461106).sum := by decide
  have hdescent : baseEnd_461106 < baseStart_461106 := by decide
  rcases family_descends (prefixWord ++ tailWord_461106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_461113 : List Nat := [1, 2, 1, 6, 1, 1, 2, 3, 3]
def baseStart_461113 : Nat := 118140960795 + 461113 * 2 ^ 59
def prefixEnd_461113 : Nat := 4983230072969 + 3 ^ 40 * 461113 * 2
def baseEnd_461113 : Nat := 210464537810453001748343

theorem tailTrace_461113 : CollatzResearch.WordTrace tailWord_461113 prefixEnd_461113 210464537810453001748343 := by
  unfold tailWord_461113
  simp only [CollatzResearch.WordTrace]
  refine ⟨16818172778473827675755993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11212115185649218450503995 16818172778473827675755993)
  ·
    refine ⟨12613629583855370756816995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16818172778473827675755993 12613629583855370756816995)
    ·
      refine ⟨18920444375783056135225493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12613629583855370756816995 18920444375783056135225493)
      ·
        refine ⟨886895830114830756338695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 18920444375783056135225493 886895830114830756338695)
        ·
          refine ⟨1330343745172246134508043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 886895830114830756338695 1330343745172246134508043)
          ·
            refine ⟨1995515617758369201762065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1330343745172246134508043 1995515617758369201762065)
            ·
              refine ⟨1496636713318776901321549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1995515617758369201762065 1496636713318776901321549)
              ·
                refine ⟨561238767494541337995581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1496636713318776901321549 561238767494541337995581)
                ·
                  refine ⟨210464537810453001748343, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 561238767494541337995581 210464537810453001748343)
                  ·
                    rfl

theorem cell20_461113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 2, 3, 3].length) (baseStart_461113 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_461113 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_461113 prefixEnd_461113 := by exact prefixLift 461113
  have htrace : WordTrace (prefixWord ++ tailWord_461113) baseStart_461113 baseEnd_461113 := by
    simpa [prefixWord, tailWord_461113, baseEnd_461113] using wordTrace_append hprefix tailTrace_461113
  have hstable : (prefixWord ++ tailWord_461113).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_461113).length < 2 ^ (prefixWord ++ tailWord_461113).sum := by decide
  have hdescent : baseEnd_461113 < baseStart_461113 := by decide
  rcases family_descends (prefixWord ++ tailWord_461113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_461127 : List Nat := [1, 1, 4, 1, 2, 2, 5, 4]
def baseStart_461127 : Nat := 118140960795 + 461127 * 2 ^ 59
def prefixEnd_461127 : Nat := 4983230072969 + 3 ^ 40 * 461127 * 2
def baseEnd_461127 : Nat := 70156975930643725093873

theorem tailTrace_461127 : CollatzResearch.WordTrace tailWord_461127 prefixEnd_461127 70156975930643725093873 := by
  unfold tailWord_461127
  simp only [CollatzResearch.WordTrace]
  refine ⟨16818683400423108066765635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11212455600282072044510423 16818683400423108066765635)
  ·
    refine ⟨25228025100634662100148453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16818683400423108066765635 25228025100634662100148453)
    ·
      refine ⟨4730254706368999143777835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 25228025100634662100148453 4730254706368999143777835)
      ·
        refine ⟨7095382059553498715666753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4730254706368999143777835 7095382059553498715666753)
        ·
          refine ⟨5321536544665124036750065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7095382059553498715666753 5321536544665124036750065)
          ·
            refine ⟨3991152408498843027562549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5321536544665124036750065 3991152408498843027562549)
            ·
              refine ⟨374170538296766533833989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3991152408498843027562549 374170538296766533833989)
              ·
                refine ⟨70156975930643725093873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 374170538296766533833989 70156975930643725093873)
                ·
                  rfl

theorem cell20_461127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 5, 4].length) (baseStart_461127 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_461127 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_461127 prefixEnd_461127 := by exact prefixLift 461127
  have htrace : WordTrace (prefixWord ++ tailWord_461127) baseStart_461127 baseEnd_461127 := by
    simpa [prefixWord, tailWord_461127, baseEnd_461127] using wordTrace_append hprefix tailTrace_461127
  have hstable : (prefixWord ++ tailWord_461127).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_461127).length < 2 ^ (prefixWord ++ tailWord_461127).sum := by decide
  have hdescent : baseEnd_461127 < baseStart_461127 := by decide
  rcases family_descends (prefixWord ++ tailWord_461127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_461137 : List Nat := [1, 2, 2, 1, 4, 3, 2, 3, 2]
def baseStart_461137 : Nat := 118140960795 + 461137 * 2 ^ 59
def prefixEnd_461137 : Nat := 4983230072969 + 3 ^ 40 * 461137 * 2
def baseEnd_461137 : Nat := 210475492064415584948245

theorem tailTrace_461137 : CollatzResearch.WordTrace tailWord_461137 prefixEnd_461137 210475492064415584948245 := by
  unfold tailWord_461137
  simp only [CollatzResearch.WordTrace]
  refine ⟨16819048130386879774629665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11212698753591253183086443 16819048130386879774629665)
  ·
    refine ⟨12614286097790159830972249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16819048130386879774629665 12614286097790159830972249)
    ·
      refine ⟨9460714573342619873229187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12614286097790159830972249 9460714573342619873229187)
      ·
        refine ⟨14191071860013929809843781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9460714573342619873229187 14191071860013929809843781)
        ·
          refine ⟨2660825973752611839345709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14191071860013929809843781 2660825973752611839345709)
          ·
            refine ⟨997809740157229439754641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2660825973752611839345709 997809740157229439754641)
            ·
              refine ⟨748357305117922079815981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 997809740157229439754641 748357305117922079815981)
              ·
                refine ⟨280633989419220779930993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 748357305117922079815981 280633989419220779930993)
                ·
                  refine ⟨210475492064415584948245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 280633989419220779930993 210475492064415584948245)
                  ·
                    rfl

theorem cell20_461137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 3, 2, 3, 2].length) (baseStart_461137 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_461137 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_461137 prefixEnd_461137 := by exact prefixLift 461137
  have htrace : WordTrace (prefixWord ++ tailWord_461137) baseStart_461137 baseEnd_461137 := by
    simpa [prefixWord, tailWord_461137, baseEnd_461137] using wordTrace_append hprefix tailTrace_461137
  have hstable : (prefixWord ++ tailWord_461137).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_461137).length < 2 ^ (prefixWord ++ tailWord_461137).sum := by decide
  have hdescent : baseEnd_461137 < baseStart_461137 := by decide
  rcases family_descends (prefixWord ++ tailWord_461137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_461150 : List Nat := [4, 4, 2, 1, 1, 1, 2, 1, 4]
def baseStart_461150 : Nat := 118140960795 + 461150 * 2 ^ 59
def prefixEnd_461150 : Nat := 4983230072969 + 3 ^ 40 * 461150 * 2
def baseEnd_461150 : Nat := 210481425618645317514859

theorem tailTrace_461150 : CollatzResearch.WordTrace tailWord_461150 prefixEnd_461150 210481425618645317514859 := by
  unfold tailWord_461150
  simp only [CollatzResearch.WordTrace]
  refine ⟨2102440284917472874356613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11213014852893188663235269 2102440284917472874356613)
  ·
    refine ⟨394207553422026163941865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2102440284917472874356613 394207553422026163941865)
    ·
      refine ⟨295655665066519622956399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 394207553422026163941865 295655665066519622956399)
      ·
        refine ⟨443483497599779434434599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 295655665066519622956399 443483497599779434434599)
        ·
          refine ⟨665225246399669151651899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 443483497599779434434599 665225246399669151651899)
          ·
            refine ⟨997837869599503727477849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 665225246399669151651899 997837869599503727477849)
            ·
              refine ⟨748378402199627795608387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 997837869599503727477849 748378402199627795608387)
              ·
                refine ⟨1122567603299441693412581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 748378402199627795608387 1122567603299441693412581)
                ·
                  refine ⟨210481425618645317514859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1122567603299441693412581 210481425618645317514859)
                  ·
                    rfl

theorem cell20_461150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 1, 2, 1, 4].length) (baseStart_461150 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_461150 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_461150 prefixEnd_461150 := by exact prefixLift 461150
  have htrace : WordTrace (prefixWord ++ tailWord_461150) baseStart_461150 baseEnd_461150 := by
    simpa [prefixWord, tailWord_461150, baseEnd_461150] using wordTrace_append hprefix tailTrace_461150
  have hstable : (prefixWord ++ tailWord_461150).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_461150).length < 2 ^ (prefixWord ++ tailWord_461150).sum := by decide
  have hdescent : baseEnd_461150 < baseStart_461150 := by decide
  rcases family_descends (prefixWord ++ tailWord_461150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_461179 : List Nat := [1, 1, 1, 1, 1, 7, 2, 2, 4]
def baseStart_461179 : Nat := 118140960795 + 461179 * 2 ^ 59
def prefixEnd_461179 : Nat := 4983230072969 + 3 ^ 40 * 461179 * 2
def baseEnd_461179 : Nat := 210494662008850105548073

theorem tailTrace_461179 : CollatzResearch.WordTrace tailWord_461179 prefixEnd_461179 210494662008850105548073 := by
  unfold tailWord_461179
  simp only [CollatzResearch.WordTrace]
  refine ⟨16820579996234720947658591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11213719997489813965105727 16820579996234720947658591)
  ·
    refine ⟨25230869994352081421487887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16820579996234720947658591 25230869994352081421487887)
    ·
      refine ⟨37846304991528122132231831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25230869994352081421487887 37846304991528122132231831)
      ·
        refine ⟨56769457487292183198347747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37846304991528122132231831 56769457487292183198347747)
        ·
          refine ⟨85154186230938274797521621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56769457487292183198347747 85154186230938274797521621)
          ·
            refine ⟨1995801239787615815566913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 85154186230938274797521621 1995801239787615815566913)
            ·
              refine ⟨1496850929840711861675185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1995801239787615815566913 1496850929840711861675185)
              ·
                refine ⟨1122638197380533896256389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1496850929840711861675185 1122638197380533896256389)
                ·
                  refine ⟨210494662008850105548073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1122638197380533896256389 210494662008850105548073)
                  ·
                    rfl

theorem cell20_461179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 2, 2, 4].length) (baseStart_461179 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_461179 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_461179 prefixEnd_461179 := by exact prefixLift 461179
  have htrace : WordTrace (prefixWord ++ tailWord_461179) baseStart_461179 baseEnd_461179 := by
    simpa [prefixWord, tailWord_461179, baseEnd_461179] using wordTrace_append hprefix tailTrace_461179
  have hstable : (prefixWord ++ tailWord_461179).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_461179).length < 2 ^ (prefixWord ++ tailWord_461179).sum := by decide
  have hdescent : baseEnd_461179 < baseStart_461179 := by decide
  rcases family_descends (prefixWord ++ tailWord_461179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_461210 : List Nat := [3, 1, 1, 4, 1, 2, 2, 1, 5]
def baseStart_461210 : Nat := 118140960795 + 461210 * 2 ^ 59
def prefixEnd_461210 : Nat := 4983230072969 + 3 ^ 40 * 461210 * 2
def baseEnd_461210 : Nat := 210508811253551775514613

theorem tailTrace_461210 : CollatzResearch.WordTrace tailWord_461210 prefixEnd_461210 210508811253551775514613 := by
  unfold tailWord_461210
  simp only [CollatzResearch.WordTrace]
  refine ⟨4205427664780603310509271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11214473772748275494691389 4205427664780603310509271)
  ·
    refine ⟨6308141497170904965763907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4205427664780603310509271 6308141497170904965763907)
    ·
      refine ⟨9462212245756357448645861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6308141497170904965763907 9462212245756357448645861)
      ·
        refine ⟨1774164796079317021621099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9462212245756357448645861 1774164796079317021621099)
        ·
          refine ⟨2661247194118975532431649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1774164796079317021621099 2661247194118975532431649)
          ·
            refine ⟨1995935395589231649323737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2661247194118975532431649 1995935395589231649323737)
            ·
              refine ⟨1496951546691923736992803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1995935395589231649323737 1496951546691923736992803)
              ·
                refine ⟨2245427320037885605489205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1496951546691923736992803 2245427320037885605489205)
                ·
                  refine ⟨210508811253551775514613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2245427320037885605489205 210508811253551775514613)
                  ·
                    rfl

theorem cell20_461210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 2, 1, 5].length) (baseStart_461210 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_461210 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_461210 prefixEnd_461210 := by exact prefixLift 461210
  have htrace : WordTrace (prefixWord ++ tailWord_461210) baseStart_461210 baseEnd_461210 := by
    simpa [prefixWord, tailWord_461210, baseEnd_461210] using wordTrace_append hprefix tailTrace_461210
  have hstable : (prefixWord ++ tailWord_461210).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_461210).length < 2 ^ (prefixWord ++ tailWord_461210).sum := by decide
  have hdescent : baseEnd_461210 < baseStart_461210 := by decide
  rcases family_descends (prefixWord ++ tailWord_461210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_461213 : List Nat := [1, 4, 2, 1, 4, 2, 1, 1, 4]
def baseStart_461213 : Nat := 118140960795 + 461213 * 2 ^ 59
def prefixEnd_461213 : Nat := 4983230072969 + 3 ^ 40 * 461213 * 2
def baseEnd_461213 : Nat := 210510180535297098414601

theorem tailTrace_461213 : CollatzResearch.WordTrace tailWord_461213 prefixEnd_461213 210510180535297098414601 := by
  unfold tailWord_461213
  simp only [CollatzResearch.WordTrace]
  refine ⟨16821820078111544754396293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11214546718741029836264195 16821820078111544754396293)
  ·
    refine ⟨3154091264645914641449305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16821820078111544754396293 3154091264645914641449305)
    ·
      refine ⟨2365568448484435981086979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3154091264645914641449305 2365568448484435981086979)
      ·
        refine ⟨3548352672726653971630469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2365568448484435981086979 3548352672726653971630469)
        ·
          refine ⟨665316126136247619680713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3548352672726653971630469 665316126136247619680713)
          ·
            refine ⟨498987094602185714760535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 665316126136247619680713 498987094602185714760535)
            ·
              refine ⟨748480641903278572140803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 498987094602185714760535 748480641903278572140803)
              ·
                refine ⟨1122720962854917858211205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 748480641903278572140803 1122720962854917858211205)
                ·
                  refine ⟨210510180535297098414601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1122720962854917858211205 210510180535297098414601)
                  ·
                    rfl

theorem cell20_461213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 2, 1, 1, 4].length) (baseStart_461213 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_461213 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_461213 prefixEnd_461213 := by exact prefixLift 461213
  have htrace : WordTrace (prefixWord ++ tailWord_461213) baseStart_461213 baseEnd_461213 := by
    simpa [prefixWord, tailWord_461213, baseEnd_461213] using wordTrace_append hprefix tailTrace_461213
  have hstable : (prefixWord ++ tailWord_461213).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_461213).length < 2 ^ (prefixWord ++ tailWord_461213).sum := by decide
  have hdescent : baseEnd_461213 < baseStart_461213 := by decide
  rcases family_descends (prefixWord ++ tailWord_461213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_461268 : List Nat := [2, 4, 1, 2, 2, 1, 4, 2, 2]
def baseStart_461268 : Nat := 118140960795 + 461268 * 2 ^ 59
def prefixEnd_461268 : Nat := 4983230072969 + 3 ^ 40 * 461268 * 2
def baseEnd_461268 : Nat := 210535284033961351581043

theorem tailTrace_461268 : CollatzResearch.WordTrace tailWord_461268 prefixEnd_461268 210535284033961351581043 := by
  unfold tailWord_461268
  simp only [CollatzResearch.WordTrace]
  refine ⟨8411913046456144573824229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11215884061941526098432305 8411913046456144573824229)
  ·
    refine ⟨1577233696210527107592043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8411913046456144573824229 1577233696210527107592043)
    ·
      refine ⟨2365850544315790661388065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1577233696210527107592043 2365850544315790661388065)
      ·
        refine ⟨1774387908236842996041049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2365850544315790661388065 1774387908236842996041049)
        ·
          refine ⟨1330790931177632247030787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1774387908236842996041049 1330790931177632247030787)
          ·
            refine ⟨1996186396766448370546181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1330790931177632247030787 1996186396766448370546181)
            ·
              refine ⟨374284949393709069477409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1996186396766448370546181 374284949393709069477409)
              ·
                refine ⟨280713712045281802108057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 374284949393709069477409 280713712045281802108057)
                ·
                  refine ⟨210535284033961351581043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 280713712045281802108057 210535284033961351581043)
                  ·
                    rfl

theorem cell20_461268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 4, 2, 2].length) (baseStart_461268 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_461268 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_461268 prefixEnd_461268 := by exact prefixLift 461268
  have htrace : WordTrace (prefixWord ++ tailWord_461268) baseStart_461268 baseEnd_461268 := by
    simpa [prefixWord, tailWord_461268, baseEnd_461268] using wordTrace_append hprefix tailTrace_461268
  have hstable : (prefixWord ++ tailWord_461268).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_461268).length < 2 ^ (prefixWord ++ tailWord_461268).sum := by decide
  have hdescent : baseEnd_461268 < baseStart_461268 := by decide
  rcases family_descends (prefixWord ++ tailWord_461268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_461279 : List Nat := [1, 1, 2, 3, 3, 4, 1, 5]
def baseStart_461279 : Nat := 118140960795 + 461279 * 2 ^ 59
def prefixEnd_461279 : Nat := 4983230072969 + 3 ^ 40 * 461279 * 2
def baseEnd_461279 : Nat := 70180101577898067404777

theorem tailTrace_461279 : CollatzResearch.WordTrace tailWord_461279 prefixEnd_461279 70180101577898067404777 := by
  unfold tailWord_461279
  simp only [CollatzResearch.WordTrace]
  refine ⟨16824227295872438026298891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11216151530581625350865927 16824227295872438026298891)
  ·
    refine ⟨25236340943808657039448337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16824227295872438026298891 25236340943808657039448337)
    ·
      refine ⟨18927255707856492779586253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25236340943808657039448337 18927255707856492779586253)
      ·
        refine ⟨7097720890446184792344845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18927255707856492779586253 7097720890446184792344845)
        ·
          refine ⟨2661645333917319297129317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7097720890446184792344845 2661645333917319297129317)
          ·
            refine ⟨499058500109497368211747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2661645333917319297129317 499058500109497368211747)
            ·
              refine ⟨748587750164246052317621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 499058500109497368211747 748587750164246052317621)
              ·
                refine ⟨70180101577898067404777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 748587750164246052317621 70180101577898067404777)
                ·
                  rfl

theorem cell20_461279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 4, 1, 5].length) (baseStart_461279 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_461279 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_461279 prefixEnd_461279 := by exact prefixLift 461279
  have htrace : WordTrace (prefixWord ++ tailWord_461279) baseStart_461279 baseEnd_461279 := by
    simpa [prefixWord, tailWord_461279, baseEnd_461279] using wordTrace_append hprefix tailTrace_461279
  have hstable : (prefixWord ++ tailWord_461279).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_461279).length < 2 ^ (prefixWord ++ tailWord_461279).sum := by decide
  have hdescent : baseEnd_461279 < baseStart_461279 := by decide
  rcases family_descends (prefixWord ++ tailWord_461279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_461324 : List Nat := [2, 2, 1, 2, 4, 2, 1, 1, 5]
def baseStart_461324 : Nat := 118140960795 + 461324 * 2 ^ 59
def prefixEnd_461324 : Nat := 4983230072969 + 3 ^ 40 * 461324 * 2
def baseEnd_461324 : Nat := 210560843959874045714147

theorem tailTrace_461324 : CollatzResearch.WordTrace tailWord_461324 prefixEnd_461324 210560843959874045714147 := by
  unfold tailWord_461324
  simp only [CollatzResearch.WordTrace]
  refine ⟨8412934290354705355843513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11217245720472940474458017 8412934290354705355843513)
  ·
    refine ⟨6309700717766029016882635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8412934290354705355843513 6309700717766029016882635)
    ·
      refine ⟨9464551076649043525323953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6309700717766029016882635 9464551076649043525323953)
      ·
        refine ⟨7098413307486782643992965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9464551076649043525323953 7098413307486782643992965)
        ·
          refine ⟨1330952495153771745748681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7098413307486782643992965 1330952495153771745748681)
          ·
            refine ⟨998214371365328809311511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1330952495153771745748681 998214371365328809311511)
            ·
              refine ⟨1497321557047993213967267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 998214371365328809311511 1497321557047993213967267)
              ·
                refine ⟨2245982335571989820950901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1497321557047993213967267 2245982335571989820950901)
                ·
                  refine ⟨210560843959874045714147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2245982335571989820950901 210560843959874045714147)
                  ·
                    rfl

theorem cell20_461324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 2, 1, 1, 5].length) (baseStart_461324 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_461324 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_461324 prefixEnd_461324 := by exact prefixLift 461324
  have htrace : WordTrace (prefixWord ++ tailWord_461324) baseStart_461324 baseEnd_461324 := by
    simpa [prefixWord, tailWord_461324, baseEnd_461324] using wordTrace_append hprefix tailTrace_461324
  have hstable : (prefixWord ++ tailWord_461324).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_461324).length < 2 ^ (prefixWord ++ tailWord_461324).sum := by decide
  have hdescent : baseEnd_461324 < baseStart_461324 := by decide
  rcases family_descends (prefixWord ++ tailWord_461324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_461331 : List Nat := [1, 1, 1, 2, 1, 5, 4, 1, 4]
def baseStart_461331 : Nat := 118140960795 + 461331 * 2 ^ 59
def prefixEnd_461331 : Nat := 4983230072969 + 3 ^ 40 * 461331 * 2
def baseEnd_461331 : Nat := 210564038950613132480785

theorem tailTrace_461331 : CollatzResearch.WordTrace tailWord_461331 prefixEnd_461331 210564038950613132480785 := by
  unfold tailWord_461331
  simp only [CollatzResearch.WordTrace]
  refine ⟨16826123891684050907191847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11217415927789367271461231 16826123891684050907191847)
  ·
    refine ⟨25239185837526076360787771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16826123891684050907191847 25239185837526076360787771)
    ·
      refine ⟨37858778756289114541181657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25239185837526076360787771 37858778756289114541181657)
      ·
        refine ⟨28394084067216835905886243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37858778756289114541181657 28394084067216835905886243)
        ·
          refine ⟨42591126100825253858829365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28394084067216835905886243 42591126100825253858829365)
          ·
            refine ⟨3992918071952367549265253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 42591126100825253858829365 3992918071952367549265253)
            ·
              refine ⟨748672138491068915487235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3992918071952367549265253 748672138491068915487235)
              ·
                refine ⟨1123008207736603373230853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 748672138491068915487235 1123008207736603373230853)
                ·
                  refine ⟨210564038950613132480785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1123008207736603373230853 210564038950613132480785)
                  ·
                    rfl

theorem cell20_461331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 4, 1, 4].length) (baseStart_461331 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_461331 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_461331 prefixEnd_461331 := by exact prefixLift 461331
  have htrace : WordTrace (prefixWord ++ tailWord_461331) baseStart_461331 baseEnd_461331 := by
    simpa [prefixWord, tailWord_461331, baseEnd_461331] using wordTrace_append hprefix tailTrace_461331
  have hstable : (prefixWord ++ tailWord_461331).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_461331).length < 2 ^ (prefixWord ++ tailWord_461331).sum := by decide
  have hdescent : baseEnd_461331 < baseStart_461331 := by decide
  rcases family_descends (prefixWord ++ tailWord_461331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_461357 : List Nat := [1, 5, 4, 1, 2, 1, 1, 3, 2]
def baseStart_461357 : Nat := 118140960795 + 461357 * 2 ^ 59
def prefixEnd_461357 : Nat := 4983230072969 + 3 ^ 40 * 461357 * 2
def baseEnd_461357 : Nat := 210575906059072597614013

theorem tailTrace_461357 : CollatzResearch.WordTrace tailWord_461357 prefixEnd_461357 210575906059072597614013 := by
  unfold tailWord_461357
  simp only [CollatzResearch.WordTrace]
  refine ⟨16827072189589857347638325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11218048126393238231758883 16827072189589857347638325)
  ·
    refine ⟨1577538017774049126341093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 16827072189589857347638325 1577538017774049126341093)
    ·
      refine ⟨295788378332634211188955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1577538017774049126341093 295788378332634211188955)
      ·
        refine ⟨443682567498951316783433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 295788378332634211188955 443682567498951316783433)
        ·
          refine ⟨332761925624213487587575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 443682567498951316783433 332761925624213487587575)
          ·
            refine ⟨499142888436320231381363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 332761925624213487587575 499142888436320231381363)
            ·
              refine ⟨748714332654480347072045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 499142888436320231381363 748714332654480347072045)
              ·
                refine ⟨280767874745430130152017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 748714332654480347072045 280767874745430130152017)
                ·
                  refine ⟨210575906059072597614013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 280767874745430130152017 210575906059072597614013)
                  ·
                    rfl

theorem cell20_461357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 2, 1, 1, 3, 2].length) (baseStart_461357 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_461357 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_461357 prefixEnd_461357 := by exact prefixLift 461357
  have htrace : WordTrace (prefixWord ++ tailWord_461357) baseStart_461357 baseEnd_461357 := by
    simpa [prefixWord, tailWord_461357, baseEnd_461357] using wordTrace_append hprefix tailTrace_461357
  have hstable : (prefixWord ++ tailWord_461357).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_461357).length < 2 ^ (prefixWord ++ tailWord_461357).sum := by decide
  have hdescent : baseEnd_461357 < baseStart_461357 := by decide
  rcases family_descends (prefixWord ++ tailWord_461357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_461382 : List Nat := [6, 1, 1, 1, 2, 3, 1, 1, 4]
def baseStart_461382 : Nat := 118140960795 + 461382 * 2 ^ 59
def prefixEnd_461382 : Nat := 4983230072969 + 3 ^ 40 * 461382 * 2
def baseEnd_461382 : Nat := 210587316740283621780577

theorem tailTrace_461382 : CollatzResearch.WordTrace tailWord_461382 prefixEnd_461382 210587316740283621780577 := by
  unfold tailWord_461382
  simp only [CollatzResearch.WordTrace]
  refine ⟨525874500453102706790575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 11218656009666191078198933 525874500453102706790575)
  ·
    refine ⟨788811750679654060185863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 525874500453102706790575 788811750679654060185863)
    ·
      refine ⟨1183217626019481090278795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 788811750679654060185863 1183217626019481090278795)
      ·
        refine ⟨1774826439029221635418193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1183217626019481090278795 1774826439029221635418193)
        ·
          refine ⟨1331119829271916226563645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1774826439029221635418193 1331119829271916226563645)
          ·
            refine ⟨499169935976968584961367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1331119829271916226563645 499169935976968584961367)
            ·
              refine ⟨748754903965452877442051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 499169935976968584961367 748754903965452877442051)
              ·
                refine ⟨1123132355948179316163077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 748754903965452877442051 1123132355948179316163077)
                ·
                  refine ⟨210587316740283621780577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1123132355948179316163077 210587316740283621780577)
                  ·
                    rfl

theorem cell20_461382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 3, 1, 1, 4].length) (baseStart_461382 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_461382 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_461382 prefixEnd_461382 := by exact prefixLift 461382
  have htrace : WordTrace (prefixWord ++ tailWord_461382) baseStart_461382 baseEnd_461382 := by
    simpa [prefixWord, tailWord_461382, baseEnd_461382] using wordTrace_append hprefix tailTrace_461382
  have hstable : (prefixWord ++ tailWord_461382).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_461382).length < 2 ^ (prefixWord ++ tailWord_461382).sum := by decide
  have hdescent : baseEnd_461382 < baseStart_461382 := by decide
  rcases family_descends (prefixWord ++ tailWord_461382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_461386 : List Nat := [3, 1, 2, 1, 1, 6, 1, 1, 4]
def baseStart_461386 : Nat := 118140960795 + 461386 * 2 ^ 59
def prefixEnd_461386 : Nat := 4983230072969 + 3 ^ 40 * 461386 * 2
def baseEnd_461386 : Nat := 210589142449277385647227

theorem tailTrace_461386 : CollatzResearch.WordTrace tailWord_461386 prefixEnd_461386 210589142449277385647227 := by
  unfold tailWord_461386
  simp only [CollatzResearch.WordTrace]
  refine ⟨4207032476621198825111003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11218753270989863533629341 4207032476621198825111003)
  ·
    refine ⟨6310548714931798237666505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4207032476621198825111003 6310548714931798237666505)
    ·
      refine ⟨4732911536198848678249879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6310548714931798237666505 4732911536198848678249879)
      ·
        refine ⟨7099367304298273017374819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4732911536198848678249879 7099367304298273017374819)
        ·
          refine ⟨10649050956447409526062229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7099367304298273017374819 10649050956447409526062229)
          ·
            refine ⟨499174263583472321534167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 10649050956447409526062229 499174263583472321534167)
            ·
              refine ⟨748761395375208482301251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 499174263583472321534167 748761395375208482301251)
              ·
                refine ⟨1123142093062812723451877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 748761395375208482301251 1123142093062812723451877)
                ·
                  refine ⟨210589142449277385647227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1123142093062812723451877 210589142449277385647227)
                  ·
                    rfl

theorem cell20_461386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 6, 1, 1, 4].length) (baseStart_461386 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_461386 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_461386 prefixEnd_461386 := by exact prefixLift 461386
  have htrace : WordTrace (prefixWord ++ tailWord_461386) baseStart_461386 baseEnd_461386 := by
    simpa [prefixWord, tailWord_461386, baseEnd_461386] using wordTrace_append hprefix tailTrace_461386
  have hstable : (prefixWord ++ tailWord_461386).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_461386).length < 2 ^ (prefixWord ++ tailWord_461386).sum := by decide
  have hdescent : baseEnd_461386 < baseStart_461386 := by decide
  rcases family_descends (prefixWord ++ tailWord_461386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_461396 : List Nat := [2, 4, 1, 1, 1, 5, 2, 1, 3]
def baseStart_461396 : Nat := 118140960795 + 461396 * 2 ^ 59
def prefixEnd_461396 : Nat := 4983230072969 + 3 ^ 40 * 461396 * 2
def baseEnd_461396 : Nat := 210593706721761795313853

theorem tailTrace_461396 : CollatzResearch.WordTrace tailWord_461396 prefixEnd_461396 210593706721761795313853 := by
  unfold tailWord_461396
  simp only [CollatzResearch.WordTrace]
  refine ⟨8414247318224283504154021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11218996424299044672205361 8414247318224283504154021)
  ·
    refine ⟨1577671372167053157028879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8414247318224283504154021 1577671372167053157028879)
    ·
      refine ⟨2366507058250579735543319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1577671372167053157028879 2366507058250579735543319)
      ·
        refine ⟨3549760587375869603314979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2366507058250579735543319 3549760587375869603314979)
        ·
          refine ⟨5324640881063804404972469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3549760587375869603314979 5324640881063804404972469)
          ·
            refine ⟨499185082599731662966169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 5324640881063804404972469 499185082599731662966169)
            ·
              refine ⟨374388811949798747224627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 499185082599731662966169 374388811949798747224627)
              ·
                refine ⟨561583217924698120836941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 374388811949798747224627 561583217924698120836941)
                ·
                  refine ⟨210593706721761795313853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 561583217924698120836941 210593706721761795313853)
                  ·
                    rfl

theorem cell20_461396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 5, 2, 1, 3].length) (baseStart_461396 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_461396 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_461396 prefixEnd_461396 := by exact prefixLift 461396
  have htrace : WordTrace (prefixWord ++ tailWord_461396) baseStart_461396 baseEnd_461396 := by
    simpa [prefixWord, tailWord_461396, baseEnd_461396] using wordTrace_append hprefix tailTrace_461396
  have hstable : (prefixWord ++ tailWord_461396).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_461396).length < 2 ^ (prefixWord ++ tailWord_461396).sum := by decide
  have hdescent : baseEnd_461396 < baseStart_461396 := by decide
  rcases family_descends (prefixWord ++ tailWord_461396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_461437 : List Nat := [1, 4, 1, 1, 6, 1, 2, 2, 2]
def baseStart_461437 : Nat := 118140960795 + 461437 * 2 ^ 59
def prefixEnd_461437 : Nat := 4983230072969 + 3 ^ 40 * 461437 * 2
def baseEnd_461437 : Nat := 210612420238947874947019

theorem tailTrace_461437 : CollatzResearch.WordTrace tailWord_461437 prefixEnd_461437 210612420238947874947019 := by
  unfold tailWord_461437
  simp only [CollatzResearch.WordTrace]
  refine ⟨16829990029300031010550565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11219993352866687340367043 16829990029300031010550565)
  ·
    refine ⟨3155623130493755814478231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16829990029300031010550565 3155623130493755814478231)
    ·
      refine ⟨4733434695740633721717347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3155623130493755814478231 4733434695740633721717347)
      ·
        refine ⟨7100152043610950582576021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4733434695740633721717347 7100152043610950582576021)
        ·
          refine ⟨332819627044263308558251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 7100152043610950582576021 332819627044263308558251)
          ·
            refine ⟨499229440566394962837377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 332819627044263308558251 499229440566394962837377)
            ·
              refine ⟨374422080424796222128033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 499229440566394962837377 374422080424796222128033)
              ·
                refine ⟨280816560318597166596025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 374422080424796222128033 280816560318597166596025)
                ·
                  refine ⟨210612420238947874947019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 280816560318597166596025 210612420238947874947019)
                  ·
                    rfl

theorem cell20_461437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 6, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 6, 1, 2, 2, 2].length) (baseStart_461437 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_461437 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_461437 prefixEnd_461437 := by exact prefixLift 461437
  have htrace : WordTrace (prefixWord ++ tailWord_461437) baseStart_461437 baseEnd_461437 := by
    simpa [prefixWord, tailWord_461437, baseEnd_461437] using wordTrace_append hprefix tailTrace_461437
  have hstable : (prefixWord ++ tailWord_461437).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_461437).length < 2 ^ (prefixWord ++ tailWord_461437).sum := by decide
  have hdescent : baseEnd_461437 < baseStart_461437 := by decide
  rcases family_descends (prefixWord ++ tailWord_461437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_461489 : List Nat := [1, 2, 2, 6, 2, 1, 1, 2, 3]
def baseStart_461489 : Nat := 118140960795 + 461489 * 2 ^ 59
def prefixEnd_461489 : Nat := 4983230072969 + 3 ^ 40 * 461489 * 2
def baseEnd_461489 : Nat := 210636154455866805213473

theorem tailTrace_461489 : CollatzResearch.WordTrace tailWord_461489 prefixEnd_461489 210636154455866805213473 := by
  unfold tailWord_461489
  simp only [CollatzResearch.WordTrace]
  refine ⟨16831886625111643891443521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11221257750074429260962347 16831886625111643891443521)
  ·
    refine ⟨12623914968833732918582641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16831886625111643891443521 12623914968833732918582641)
    ·
      refine ⟨9467936226625299688936981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12623914968833732918582641 9467936226625299688936981)
      ·
        refine ⟨443809510623060922918921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 9467936226625299688936981 443809510623060922918921)
        ·
          refine ⟨332857132967295692189191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 443809510623060922918921 332857132967295692189191)
          ·
            refine ⟨499285699450943538283787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 332857132967295692189191 499285699450943538283787)
            ·
              refine ⟨748928549176415307425681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 499285699450943538283787 748928549176415307425681)
              ·
                refine ⟨561696411882311480569261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 748928549176415307425681 561696411882311480569261)
                ·
                  refine ⟨210636154455866805213473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 561696411882311480569261 210636154455866805213473)
                  ·
                    rfl

theorem cell20_461489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 2, 1, 1, 2, 3].length) (baseStart_461489 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_461489 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_461489 prefixEnd_461489 := by exact prefixLift 461489
  have htrace : WordTrace (prefixWord ++ tailWord_461489) baseStart_461489 baseEnd_461489 := by
    simpa [prefixWord, tailWord_461489, baseEnd_461489] using wordTrace_append hprefix tailTrace_461489
  have hstable : (prefixWord ++ tailWord_461489).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_461489).length < 2 ^ (prefixWord ++ tailWord_461489).sum := by decide
  have hdescent : baseEnd_461489 < baseStart_461489 := by decide
  rcases family_descends (prefixWord ++ tailWord_461489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_461493 : List Nat := [1, 3, 3, 3, 1, 1, 3, 2, 3]
def baseStart_461493 : Nat := 118140960795 + 461493 * 2 ^ 59
def prefixEnd_461493 : Nat := 4983230072969 + 3 ^ 40 * 461493 * 2
def baseEnd_461493 : Nat := 210637980164860569080123

theorem tailTrace_461493 : CollatzResearch.WordTrace tailWord_461493 prefixEnd_461493 210637980164860569080123 := by
  unfold tailWord_461493
  simp only [CollatzResearch.WordTrace]
  refine ⟨16832032517097152574589133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11221355011398101716392755 16832032517097152574589133)
  ·
    refine ⟨6312012193911432215470925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16832032517097152574589133 6312012193911432215470925)
    ·
      refine ⟨2367004572716787080801597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6312012193911432215470925 2367004572716787080801597)
      ·
        refine ⟨887626714768795155300599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2367004572716787080801597 887626714768795155300599)
        ·
          refine ⟨1331440072153192732950899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 887626714768795155300599 1331440072153192732950899)
          ·
            refine ⟨1997160108229789099426349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1331440072153192732950899 1997160108229789099426349)
            ·
              refine ⟨748935040586170912284881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1997160108229789099426349 748935040586170912284881)
              ·
                refine ⟨561701280439628184213661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 748935040586170912284881 561701280439628184213661)
                ·
                  refine ⟨210637980164860569080123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 561701280439628184213661 210637980164860569080123)
                  ·
                    rfl

theorem cell20_461493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 3, 2, 3].length) (baseStart_461493 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_461493 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_461493 prefixEnd_461493 := by exact prefixLift 461493
  have htrace : WordTrace (prefixWord ++ tailWord_461493) baseStart_461493 baseEnd_461493 := by
    simpa [prefixWord, tailWord_461493, baseEnd_461493] using wordTrace_append hprefix tailTrace_461493
  have hstable : (prefixWord ++ tailWord_461493).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_461493).length < 2 ^ (prefixWord ++ tailWord_461493).sum := by decide
  have hdescent : baseEnd_461493 < baseStart_461493 := by decide
  rcases family_descends (prefixWord ++ tailWord_461493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_461500 : List Nat := [2, 2, 2, 3, 1, 1, 1, 6, 2]
def baseStart_461500 : Nat := 118140960795 + 461500 * 2 ^ 59
def prefixEnd_461500 : Nat := 4983230072969 + 3 ^ 40 * 461500 * 2
def baseEnd_461500 : Nat := 210641175155599655846761

theorem tailTrace_461500 : CollatzResearch.WordTrace tailWord_461500 prefixEnd_461500 210641175155599655846761 := by
  unfold tailWord_461500
  simp only [CollatzResearch.WordTrace]
  refine ⟨8416143914035896385046977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11221525218714528513395969 8416143914035896385046977)
  ·
    refine ⟨6312107935526922288785233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8416143914035896385046977 6312107935526922288785233)
    ·
      refine ⟨4734080951645191716588925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6312107935526922288785233 4734080951645191716588925)
      ·
        refine ⟨1775280356866946893720847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4734080951645191716588925 1775280356866946893720847)
        ·
          refine ⟨2662920535300420340581271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1775280356866946893720847 2662920535300420340581271)
          ·
            refine ⟨3994380802950630510871907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2662920535300420340581271 3994380802950630510871907)
            ·
              refine ⟨5991571204425945766307861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3994380802950630510871907 5991571204425945766307861)
              ·
                refine ⟨280854900207466207795681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 5991571204425945766307861 280854900207466207795681)
                ·
                  refine ⟨210641175155599655846761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 280854900207466207795681 210641175155599655846761)
                  ·
                    rfl

theorem cell20_461500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 1, 6, 2].length) (baseStart_461500 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_461500 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_461500 prefixEnd_461500 := by exact prefixLift 461500
  have htrace : WordTrace (prefixWord ++ tailWord_461500) baseStart_461500 baseEnd_461500 := by
    simpa [prefixWord, tailWord_461500, baseEnd_461500] using wordTrace_append hprefix tailTrace_461500
  have hstable : (prefixWord ++ tailWord_461500).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_461500).length < 2 ^ (prefixWord ++ tailWord_461500).sum := by decide
  have hdescent : baseEnd_461500 < baseStart_461500 := by decide
  rcases family_descends (prefixWord ++ tailWord_461500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_461528 : List Nat := [2, 1, 2, 2, 3, 3, 1, 6]
def baseStart_461528 : Nat := 118140960795 + 461528 * 2 ^ 59
def prefixEnd_461528 : Nat := 4983230072969 + 3 ^ 40 * 461528 * 2
def baseEnd_461528 : Nat := 70217985039518667637771

theorem tailTrace_461528 : CollatzResearch.WordTrace tailWord_461528 prefixEnd_461528 70217985039518667637771 := by
  unfold tailWord_461528
  simp only [CollatzResearch.WordTrace]
  refine ⟨8416654535985176776056619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11222206047980235701408825 8416654535985176776056619)
  ·
    refine ⟨12624981803977765164084929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8416654535985176776056619 12624981803977765164084929)
    ·
      refine ⟨9468736352983323873063697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12624981803977765164084929 9468736352983323873063697)
      ·
        refine ⟨7101552264737492904797773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9468736352983323873063697 7101552264737492904797773)
        ·
          refine ⟨2663082099276559839299165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7101552264737492904797773 2663082099276559839299165)
          ·
            refine ⟨998655787228709939737187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2663082099276559839299165 998655787228709939737187)
            ·
              refine ⟨1497983680843064909605781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 998655787228709939737187 1497983680843064909605781)
              ·
                refine ⟨70217985039518667637771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1497983680843064909605781 70217985039518667637771)
                ·
                  rfl

theorem cell20_461528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 3, 1, 6].length) (baseStart_461528 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_461528 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_461528 prefixEnd_461528 := by exact prefixLift 461528
  have htrace : WordTrace (prefixWord ++ tailWord_461528) baseStart_461528 baseEnd_461528 := by
    simpa [prefixWord, tailWord_461528, baseEnd_461528] using wordTrace_append hprefix tailTrace_461528
  have hstable : (prefixWord ++ tailWord_461528).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_461528).length < 2 ^ (prefixWord ++ tailWord_461528).sum := by decide
  have hdescent : baseEnd_461528 < baseStart_461528 := by decide
  rcases family_descends (prefixWord ++ tailWord_461528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_461535 : List Nat := [1, 1, 2, 3, 2, 3, 1, 2, 5]
def baseStart_461535 : Nat := 118140960795 + 461535 * 2 ^ 59
def prefixEnd_461535 : Nat := 4983230072969 + 3 ^ 40 * 461535 * 2
def baseEnd_461535 : Nat := 210657150109295089679951

theorem tailTrace_461535 : CollatzResearch.WordTrace tailWord_461535 prefixEnd_461535 210657150109295089679951 := by
  unfold tailWord_461535
  simp only [CollatzResearch.WordTrace]
  refine ⟨16833564382944993747618059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11222376255296662498412039 16833564382944993747618059)
  ·
    refine ⟨25250346574417490621427089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16833564382944993747618059 25250346574417490621427089)
    ·
      refine ⟨18937759930813117966070317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25250346574417490621427089 18937759930813117966070317)
      ·
        refine ⟨7101659974054919237276369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18937759930813117966070317 7101659974054919237276369)
        ·
          refine ⟨5326244980541189427957277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7101659974054919237276369 5326244980541189427957277)
          ·
            refine ⟨1997341867702946035483979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5326244980541189427957277 1997341867702946035483979)
            ·
              refine ⟨2996012801554419053225969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1997341867702946035483979 2996012801554419053225969)
              ·
                refine ⟨2247009601165814289919477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2996012801554419053225969 2247009601165814289919477)
                ·
                  refine ⟨210657150109295089679951, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2247009601165814289919477 210657150109295089679951)
                  ·
                    rfl

theorem cell20_461535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 1, 2, 5].length) (baseStart_461535 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_461535 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_461535 prefixEnd_461535 := by exact prefixLift 461535
  have htrace : WordTrace (prefixWord ++ tailWord_461535) baseStart_461535 baseEnd_461535 := by
    simpa [prefixWord, tailWord_461535, baseEnd_461535] using wordTrace_append hprefix tailTrace_461535
  have hstable : (prefixWord ++ tailWord_461535).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_461535).length < 2 ^ (prefixWord ++ tailWord_461535).sum := by decide
  have hdescent : baseEnd_461535 < baseStart_461535 := by decide
  rcases family_descends (prefixWord ++ tailWord_461535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_461580 : List Nat := [2, 2, 1, 2, 2, 1, 1, 3, 6]
def baseStart_461580 : Nat := 118140960795 + 461580 * 2 ^ 59
def prefixEnd_461580 : Nat := 4983230072969 + 3 ^ 40 * 461580 * 2
def baseEnd_461580 : Nat := 210677689335474933179767

theorem tailTrace_461580 : CollatzResearch.WordTrace tailWord_461580 prefixEnd_461580 210677689335474933179767 := by
  unfold tailWord_461580
  simp only [CollatzResearch.WordTrace]
  refine ⟨8417602833890983216503097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11223470445187977622004129 8417602833890983216503097)
  ·
    refine ⟨6313202125418237412377323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8417602833890983216503097 6313202125418237412377323)
    ·
      refine ⟨9469803188127356118565985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6313202125418237412377323 9469803188127356118565985)
      ·
        refine ⟨7102352391095517088924489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9469803188127356118565985 7102352391095517088924489)
        ·
          refine ⟨5326764293321637816693367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7102352391095517088924489 5326764293321637816693367)
          ·
            refine ⟨7990146439982456725040051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5326764293321637816693367 7990146439982456725040051)
            ·
              refine ⟨11985219659973685087560077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7990146439982456725040051 11985219659973685087560077)
              ·
                refine ⟨4494457372490131907835029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11985219659973685087560077 4494457372490131907835029)
                ·
                  refine ⟨210677689335474933179767, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4494457372490131907835029 210677689335474933179767)
                  ·
                    rfl

theorem cell20_461580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 3, 6].length) (baseStart_461580 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_461580 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_461580 prefixEnd_461580 := by exact prefixLift 461580
  have htrace : WordTrace (prefixWord ++ tailWord_461580) baseStart_461580 baseEnd_461580 := by
    simpa [prefixWord, tailWord_461580, baseEnd_461580] using wordTrace_append hprefix tailTrace_461580
  have hstable : (prefixWord ++ tailWord_461580).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_461580).length < 2 ^ (prefixWord ++ tailWord_461580).sum := by decide
  have hdescent : baseEnd_461580 < baseStart_461580 := by decide
  rcases family_descends (prefixWord ++ tailWord_461580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_461587 : List Nat := [1, 1, 1, 2, 1, 3, 3, 8]
def baseStart_461587 : Nat := 118140960795 + 461587 * 2 ^ 59
def prefixEnd_461587 : Nat := 4983230072969 + 3 ^ 40 * 461587 * 2
def baseEnd_461587 : Nat := 70226961442071339982135

theorem tailTrace_461587 : CollatzResearch.WordTrace tailWord_461587 prefixEnd_461587 70226961442071339982135 := by
  unfold tailWord_461587
  simp only [CollatzResearch.WordTrace]
  refine ⟨16835460978756606628511015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11223640652504404419007343 16835460978756606628511015)
  ·
    refine ⟨25253191468134909942766523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16835460978756606628511015 25253191468134909942766523)
    ·
      refine ⟨37879787202202364914149785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25253191468134909942766523 37879787202202364914149785)
      ·
        refine ⟨28409840401651773685612339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37879787202202364914149785 28409840401651773685612339)
        ·
          refine ⟨42614760602477660528418509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28409840401651773685612339 42614760602477660528418509)
          ·
            refine ⟨15980535225929122698156941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42614760602477660528418509 15980535225929122698156941)
            ·
              refine ⟨5992700709723421011808853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15980535225929122698156941 5992700709723421011808853)
              ·
                refine ⟨70226961442071339982135, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5992700709723421011808853 70226961442071339982135)
                ·
                  rfl

theorem cell20_461587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 3, 8].length) (baseStart_461587 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_461587 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_461587 prefixEnd_461587 := by exact prefixLift 461587
  have htrace : WordTrace (prefixWord ++ tailWord_461587) baseStart_461587 baseEnd_461587 := by
    simpa [prefixWord, tailWord_461587, baseEnd_461587] using wordTrace_append hprefix tailTrace_461587
  have hstable : (prefixWord ++ tailWord_461587).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_461587).length < 2 ^ (prefixWord ++ tailWord_461587).sum := by decide
  have hdescent : baseEnd_461587 < baseStart_461587 := by decide
  rcases family_descends (prefixWord ++ tailWord_461587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_461604 : List Nat := [2, 3, 1, 3, 3, 8]
def baseStart_461604 : Nat := 118140960795 + 461604 * 2 ^ 59
def prefixEnd_461604 : Nat := 4983230072969 + 3 ^ 40 * 461604 * 2
def baseEnd_461604 : Nat := 7803283095905093199247

theorem tailTrace_461604 : CollatzResearch.WordTrace tailWord_461604 prefixEnd_461604 7803283095905093199247 := by
  unfold tailWord_461604
  simp only [CollatzResearch.WordTrace]
  refine ⟨8418040509847509265939933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11224054013130012354586577 8418040509847509265939933)
  ·
    refine ⟨3156765191192815974727475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8418040509847509265939933 3156765191192815974727475)
    ·
      refine ⟨4735147786789223962091213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3156765191192815974727475 4735147786789223962091213)
      ·
        refine ⟨1775680420045958985784205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4735147786789223962091213 1775680420045958985784205)
        ·
          refine ⟨665880157517234619669077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1775680420045958985784205 665880157517234619669077)
          ·
            refine ⟨7803283095905093199247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 665880157517234619669077 7803283095905093199247)
            ·
              rfl

theorem cell20_461604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 8].length) (baseStart_461604 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_461604 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_461604 prefixEnd_461604 := by exact prefixLift 461604
  have htrace : WordTrace (prefixWord ++ tailWord_461604) baseStart_461604 baseEnd_461604 := by
    simpa [prefixWord, tailWord_461604, baseEnd_461604] using wordTrace_append hprefix tailTrace_461604
  have hstable : (prefixWord ++ tailWord_461604).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_461604).length < 2 ^ (prefixWord ++ tailWord_461604).sum := by decide
  have hdescent : baseEnd_461604 < baseStart_461604 := by decide
  rcases family_descends (prefixWord ++ tailWord_461604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_461610 : List Nat := [3, 1, 4, 3, 1, 1, 1, 4, 2]
def baseStart_461610 : Nat := 118140960795 + 461610 * 2 ^ 59
def prefixEnd_461610 : Nat := 4983230072969 + 3 ^ 40 * 461610 * 2
def baseEnd_461610 : Nat := 210691382152928162179645

theorem tailTrace_461610 : CollatzResearch.WordTrace tailWord_461610 prefixEnd_461610 210691382152928162179645 := by
  unfold tailWord_461610
  simp only [CollatzResearch.WordTrace]
  refine ⟨4209074964418320389149571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11224199905115521037732189 4209074964418320389149571)
  ·
    refine ⟨6313612446627480583724357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4209074964418320389149571 6313612446627480583724357)
    ·
      refine ⟨1183802333742652609448317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6313612446627480583724357 1183802333742652609448317)
      ·
        refine ⟨443925875153494728543119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1183802333742652609448317 443925875153494728543119)
        ·
          refine ⟨665888812730242092814679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 443925875153494728543119 665888812730242092814679)
          ·
            refine ⟨998833219095363139222019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 665888812730242092814679 998833219095363139222019)
            ·
              refine ⟨1498249828643044708833029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 998833219095363139222019 1498249828643044708833029)
              ·
                refine ⟨280921842870570882906193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1498249828643044708833029 280921842870570882906193)
                ·
                  refine ⟨210691382152928162179645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 280921842870570882906193 210691382152928162179645)
                  ·
                    rfl

theorem cell20_461610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 1, 1, 4, 2].length) (baseStart_461610 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_461610 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_461610 prefixEnd_461610 := by exact prefixLift 461610
  have htrace : WordTrace (prefixWord ++ tailWord_461610) baseStart_461610 baseEnd_461610 := by
    simpa [prefixWord, tailWord_461610, baseEnd_461610] using wordTrace_append hprefix tailTrace_461610
  have hstable : (prefixWord ++ tailWord_461610).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_461610).length < 2 ^ (prefixWord ++ tailWord_461610).sum := by decide
  have hdescent : baseEnd_461610 < baseStart_461610 := by decide
  rcases family_descends (prefixWord ++ tailWord_461610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_461611 : List Nat := [1, 1, 1, 1, 2, 1, 2, 8, 3]
def baseStart_461611 : Nat := 118140960795 + 461611 * 2 ^ 59
def prefixEnd_461611 : Nat := 4983230072969 + 3 ^ 40 * 461611 * 2
def baseEnd_461611 : Nat := 210691838580176603146307

theorem tailTrace_461611 : CollatzResearch.WordTrace tailWord_461611 prefixEnd_461611 210691838580176603146307 := by
  unfold tailWord_461611
  simp only [CollatzResearch.WordTrace]
  refine ⟨16836336330669658727384687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11224224220446439151589791 16836336330669658727384687)
  ·
    refine ⟨25254504496004488091077031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16836336330669658727384687 25254504496004488091077031)
    ·
      refine ⟨37881756744006732136615547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25254504496004488091077031 37881756744006732136615547)
      ·
        refine ⟨56822635116010098204923321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37881756744006732136615547 56822635116010098204923321)
        ·
          refine ⟨42616976337007573653692491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56822635116010098204923321 42616976337007573653692491)
          ·
            refine ⟨63925464505511360480538737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42616976337007573653692491 63925464505511360480538737)
            ·
              refine ⟨47944098379133520360404053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63925464505511360480538737 47944098379133520360404053)
              ·
                refine ⟨561844902880470941723485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 47944098379133520360404053 561844902880470941723485)
                ·
                  refine ⟨210691838580176603146307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 561844902880470941723485 210691838580176603146307)
                  ·
                    rfl

theorem cell20_461611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 8, 3].length) (baseStart_461611 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_461611 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_461611 prefixEnd_461611 := by exact prefixLift 461611
  have htrace : WordTrace (prefixWord ++ tailWord_461611) baseStart_461611 baseEnd_461611 := by
    simpa [prefixWord, tailWord_461611, baseEnd_461611] using wordTrace_append hprefix tailTrace_461611
  have hstable : (prefixWord ++ tailWord_461611).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_461611).length < 2 ^ (prefixWord ++ tailWord_461611).sum := by decide
  have hdescent : baseEnd_461611 < baseStart_461611 := by decide
  rcases family_descends (prefixWord ++ tailWord_461611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_461621 : List Nat := [1, 3, 3, 1, 3, 3, 1, 5]
def baseStart_461621 : Nat := 118140960795 + 461621 * 2 ^ 59
def prefixEnd_461621 : Nat := 4983230072969 + 3 ^ 40 * 461621 * 2
def baseEnd_461621 : Nat := 70232134284220337604311

theorem tailTrace_461621 : CollatzResearch.WordTrace tailWord_461621 prefixEnd_461621 70232134284220337604311 := by
  unfold tailWord_461621
  simp only [CollatzResearch.WordTrace]
  refine ⟨16836701060633430435248717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11224467373755620290165811 16836701060633430435248717)
  ·
    refine ⟨6313762897737536413218269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16836701060633430435248717 6313762897737536413218269)
    ·
      refine ⟨2367661086651576154956851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6313762897737536413218269 2367661086651576154956851)
      ·
        refine ⟨3551491629977364232435277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2367661086651576154956851 3551491629977364232435277)
        ·
          refine ⟨1331809361241511587163229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3551491629977364232435277 1331809361241511587163229)
          ·
            refine ⟨499428510465566845186211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1331809361241511587163229 499428510465566845186211)
            ·
              refine ⟨749142765698350267779317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 499428510465566845186211 749142765698350267779317)
              ·
                refine ⟨70232134284220337604311, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 749142765698350267779317 70232134284220337604311)
                ·
                  rfl

theorem cell20_461621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 3, 1, 5].length) (baseStart_461621 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_461621 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_461621 prefixEnd_461621 := by exact prefixLift 461621
  have htrace : WordTrace (prefixWord ++ tailWord_461621) baseStart_461621 baseEnd_461621 := by
    simpa [prefixWord, tailWord_461621, baseEnd_461621] using wordTrace_append hprefix tailTrace_461621
  have hstable : (prefixWord ++ tailWord_461621).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_461621).length < 2 ^ (prefixWord ++ tailWord_461621).sum := by decide
  have hdescent : baseEnd_461621 < baseStart_461621 := by decide
  rcases family_descends (prefixWord ++ tailWord_461621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_461663 : List Nat := [1, 1, 2, 3, 1, 3, 9]
def baseStart_461663 : Nat := 118140960795 + 461663 * 2 ^ 59
def prefixEnd_461663 : Nat := 4983230072969 + 3 ^ 40 * 461663 * 2
def baseEnd_461663 : Nat := 23412841421899503712529

theorem tailTrace_461663 : CollatzResearch.WordTrace tailWord_461663 prefixEnd_461663 23412841421899503712529 := by
  unfold tailWord_461663
  simp only [CollatzResearch.WordTrace]
  refine ⟨16838232926481271608277643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11225488617654181072185095 16838232926481271608277643)
  ·
    refine ⟨25257349389721907412416465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16838232926481271608277643 25257349389721907412416465)
    ·
      refine ⟨18943012042291430559312349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25257349389721907412416465 18943012042291430559312349)
      ·
        refine ⟨7103629515859286459742131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18943012042291430559312349 7103629515859286459742131)
        ·
          refine ⟨10655444273788929689613197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7103629515859286459742131 10655444273788929689613197)
          ·
            refine ⟨3995791602670848633604949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10655444273788929689613197 3995791602670848633604949)
            ·
              refine ⟨23412841421899503712529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 3995791602670848633604949 23412841421899503712529)
              ·
                rfl

theorem cell20_461663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 9].length) (baseStart_461663 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_461663 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_461663 prefixEnd_461663 := by exact prefixLift 461663
  have htrace : WordTrace (prefixWord ++ tailWord_461663) baseStart_461663 baseEnd_461663 := by
    simpa [prefixWord, tailWord_461663, baseEnd_461663] using wordTrace_append hprefix tailTrace_461663
  have hstable : (prefixWord ++ tailWord_461663).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_461663).length < 2 ^ (prefixWord ++ tailWord_461663).sum := by decide
  have hdescent : baseEnd_461663 < baseStart_461663 := by decide
  rcases family_descends (prefixWord ++ tailWord_461663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_461687 : List Nat := [1, 1, 3, 1, 1, 2, 1, 7, 3]
def baseStart_461687 : Nat := 118140960795 + 461687 * 2 ^ 59
def prefixEnd_461687 : Nat := 4983230072969 + 3 ^ 40 * 461687 * 2
def baseEnd_461687 : Nat := 210726527051058116612663

theorem tailTrace_461687 : CollatzResearch.WordTrace tailWord_461687 prefixEnd_461687 210726527051058116612663 := by
  unfold tailWord_461687
  simp only [CollatzResearch.WordTrace]
  refine ⟨16839108278394323707151315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11226072185596215804767543 16839108278394323707151315)
  ·
    refine ⟨25258662417591485560726973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16839108278394323707151315 25258662417591485560726973)
    ·
      refine ⟨9471998406596807085272615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25258662417591485560726973 9471998406596807085272615)
      ·
        refine ⟨14207997609895210627908923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9471998406596807085272615 14207997609895210627908923)
        ·
          refine ⟨21311996414842815941863385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14207997609895210627908923 21311996414842815941863385)
          ·
            refine ⟨15983997311132111956397539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21311996414842815941863385 15983997311132111956397539)
            ·
              refine ⟨23975995966698167934596309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15983997311132111956397539 23975995966698167934596309)
              ·
                refine ⟨561937405469488310967101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 23975995966698167934596309 561937405469488310967101)
                ·
                  refine ⟨210726527051058116612663, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 561937405469488310967101 210726527051058116612663)
                  ·
                    rfl

theorem cell20_461687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 7, 3].length) (baseStart_461687 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_461687 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_461687 prefixEnd_461687 := by exact prefixLift 461687
  have htrace : WordTrace (prefixWord ++ tailWord_461687) baseStart_461687 baseEnd_461687 := by
    simpa [prefixWord, tailWord_461687, baseEnd_461687] using wordTrace_append hprefix tailTrace_461687
  have hstable : (prefixWord ++ tailWord_461687).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_461687).length < 2 ^ (prefixWord ++ tailWord_461687).sum := by decide
  have hdescent : baseEnd_461687 < baseStart_461687 := by decide
  rcases family_descends (prefixWord ++ tailWord_461687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_461714 : List Nat := [3, 2, 3, 2, 3, 1, 6]
def baseStart_461714 : Nat := 118140960795 + 461714 * 2 ^ 59
def prefixEnd_461714 : Nat := 4983230072969 + 3 ^ 40 * 461714 * 2
def baseEnd_461714 : Nat := 23415427842974002523617

theorem tailTrace_461714 : CollatzResearch.WordTrace tailWord_461714 prefixEnd_461714 23415427842974002523617 := by
  unfold tailWord_461714
  simp only [CollatzResearch.WordTrace]
  refine ⟨4210023262324126829596049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11226728699531004878922797 4210023262324126829596049)
  ·
    refine ⟨3157517446743095122197037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4210023262324126829596049 3157517446743095122197037)
    ·
      refine ⟨1184069042528660670823889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3157517446743095122197037 1184069042528660670823889)
      ·
        refine ⟨888051781896495503117917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1184069042528660670823889 888051781896495503117917)
        ·
          refine ⟨333019418211185813669219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 888051781896495503117917 333019418211185813669219)
          ·
            refine ⟨499529127316778720503829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 333019418211185813669219 499529127316778720503829)
            ·
              refine ⟨23415427842974002523617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 499529127316778720503829 23415427842974002523617)
              ·
                rfl

theorem cell20_461714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 3, 1, 6].length) (baseStart_461714 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_461714 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_461714 prefixEnd_461714 := by exact prefixLift 461714
  have htrace : WordTrace (prefixWord ++ tailWord_461714) baseStart_461714 baseEnd_461714 := by
    simpa [prefixWord, tailWord_461714, baseEnd_461714] using wordTrace_append hprefix tailTrace_461714
  have hstable : (prefixWord ++ tailWord_461714).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_461714).length < 2 ^ (prefixWord ++ tailWord_461714).sum := by decide
  have hdescent : baseEnd_461714 < baseStart_461714 := by decide
  rcases family_descends (prefixWord ++ tailWord_461714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_461724 : List Nat := [2, 2, 3, 3, 2, 1, 3, 2, 2]
def baseStart_461724 : Nat := 118140960795 + 461724 * 2 ^ 59
def prefixEnd_461724 : Nat := 4983230072969 + 3 ^ 40 * 461724 * 2
def baseEnd_461724 : Nat := 210743414859250432379179

theorem tailTrace_461724 : CollatzResearch.WordTrace tailWord_461724 prefixEnd_461724 210743414859250432379179 := by
  unfold tailWord_461724
  simp only [CollatzResearch.WordTrace]
  refine ⟨8420228889630139513124113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11226971852840186017498817 8420228889630139513124113)
  ·
    refine ⟨6315171667222604634843085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8420228889630139513124113 6315171667222604634843085)
    ·
      refine ⟨2368189375208476738066157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6315171667222604634843085 2368189375208476738066157)
      ·
        refine ⟨888071015703178776774809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2368189375208476738066157 888071015703178776774809)
        ·
          refine ⟨666053261777384082581107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 888071015703178776774809 666053261777384082581107)
          ·
            refine ⟨999079892666076123871661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 666053261777384082581107 999079892666076123871661)
            ·
              refine ⟨374654959749778546451873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 999079892666076123871661 374654959749778546451873)
              ·
                refine ⟨280991219812333909838905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 374654959749778546451873 280991219812333909838905)
                ·
                  refine ⟨210743414859250432379179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 280991219812333909838905 210743414859250432379179)
                  ·
                    rfl

theorem cell20_461724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 1, 3, 2, 2].length) (baseStart_461724 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_461724 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_461724 prefixEnd_461724 := by exact prefixLift 461724
  have htrace : WordTrace (prefixWord ++ tailWord_461724) baseStart_461724 baseEnd_461724 := by
    simpa [prefixWord, tailWord_461724, baseEnd_461724] using wordTrace_append hprefix tailTrace_461724
  have hstable : (prefixWord ++ tailWord_461724).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_461724).length < 2 ^ (prefixWord ++ tailWord_461724).sum := by decide
  have hdescent : baseEnd_461724 < baseStart_461724 := by decide
  rcases family_descends (prefixWord ++ tailWord_461724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_461725 : List Nat := [1, 4, 2, 1, 2, 1, 1, 3, 5]
def baseStart_461725 : Nat := 118140960795 + 461725 * 2 ^ 59
def prefixEnd_461725 : Nat := 4983230072969 + 3 ^ 40 * 461725 * 2
def baseEnd_461725 : Nat := 210743871286498873345841

theorem tailTrace_461725 : CollatzResearch.WordTrace tailWord_461725 prefixEnd_461725 210743871286498873345841 := by
  unfold tailWord_461725
  simp only [CollatzResearch.WordTrace]
  refine ⟨16840494252256656197034629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11226996168171104131356419 16840494252256656197034629)
  ·
    refine ⟨3157592672298123036943993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16840494252256656197034629 3157592672298123036943993)
    ·
      refine ⟨2368194504223592277707995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3157592672298123036943993 2368194504223592277707995)
      ·
        refine ⟨3552291756335388416561993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2368194504223592277707995 3552291756335388416561993)
        ·
          refine ⟨2664218817251541312421495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3552291756335388416561993 2664218817251541312421495)
          ·
            refine ⟨3996328225877311968632243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2664218817251541312421495 3996328225877311968632243)
            ·
              refine ⟨5994492338815967952948365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3996328225877311968632243 5994492338815967952948365)
              ·
                refine ⟨2247934627055987982355637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5994492338815967952948365 2247934627055987982355637)
                ·
                  refine ⟨210743871286498873345841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2247934627055987982355637 210743871286498873345841)
                  ·
                    rfl

theorem cell20_461725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 1, 3, 5].length) (baseStart_461725 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_461725 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_461725 prefixEnd_461725 := by exact prefixLift 461725
  have htrace : WordTrace (prefixWord ++ tailWord_461725) baseStart_461725 baseEnd_461725 := by
    simpa [prefixWord, tailWord_461725, baseEnd_461725] using wordTrace_append hprefix tailTrace_461725
  have hstable : (prefixWord ++ tailWord_461725).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_461725).length < 2 ^ (prefixWord ++ tailWord_461725).sum := by decide
  have hdescent : baseEnd_461725 < baseStart_461725 := by decide
  rcases family_descends (prefixWord ++ tailWord_461725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_461735 : List Nat := [1, 1, 6, 1, 3, 1, 2, 5]
def baseStart_461735 : Nat := 118140960795 + 461735 * 2 ^ 59
def prefixEnd_461735 : Nat := 4983230072969 + 3 ^ 40 * 461735 * 2
def baseEnd_461735 : Nat := 70249478519661094337489

theorem tailTrace_461735 : CollatzResearch.WordTrace tailWord_461735 prefixEnd_461735 70249478519661094337489 := by
  unfold tailWord_461735
  simp only [CollatzResearch.WordTrace]
  refine ⟨16840858982220427904898659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11227239321480285269932439 16840858982220427904898659)
  ·
    refine ⟨25261288473330641857347989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16840858982220427904898659 25261288473330641857347989)
    ·
      refine ⟨1184122897187373837063187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 25261288473330641857347989 1184122897187373837063187)
      ·
        refine ⟨1776184345781060755594781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1184122897187373837063187 1776184345781060755594781)
        ·
          refine ⟨666069129667897783348043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1776184345781060755594781 666069129667897783348043)
          ·
            refine ⟨999103694501846675022065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 666069129667897783348043 999103694501846675022065)
            ·
              refine ⟨749327770876385006266549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 999103694501846675022065 749327770876385006266549)
              ·
                refine ⟨70249478519661094337489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 749327770876385006266549 70249478519661094337489)
                ·
                  rfl

theorem cell20_461735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 1, 2, 5].length) (baseStart_461735 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_461735 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_461735 prefixEnd_461735 := by exact prefixLift 461735
  have htrace : WordTrace (prefixWord ++ tailWord_461735) baseStart_461735 baseEnd_461735 := by
    simpa [prefixWord, tailWord_461735, baseEnd_461735] using wordTrace_append hprefix tailTrace_461735
  have hstable : (prefixWord ++ tailWord_461735).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_461735).length < 2 ^ (prefixWord ++ tailWord_461735).sum := by decide
  have hdescent : baseEnd_461735 < baseStart_461735 := by decide
  rcases family_descends (prefixWord ++ tailWord_461735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_461780 : List Nat := [2, 4, 1, 2, 1, 2, 1, 4, 3]
def baseStart_461780 : Nat := 118140960795 + 461780 * 2 ^ 59
def prefixEnd_461780 : Nat := 4983230072969 + 3 ^ 40 * 461780 * 2
def baseEnd_461780 : Nat := 210768974785163126512283

theorem tailTrace_461780 : CollatzResearch.WordTrace tailWord_461780 prefixEnd_461780 210768974785163126512283 := by
  unfold tailWord_461780
  simp only [CollatzResearch.WordTrace]
  refine ⟨8421250133528700295143397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11228333511371600393524529 8421250133528700295143397)
  ·
    refine ⟨1578984400036631305339387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8421250133528700295143397 1578984400036631305339387)
    ·
      refine ⟨2368476600054946958009081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1578984400036631305339387 2368476600054946958009081)
      ·
        refine ⟨1776357450041210218506811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2368476600054946958009081 1776357450041210218506811)
        ·
          refine ⟨2664536175061815327760217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1776357450041210218506811 2664536175061815327760217)
          ·
            refine ⟨1998402131296361495820163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2664536175061815327760217 1998402131296361495820163)
            ·
              refine ⟨2997603196944542243730245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1998402131296361495820163 2997603196944542243730245)
              ·
                refine ⟨562050599427101670699421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2997603196944542243730245 562050599427101670699421)
                ·
                  refine ⟨210768974785163126512283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 562050599427101670699421 210768974785163126512283)
                  ·
                    rfl

theorem cell20_461780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 1, 4, 3].length) (baseStart_461780 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_461780 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_461780 prefixEnd_461780 := by exact prefixLift 461780
  have htrace : WordTrace (prefixWord ++ tailWord_461780) baseStart_461780 baseEnd_461780 := by
    simpa [prefixWord, tailWord_461780, baseEnd_461780] using wordTrace_append hprefix tailTrace_461780
  have hstable : (prefixWord ++ tailWord_461780).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_461780).length < 2 ^ (prefixWord ++ tailWord_461780).sum := by decide
  have hdescent : baseEnd_461780 < baseStart_461780 := by decide
  rcases family_descends (prefixWord ++ tailWord_461780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_461866 : List Nat := [3, 1, 4, 1, 3, 2, 2, 4]
def baseStart_461866 : Nat := 118140960795 + 461866 * 2 ^ 59
def prefixEnd_461866 : Nat := 4983230072969 + 3 ^ 40 * 461866 * 2
def baseEnd_461866 : Nat := 70269409176176349881755

theorem tailTrace_461866 : CollatzResearch.WordTrace tailWord_461866 prefixEnd_461866 70269409176176349881755 := by
  unfold tailWord_461866
  simp only [CollatzResearch.WordTrace]
  refine ⟨4211409236186459319479363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11230424629830558185278301 4211409236186459319479363)
  ·
    refine ⟨6317113854279688979219045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4211409236186459319479363 6317113854279688979219045)
    ·
      refine ⟨1184458847677441683603571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6317113854279688979219045 1184458847677441683603571)
      ·
        refine ⟨1776688271516162525405357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1184458847677441683603571 1776688271516162525405357)
        ·
          refine ⟨666258101818560947027009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1776688271516162525405357 666258101818560947027009)
          ·
            refine ⟨499693576363920710270257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 666258101818560947027009 499693576363920710270257)
            ·
              refine ⟨374770182272940532702693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 499693576363920710270257 374770182272940532702693)
              ·
                refine ⟨70269409176176349881755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 374770182272940532702693 70269409176176349881755)
                ·
                  rfl

theorem cell20_461866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 2, 2, 4].length) (baseStart_461866 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_461866 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_461866 prefixEnd_461866 := by exact prefixLift 461866
  have htrace : WordTrace (prefixWord ++ tailWord_461866) baseStart_461866 baseEnd_461866 := by
    simpa [prefixWord, tailWord_461866, baseEnd_461866] using wordTrace_append hprefix tailTrace_461866
  have hstable : (prefixWord ++ tailWord_461866).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_461866).length < 2 ^ (prefixWord ++ tailWord_461866).sum := by decide
  have hdescent : baseEnd_461866 < baseStart_461866 := by decide
  rcases family_descends (prefixWord ++ tailWord_461866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_461870 : List Nat := [4, 1, 3, 1, 1, 1, 3, 6]
def baseStart_461870 : Nat := 118140960795 + 461870 * 2 ^ 59
def prefixEnd_461870 : Nat := 4983230072969 + 3 ^ 40 * 461870 * 2
def baseEnd_461870 : Nat := 70270017745840937837305

theorem tailTrace_461870 : CollatzResearch.WordTrace tailWord_461870 prefixEnd_461870 70270017745840937837305 := by
  unfold tailWord_461870
  simp only [CollatzResearch.WordTrace]
  refine ⟨2105722854591418245132883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11230521891154230640708709 2105722854591418245132883)
  ·
    refine ⟨3158584281887127367699325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2105722854591418245132883 3158584281887127367699325)
    ·
      refine ⟨1184469105707672762887247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3158584281887127367699325 1184469105707672762887247)
      ·
        refine ⟨1776703658561509144330871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1184469105707672762887247 1776703658561509144330871)
        ·
          refine ⟨2665055487842263716496307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1776703658561509144330871 2665055487842263716496307)
          ·
            refine ⟨3997583231763395574744461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2665055487842263716496307 3997583231763395574744461)
            ·
              refine ⟨1499093711911273340529173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3997583231763395574744461 1499093711911273340529173)
              ·
                refine ⟨70270017745840937837305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1499093711911273340529173 70270017745840937837305)
                ·
                  rfl

theorem cell20_461870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 3, 6].length) (baseStart_461870 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_461870 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_461870 prefixEnd_461870 := by exact prefixLift 461870
  have htrace : WordTrace (prefixWord ++ tailWord_461870) baseStart_461870 baseEnd_461870 := by
    simpa [prefixWord, tailWord_461870, baseEnd_461870] using wordTrace_append hprefix tailTrace_461870
  have hstable : (prefixWord ++ tailWord_461870).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_461870).length < 2 ^ (prefixWord ++ tailWord_461870).sum := by decide
  have hdescent : baseEnd_461870 < baseStart_461870 := by decide
  rcases family_descends (prefixWord ++ tailWord_461870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_461876 : List Nat := [2, 5, 1, 2, 1, 3, 1, 3, 2]
def baseStart_461876 : Nat := 118140960795 + 461876 * 2 ^ 59
def prefixEnd_461876 : Nat := 4983230072969 + 3 ^ 40 * 461876 * 2
def baseEnd_461876 : Nat := 210812791801013459311891

theorem tailTrace_461876 : CollatzResearch.WordTrace tailWord_461876 prefixEnd_461876 210812791801013459311891 := by
  unfold tailWord_461876
  simp only [CollatzResearch.WordTrace]
  refine ⟨8423000837354804492890741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11230667783139739323854321 8423000837354804492890741)
  ·
    refine ⟨789656328502012921208507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 8423000837354804492890741 789656328502012921208507)
    ·
      refine ⟨1184484492753019381812761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 789656328502012921208507 1184484492753019381812761)
      ·
        refine ⟨888363369564764536359571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1184484492753019381812761 888363369564764536359571)
        ·
          refine ⟨1332545054347146804539357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 888363369564764536359571 1332545054347146804539357)
          ·
            refine ⟨499704395380180051702259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1332545054347146804539357 499704395380180051702259)
            ·
              refine ⟨749556593070270077553389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 499704395380180051702259 749556593070270077553389)
              ·
                refine ⟨281083722401351279082521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 749556593070270077553389 281083722401351279082521)
                ·
                  refine ⟨210812791801013459311891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 281083722401351279082521 210812791801013459311891)
                  ·
                    rfl

theorem cell20_461876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 3, 1, 3, 2].length) (baseStart_461876 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_461876 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_461876 prefixEnd_461876 := by exact prefixLift 461876
  have htrace : WordTrace (prefixWord ++ tailWord_461876) baseStart_461876 baseEnd_461876 := by
    simpa [prefixWord, tailWord_461876, baseEnd_461876] using wordTrace_append hprefix tailTrace_461876
  have hstable : (prefixWord ++ tailWord_461876).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_461876).length < 2 ^ (prefixWord ++ tailWord_461876).sum := by decide
  have hdescent : baseEnd_461876 < baseStart_461876 := by decide
  rcases family_descends (prefixWord ++ tailWord_461876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_461880 : List Nat := [2, 1, 2, 1, 5, 1, 3, 3, 2]
def baseStart_461880 : Nat := 118140960795 + 461880 * 2 ^ 59
def prefixEnd_461880 : Nat := 4983230072969 + 3 ^ 40 * 461880 * 2
def baseEnd_461880 : Nat := 210814617510007223178541

theorem tailTrace_461880 : CollatzResearch.WordTrace tailWord_461880 prefixEnd_461880 210814617510007223178541 := by
  unfold tailWord_461880
  simp only [CollatzResearch.WordTrace]
  refine ⟨8423073783347558834463547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11230765044463411779284729 8423073783347558834463547)
  ·
    refine ⟨12634610675021338251695321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8423073783347558834463547 12634610675021338251695321)
    ·
      refine ⟨9475958006266003688771491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12634610675021338251695321 9475958006266003688771491)
      ·
        refine ⟨14213937009399005533157237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9475958006266003688771491 14213937009399005533157237)
        ·
          refine ⟨1332556594631156768733491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 14213937009399005533157237 1332556594631156768733491)
          ·
            refine ⟨1998834891946735153100237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1332556594631156768733491 1998834891946735153100237)
            ·
              refine ⟨749563084480025682412589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1998834891946735153100237 749563084480025682412589)
              ·
                refine ⟨281086156680009630904721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 749563084480025682412589 281086156680009630904721)
                ·
                  refine ⟨210814617510007223178541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 281086156680009630904721 210814617510007223178541)
                  ·
                    rfl

theorem cell20_461880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 3, 3, 2].length) (baseStart_461880 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_461880 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_461880 prefixEnd_461880 := by exact prefixLift 461880
  have htrace : WordTrace (prefixWord ++ tailWord_461880) baseStart_461880 baseEnd_461880 := by
    simpa [prefixWord, tailWord_461880, baseEnd_461880] using wordTrace_append hprefix tailTrace_461880
  have hstable : (prefixWord ++ tailWord_461880).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_461880).length < 2 ^ (prefixWord ++ tailWord_461880).sum := by decide
  have hdescent : baseEnd_461880 < baseStart_461880 := by decide
  rcases family_descends (prefixWord ++ tailWord_461880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_461929 : List Nat := [1, 2, 1, 1, 1, 6, 2, 6]
def baseStart_461929 : Nat := 118140960795 + 461929 * 2 ^ 59
def prefixEnd_461929 : Nat := 4983230072969 + 3 ^ 40 * 461929 * 2
def baseEnd_461929 : Nat := 70278994148393610181669

theorem tailTrace_461929 : CollatzResearch.WordTrace tailWord_461929 prefixEnd_461929 70278994148393610181669 := by
  unfold tailWord_461929
  simp only [CollatzResearch.WordTrace]
  refine ⟨16847934743517599037460841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11231956495678399358307227 16847934743517599037460841)
  ·
    refine ⟨12635951057638199278095631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16847934743517599037460841 12635951057638199278095631)
    ·
      refine ⟨18953926586457298917143447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12635951057638199278095631 18953926586457298917143447)
      ·
        refine ⟨28430889879685948375715171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18953926586457298917143447 28430889879685948375715171)
        ·
          refine ⟨42646334819528922563572757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28430889879685948375715171 42646334819528922563572757)
          ·
            refine ⟨1999046944665418245167473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 42646334819528922563572757 1999046944665418245167473)
            ·
              refine ⟨1499285208499063683875605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1999046944665418245167473 1499285208499063683875605)
              ·
                refine ⟨70278994148393610181669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1499285208499063683875605 70278994148393610181669)
                ·
                  rfl

theorem cell20_461929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 2, 6].length) (baseStart_461929 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_461929 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_461929 prefixEnd_461929 := by exact prefixLift 461929
  have htrace : WordTrace (prefixWord ++ tailWord_461929) baseStart_461929 baseEnd_461929 := by
    simpa [prefixWord, tailWord_461929, baseEnd_461929] using wordTrace_append hprefix tailTrace_461929
  have hstable : (prefixWord ++ tailWord_461929).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_461929).length < 2 ^ (prefixWord ++ tailWord_461929).sum := by decide
  have hdescent : baseEnd_461929 < baseStart_461929 := by decide
  rcases family_descends (prefixWord ++ tailWord_461929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_461956 : List Nat := [2, 3, 2, 1, 2, 3, 1, 4, 2]
def baseStart_461956 : Nat := 118140960795 + 461956 * 2 ^ 59
def prefixEnd_461956 : Nat := 4983230072969 + 3 ^ 40 * 461956 * 2
def baseEnd_461956 : Nat := 210849305980888736644897

theorem tailTrace_461956 : CollatzResearch.WordTrace tailWord_461956 prefixEnd_461956 210849305980888736644897 := by
  unfold tailWord_461956
  simp only [CollatzResearch.WordTrace]
  refine ⟨8424459757209891324346861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11232613009613188432462481 8424459757209891324346861)
  ·
    refine ⟨3159172408953709246630073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8424459757209891324346861 3159172408953709246630073)
    ·
      refine ⟨2369379306715281934972555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3159172408953709246630073 2369379306715281934972555)
      ·
        refine ⟨3554068960072922902458833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2369379306715281934972555 3554068960072922902458833)
        ·
          refine ⟨2665551720054692176844125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3554068960072922902458833 2665551720054692176844125)
          ·
            refine ⟨999581895020509566316547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2665551720054692176844125 999581895020509566316547)
            ·
              refine ⟨1499372842530764349474821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 999581895020509566316547 1499372842530764349474821)
              ·
                refine ⟨281132407974518315526529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1499372842530764349474821 281132407974518315526529)
                ·
                  refine ⟨210849305980888736644897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 281132407974518315526529 210849305980888736644897)
                  ·
                    rfl

theorem cell20_461956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 3, 1, 4, 2].length) (baseStart_461956 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_461956 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_461956 prefixEnd_461956 := by exact prefixLift 461956
  have htrace : WordTrace (prefixWord ++ tailWord_461956) baseStart_461956 baseEnd_461956 := by
    simpa [prefixWord, tailWord_461956, baseEnd_461956] using wordTrace_append hprefix tailTrace_461956
  have hstable : (prefixWord ++ tailWord_461956).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_461956).length < 2 ^ (prefixWord ++ tailWord_461956).sum := by decide
  have hdescent : baseEnd_461956 < baseStart_461956 := by decide
  rcases family_descends (prefixWord ++ tailWord_461956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_461970 : List Nat := [3, 2, 3, 1, 1, 2, 2, 3, 3]
def baseStart_461970 : Nat := 118140960795 + 461970 * 2 ^ 59
def prefixEnd_461970 : Nat := 4983230072969 + 3 ^ 40 * 461970 * 2
def baseEnd_461970 : Nat := 210855695962366910178173

theorem tailTrace_461970 : CollatzResearch.WordTrace tailWord_461970 prefixEnd_461970 210855695962366910178173 := by
  unfold tailWord_461970
  simp only [CollatzResearch.WordTrace]
  refine ⟨4212357534092265759925841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11232953424246042026468909 4212357534092265759925841)
  ·
    refine ⟨3159268150569199319944381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4212357534092265759925841 3159268150569199319944381)
    ·
      refine ⟨1184725556463449744979143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3159268150569199319944381 1184725556463449744979143)
      ·
        refine ⟨1777088334695174617468715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1184725556463449744979143 1777088334695174617468715)
        ·
          refine ⟨2665632502042761926203073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1777088334695174617468715 2665632502042761926203073)
          ·
            refine ⟨1999224376532071444652305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2665632502042761926203073 1999224376532071444652305)
            ·
              refine ⟨1499418282399053583489229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1999224376532071444652305 1499418282399053583489229)
              ·
                refine ⟨562281855899645093808461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1499418282399053583489229 562281855899645093808461)
                ·
                  refine ⟨210855695962366910178173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 562281855899645093808461 210855695962366910178173)
                  ·
                    rfl

theorem cell20_461970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 2, 3, 3].length) (baseStart_461970 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_461970 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_461970 prefixEnd_461970 := by exact prefixLift 461970
  have htrace : WordTrace (prefixWord ++ tailWord_461970) baseStart_461970 baseEnd_461970 := by
    simpa [prefixWord, tailWord_461970, baseEnd_461970] using wordTrace_append hprefix tailTrace_461970
  have hstable : (prefixWord ++ tailWord_461970).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_461970).length < 2 ^ (prefixWord ++ tailWord_461970).sum := by decide
  have hdescent : baseEnd_461970 < baseStart_461970 := by decide
  rcases family_descends (prefixWord ++ tailWord_461970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_461984 : List Nat := [2, 1, 1, 4, 2, 1, 5, 4]
def baseStart_461984 : Nat := 118140960795 + 461984 * 2 ^ 59
def prefixEnd_461984 : Nat := 4983230072969 + 3 ^ 40 * 461984 * 2
def baseEnd_461984 : Nat := 70287361981281694570483

theorem tailTrace_461984 : CollatzResearch.WordTrace tailWord_461984 prefixEnd_461984 70287361981281694570483 := by
  unfold tailWord_461984
  simp only [CollatzResearch.WordTrace]
  refine ⟨8424970379159171715356503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11233293838878895620475337 8424970379159171715356503)
  ·
    refine ⟨12637455568738757573034755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8424970379159171715356503 12637455568738757573034755)
    ·
      refine ⟨18956183353108136359552133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12637455568738757573034755 18956183353108136359552133)
      ·
        refine ⟨3554284378707775567416025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18956183353108136359552133 3554284378707775567416025)
        ·
          refine ⟨2665713284030831675562019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3554284378707775567416025 2665713284030831675562019)
          ·
            refine ⟨3998569926046247513343029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2665713284030831675562019 3998569926046247513343029)
            ·
              refine ⟨374865930566835704375909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3998569926046247513343029 374865930566835704375909)
              ·
                refine ⟨70287361981281694570483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 374865930566835704375909 70287361981281694570483)
                ·
                  rfl

theorem cell20_461984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 5, 4].length) (baseStart_461984 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_461984 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_461984 prefixEnd_461984 := by exact prefixLift 461984
  have htrace : WordTrace (prefixWord ++ tailWord_461984) baseStart_461984 baseEnd_461984 := by
    simpa [prefixWord, tailWord_461984, baseEnd_461984] using wordTrace_append hprefix tailTrace_461984
  have hstable : (prefixWord ++ tailWord_461984).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_461984).length < 2 ^ (prefixWord ++ tailWord_461984).sum := by decide
  have hdescent : baseEnd_461984 < baseStart_461984 := by decide
  rcases family_descends (prefixWord ++ tailWord_461984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_462015 : List Nat := [1, 1, 2, 2, 2, 2, 4, 4, 2]
def baseStart_462015 : Nat := 118140960795 + 462015 * 2 ^ 59
def prefixEnd_462015 : Nat := 4983230072969 + 3 ^ 40 * 462015 * 2
def baseEnd_462015 : Nat := 210876235188546753677989

theorem tailTrace_462015 : CollatzResearch.WordTrace tailWord_462015 prefixEnd_462015 210876235188546753677989 := by
  unfold tailWord_462015
  simp only [CollatzResearch.WordTrace]
  refine ⟨16851071421206035725091499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11234047614137357150060999 16851071421206035725091499)
  ·
    refine ⟨25276607131809053587637249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16851071421206035725091499 25276607131809053587637249)
    ·
      refine ⟨18957455348856790190727937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25276607131809053587637249 18957455348856790190727937)
      ·
        refine ⟨14218091511642592643045953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18957455348856790190727937 14218091511642592643045953)
        ·
          refine ⟨10663568633731944482284465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14218091511642592643045953 10663568633731944482284465)
          ·
            refine ⟨7997676475298958361713349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10663568633731944482284465 7997676475298958361713349)
            ·
              refine ⟨1499564339118554692821253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7997676475298958361713349 1499564339118554692821253)
              ·
                refine ⟨281168313584729004903985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1499564339118554692821253 281168313584729004903985)
                ·
                  refine ⟨210876235188546753677989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 281168313584729004903985 210876235188546753677989)
                  ·
                    rfl

theorem cell20_462015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 4, 4, 2].length) (baseStart_462015 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_462015 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_462015 prefixEnd_462015 := by exact prefixLift 462015
  have htrace : WordTrace (prefixWord ++ tailWord_462015) baseStart_462015 baseEnd_462015 := by
    simpa [prefixWord, tailWord_462015, baseEnd_462015] using wordTrace_append hprefix tailTrace_462015
  have hstable : (prefixWord ++ tailWord_462015).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_462015).length < 2 ^ (prefixWord ++ tailWord_462015).sum := by decide
  have hdescent : baseEnd_462015 < baseStart_462015 := by decide
  rcases family_descends (prefixWord ++ tailWord_462015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_462081 : List Nat := [1, 2, 4, 1, 1, 3, 1, 7]
def baseStart_462081 : Nat := 118140960795 + 462081 * 2 ^ 59
def prefixEnd_462081 : Nat := 4983230072969 + 3 ^ 40 * 462081 * 2
def baseEnd_462081 : Nat := 70302119795647952492573

theorem tailTrace_462081 : CollatzResearch.WordTrace tailWord_462081 prefixEnd_462081 70302119795647952492573 := by
  unfold tailWord_462081
  simp only [CollatzResearch.WordTrace]
  refine ⟨16853478638966928996994097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11235652425977952664662731 16853478638966928996994097)
  ·
    refine ⟨12640108979225196747745573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16853478638966928996994097 12640108979225196747745573)
    ·
      refine ⟨2370020433604724390202295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12640108979225196747745573 2370020433604724390202295)
      ·
        refine ⟨3555030650407086585303443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2370020433604724390202295 3555030650407086585303443)
        ·
          refine ⟨5332545975610629877955165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3555030650407086585303443 5332545975610629877955165)
          ·
            refine ⟨1999704740853986204233187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5332545975610629877955165 1999704740853986204233187)
            ·
              refine ⟨2999557111280979306349781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1999704740853986204233187 2999557111280979306349781)
              ·
                refine ⟨70302119795647952492573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2999557111280979306349781 70302119795647952492573)
                ·
                  rfl

theorem cell20_462081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 1, 7].length) (baseStart_462081 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_462081 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_462081 prefixEnd_462081 := by exact prefixLift 462081
  have htrace : WordTrace (prefixWord ++ tailWord_462081) baseStart_462081 baseEnd_462081 := by
    simpa [prefixWord, tailWord_462081, baseEnd_462081] using wordTrace_append hprefix tailTrace_462081
  have hstable : (prefixWord ++ tailWord_462081).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_462081).length < 2 ^ (prefixWord ++ tailWord_462081).sum := by decide
  have hdescent : baseEnd_462081 < baseStart_462081 := by decide
  rcases family_descends (prefixWord ++ tailWord_462081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_462084 : List Nat := [2, 3, 2, 2, 2, 2, 1, 3, 3]
def baseStart_462084 : Nat := 118140960795 + 462084 * 2 ^ 59
def prefixEnd_462084 : Nat := 4983230072969 + 3 ^ 40 * 462084 * 2
def baseEnd_462084 : Nat := 210907728668689180377707

theorem tailTrace_462084 : CollatzResearch.WordTrace tailWord_462084 prefixEnd_462084 210907728668689180377707 := by
  unfold tailWord_462084
  simp only [CollatzResearch.WordTrace]
  refine ⟨8426794028978030254676653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11235725371970707006235537 8426794028978030254676653)
  ·
    refine ⟨3160047760866761345503745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8426794028978030254676653 3160047760866761345503745)
    ·
      refine ⟨2370035820650071009127809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3160047760866761345503745 2370035820650071009127809)
      ·
        refine ⟨1777526865487553256845857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2370035820650071009127809 1777526865487553256845857)
        ·
          refine ⟨1333145149115664942634393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1777526865487553256845857 1333145149115664942634393)
          ·
            refine ⟨999858861836748706975795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1333145149115664942634393 999858861836748706975795)
            ·
              refine ⟨1499788292755123060463693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 999858861836748706975795 1499788292755123060463693)
              ·
                refine ⟨562420609783171147673885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1499788292755123060463693 562420609783171147673885)
                ·
                  refine ⟨210907728668689180377707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 562420609783171147673885 210907728668689180377707)
                  ·
                    rfl

theorem cell20_462084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 2, 1, 3, 3].length) (baseStart_462084 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_462084 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_462084 prefixEnd_462084 := by exact prefixLift 462084
  have htrace : WordTrace (prefixWord ++ tailWord_462084) baseStart_462084 baseEnd_462084 := by
    simpa [prefixWord, tailWord_462084, baseEnd_462084] using wordTrace_append hprefix tailTrace_462084
  have hstable : (prefixWord ++ tailWord_462084).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_462084).length < 2 ^ (prefixWord ++ tailWord_462084).sum := by decide
  have hdescent : baseEnd_462084 < baseStart_462084 := by decide
  rcases family_descends (prefixWord ++ tailWord_462084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_462122 : List Nat := [3, 1, 4, 2, 1, 1, 1, 4, 3]
def baseStart_462122 : Nat := 118140960795 + 462122 * 2 ^ 59
def prefixEnd_462122 : Nat := 4983230072969 + 3 ^ 40 * 462122 * 2
def baseEnd_462122 : Nat := 210925072904129937110885

theorem tailTrace_462122 : CollatzResearch.WordTrace tailWord_462122 prefixEnd_462122 210925072904129937110885 := by
  unfold tailWord_462122
  simp only [CollatzResearch.WordTrace]
  refine ⟨4213743507954598249809155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11236649354545595332824413 4213743507954598249809155)
  ·
    refine ⟨6320615261931897374713733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4213743507954598249809155 6320615261931897374713733)
    ·
      refine ⟨1185115361612230757758825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6320615261931897374713733 1185115361612230757758825)
      ·
        refine ⟨888836521209173068319119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1185115361612230757758825 888836521209173068319119)
        ·
          refine ⟨1333254781813759602478679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 888836521209173068319119 1333254781813759602478679)
          ·
            refine ⟨1999882172720639403718019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1333254781813759602478679 1999882172720639403718019)
            ·
              refine ⟨2999823259080959105577029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1999882172720639403718019 2999823259080959105577029)
              ·
                refine ⟨562466861077679832295693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2999823259080959105577029 562466861077679832295693)
                ·
                  refine ⟨210925072904129937110885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 562466861077679832295693 210925072904129937110885)
                  ·
                    rfl

theorem cell20_462122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 1, 4, 3].length) (baseStart_462122 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_462122 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_462122 prefixEnd_462122 := by exact prefixLift 462122
  have htrace : WordTrace (prefixWord ++ tailWord_462122) baseStart_462122 baseEnd_462122 := by
    simpa [prefixWord, tailWord_462122, baseEnd_462122] using wordTrace_append hprefix tailTrace_462122
  have hstable : (prefixWord ++ tailWord_462122).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_462122).length < 2 ^ (prefixWord ++ tailWord_462122).sum := by decide
  have hdescent : baseEnd_462122 < baseStart_462122 := by decide
  rcases family_descends (prefixWord ++ tailWord_462122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_462125 : List Nat := [1, 5, 3, 1, 1, 2, 1, 4, 2]
def baseStart_462125 : Nat := 118140960795 + 462125 * 2 ^ 59
def prefixEnd_462125 : Nat := 4983230072969 + 3 ^ 40 * 462125 * 2
def baseEnd_462125 : Nat := 210926442185875260010873

theorem tailTrace_462125 : CollatzResearch.WordTrace tailWord_462125 prefixEnd_462125 210926442185875260010873 := by
  unfold tailWord_462125
  simp only [CollatzResearch.WordTrace]
  refine ⟨16855083450807524511595829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11236722300538349674397219 16855083450807524511595829)
  ·
    refine ⟨1580164073513205422962109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 16855083450807524511595829 1580164073513205422962109)
    ·
      refine ⟨592561527567452033610791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1580164073513205422962109 592561527567452033610791)
      ·
        refine ⟨888842291351178050416187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 592561527567452033610791 888842291351178050416187)
        ·
          refine ⟨1333263437026767075624281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 888842291351178050416187 1333263437026767075624281)
          ·
            refine ⟨999947577770075306718211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1333263437026767075624281 999947577770075306718211)
            ·
              refine ⟨1499921366655112960077317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 999947577770075306718211 1499921366655112960077317)
              ·
                refine ⟨281235256247833680014497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1499921366655112960077317 281235256247833680014497)
                ·
                  refine ⟨210926442185875260010873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 281235256247833680014497 210926442185875260010873)
                  ·
                    rfl

theorem cell20_462125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 2, 1, 4, 2].length) (baseStart_462125 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_462125 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_462125 prefixEnd_462125 := by exact prefixLift 462125
  have htrace : WordTrace (prefixWord ++ tailWord_462125) baseStart_462125 baseEnd_462125 := by
    simpa [prefixWord, tailWord_462125, baseEnd_462125] using wordTrace_append hprefix tailTrace_462125
  have hstable : (prefixWord ++ tailWord_462125).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_462125).length < 2 ^ (prefixWord ++ tailWord_462125).sum := by decide
  have hdescent : baseEnd_462125 < baseStart_462125 := by decide
  rcases family_descends (prefixWord ++ tailWord_462125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_462143 : List Nat := [1, 1, 2, 2, 4, 2, 2, 3, 3]
def baseStart_462143 : Nat := 118140960795 + 462143 * 2 ^ 59
def prefixEnd_462143 : Nat := 4983230072969 + 3 ^ 40 * 462143 * 2
def baseEnd_462143 : Nat := 210934657876347197410799

theorem tailTrace_462143 : CollatzResearch.WordTrace tailWord_462143 prefixEnd_462143 210934657876347197410799 := by
  unfold tailWord_462143
  simp only [CollatzResearch.WordTrace]
  refine ⟨16855739964742313585751083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11237159976494875723834055 16855739964742313585751083)
  ·
    refine ⟨25283609947113470378626625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16855739964742313585751083 25283609947113470378626625)
    ·
      refine ⟨18962707460335102783969969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25283609947113470378626625 18962707460335102783969969)
      ·
        refine ⟨14222030595251327087977477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18962707460335102783969969 14222030595251327087977477)
        ·
          refine ⟨2666630736609623828995777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14222030595251327087977477 2666630736609623828995777)
          ·
            refine ⟨1999973052457217871746833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2666630736609623828995777 1999973052457217871746833)
            ·
              refine ⟨1499979789342913403810125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1999973052457217871746833 1499979789342913403810125)
              ·
                refine ⟨562492421003592526428797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1499979789342913403810125 562492421003592526428797)
                ·
                  refine ⟨210934657876347197410799, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 562492421003592526428797 210934657876347197410799)
                  ·
                    rfl

theorem cell20_462143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 2, 3, 3].length) (baseStart_462143 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_462143 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_462143 prefixEnd_462143 := by exact prefixLift 462143
  have htrace : WordTrace (prefixWord ++ tailWord_462143) baseStart_462143 baseEnd_462143 := by
    simpa [prefixWord, tailWord_462143, baseEnd_462143] using wordTrace_append hprefix tailTrace_462143
  have hstable : (prefixWord ++ tailWord_462143).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_462143).length < 2 ^ (prefixWord ++ tailWord_462143).sum := by decide
  have hdescent : baseEnd_462143 < baseStart_462143 := by decide
  rcases family_descends (prefixWord ++ tailWord_462143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_462167 : List Nat := [1, 1, 3, 2, 3, 2, 1, 5, 2]
def baseStart_462167 : Nat := 118140960795 + 462167 * 2 ^ 59
def prefixEnd_462167 : Nat := 4983230072969 + 3 ^ 40 * 462167 * 2
def baseEnd_462167 : Nat := 210945612130309780610701

theorem tailTrace_462167 : CollatzResearch.WordTrace tailWord_462167 prefixEnd_462167 210945612130309780610701 := by
  unfold tailWord_462167
  simp only [CollatzResearch.WordTrace]
  refine ⟨16856615316655365684624755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11237743544436910456416503 16856615316655365684624755)
  ·
    refine ⟨25284922974983048526937133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16856615316655365684624755 25284922974983048526937133)
    ·
      refine ⟨9481846115618643197601425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25284922974983048526937133 9481846115618643197601425)
      ·
        refine ⟨7111384586713982398201069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9481846115618643197601425 7111384586713982398201069)
        ·
          refine ⟨2666769220017743399325401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7111384586713982398201069 2666769220017743399325401)
          ·
            refine ⟨2000076915013307549494051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2666769220017743399325401 2000076915013307549494051)
            ·
              refine ⟨3000115372519961324241077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2000076915013307549494051 3000115372519961324241077)
              ·
                refine ⟨281260816173746374147601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3000115372519961324241077 281260816173746374147601)
                ·
                  refine ⟨210945612130309780610701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 281260816173746374147601 210945612130309780610701)
                  ·
                    rfl

theorem cell20_462167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 1, 5, 2].length) (baseStart_462167 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_462167 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_462167 prefixEnd_462167 := by exact prefixLift 462167
  have htrace : WordTrace (prefixWord ++ tailWord_462167) baseStart_462167 baseEnd_462167 := by
    simpa [prefixWord, tailWord_462167, baseEnd_462167] using wordTrace_append hprefix tailTrace_462167
  have hstable : (prefixWord ++ tailWord_462167).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_462167).length < 2 ^ (prefixWord ++ tailWord_462167).sum := by decide
  have hdescent : baseEnd_462167 < baseStart_462167 := by decide
  rcases family_descends (prefixWord ++ tailWord_462167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_462173 : List Nat := [1, 4, 5, 1, 1, 2, 1, 2, 3]
def baseStart_462173 : Nat := 118140960795 + 462173 * 2 ^ 59
def prefixEnd_462173 : Nat := 4983230072969 + 3 ^ 40 * 462173 * 2
def baseEnd_462173 : Nat := 210948350693800426410677

theorem tailTrace_462173 : CollatzResearch.WordTrace tailWord_462173 prefixEnd_462173 210948350693800426410677 := by
  unfold tailWord_462173
  simp only [CollatzResearch.WordTrace]
  refine ⟨16856834154633628709343173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11237889436422419139562115 16856834154633628709343173)
  ·
    refine ⟨3160656403993805383001845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16856834154633628709343173 3160656403993805383001845)
    ·
      refine ⟨296311537874419254656423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 3160656403993805383001845 296311537874419254656423)
      ·
        refine ⟨444467306811628881984635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 296311537874419254656423 444467306811628881984635)
        ·
          refine ⟨666700960217443322976953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 444467306811628881984635 666700960217443322976953)
          ·
            refine ⟨500025720163082492232715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 666700960217443322976953 500025720163082492232715)
            ·
              refine ⟨750038580244623738349073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 500025720163082492232715 750038580244623738349073)
              ·
                refine ⟨562528935183467803761805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 750038580244623738349073 562528935183467803761805)
                ·
                  refine ⟨210948350693800426410677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 562528935183467803761805 210948350693800426410677)
                  ·
                    rfl

theorem cell20_462173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 2, 1, 2, 3].length) (baseStart_462173 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_462173 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_462173 prefixEnd_462173 := by exact prefixLift 462173
  have htrace : WordTrace (prefixWord ++ tailWord_462173) baseStart_462173 baseEnd_462173 := by
    simpa [prefixWord, tailWord_462173, baseEnd_462173] using wordTrace_append hprefix tailTrace_462173
  have hstable : (prefixWord ++ tailWord_462173).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_462173).length < 2 ^ (prefixWord ++ tailWord_462173).sum := by decide
  have hdescent : baseEnd_462173 < baseStart_462173 := by decide
  rcases family_descends (prefixWord ++ tailWord_462173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_462188 : List Nat := [2, 2, 1, 1, 5, 1, 1, 3, 4]
def baseStart_462188 : Nat := 118140960795 + 462188 * 2 ^ 59
def prefixEnd_462188 : Nat := 4983230072969 + 3 ^ 40 * 462188 * 2
def baseEnd_462188 : Nat := 210955197102527040910615

theorem tailTrace_462188 : CollatzResearch.WordTrace tailWord_462188 prefixEnd_462188 210955197102527040910615 := by
  unfold tailWord_462188
  simp only [CollatzResearch.WordTrace]
  refine ⟨8428690624789643135569609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11238254166386190847426145 8428690624789643135569609)
  ·
    refine ⟨6321517968592232351677207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8428690624789643135569609 6321517968592232351677207)
    ·
      refine ⟨9482276952888348527515811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6321517968592232351677207 9482276952888348527515811)
      ·
        refine ⟨14223415429332522791273717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9482276952888348527515811 14223415429332522791273717)
        ·
          refine ⟨1333445196499924011681911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 14223415429332522791273717 1333445196499924011681911)
          ·
            refine ⟨2000167794749886017522867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1333445196499924011681911 2000167794749886017522867)
            ·
              refine ⟨3000251692124829026284301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2000167794749886017522867 3000251692124829026284301)
              ·
                refine ⟨1125094384546810884856613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3000251692124829026284301 1125094384546810884856613)
                ·
                  refine ⟨210955197102527040910615, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1125094384546810884856613 210955197102527040910615)
                  ·
                    rfl

theorem cell20_462188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 4].length) (baseStart_462188 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_462188 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_462188 prefixEnd_462188 := by exact prefixLift 462188
  have htrace : WordTrace (prefixWord ++ tailWord_462188) baseStart_462188 baseEnd_462188 := by
    simpa [prefixWord, tailWord_462188, baseEnd_462188] using wordTrace_append hprefix tailTrace_462188
  have hstable : (prefixWord ++ tailWord_462188).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_462188).length < 2 ^ (prefixWord ++ tailWord_462188).sum := by decide
  have hdescent : baseEnd_462188 < baseStart_462188 := by decide
  rcases family_descends (prefixWord ++ tailWord_462188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_462212 : List Nat := [2, 3, 2, 1, 1, 3, 4, 4]
def baseStart_462212 : Nat := 118140960795 + 462212 * 2 ^ 59
def prefixEnd_462212 : Nat := 4983230072969 + 3 ^ 40 * 462212 * 2
def baseEnd_462212 : Nat := 70322050452163208036839

theorem tailTrace_462212 : CollatzResearch.WordTrace tailWord_462212 prefixEnd_462212 70322050452163208036839 := by
  unfold tailWord_462212
  simp only [CollatzResearch.WordTrace]
  refine ⟨8429128300746169185006445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11238837734328225580008593 8429128300746169185006445)
  ·
    refine ⟨3160923112779813444377417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8429128300746169185006445 3160923112779813444377417)
    ·
      refine ⟨2370692334584860083283063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3160923112779813444377417 2370692334584860083283063)
      ·
        refine ⟨3556038501877290124924595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2370692334584860083283063 3556038501877290124924595)
        ·
          refine ⟨5334057752815935187386893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3556038501877290124924595 5334057752815935187386893)
          ·
            refine ⟨2000271657305975695270085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5334057752815935187386893 2000271657305975695270085)
            ·
              refine ⟨375050935744870442863141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2000271657305975695270085 375050935744870442863141)
              ·
                refine ⟨70322050452163208036839, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 375050935744870442863141 70322050452163208036839)
                ·
                  rfl

theorem cell20_462212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 4, 4].length) (baseStart_462212 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_462212 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_462212 prefixEnd_462212 := by exact prefixLift 462212
  have htrace : WordTrace (prefixWord ++ tailWord_462212) baseStart_462212 baseEnd_462212 := by
    simpa [prefixWord, tailWord_462212, baseEnd_462212] using wordTrace_append hprefix tailTrace_462212
  have hstable : (prefixWord ++ tailWord_462212).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_462212).length < 2 ^ (prefixWord ++ tailWord_462212).sum := by decide
  have hdescent : baseEnd_462212 < baseStart_462212 := by decide
  rcases family_descends (prefixWord ++ tailWord_462212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_462233 : List Nat := [1, 2, 1, 2, 1, 7, 6]
def baseStart_462233 : Nat := 118140960795 + 462233 * 2 ^ 59
def prefixEnd_462233 : Nat := 4983230072969 + 3 ^ 40 * 462233 * 2
def baseEnd_462233 : Nat := 23441748480967431601159

theorem tailTrace_462233 : CollatzResearch.WordTrace tailWord_462233 prefixEnd_462233 23441748480967431601159 := by
  unfold tailWord_462233
  simp only [CollatzResearch.WordTrace]
  refine ⟨16859022534416258956527353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11239348356277505971018235 16859022534416258956527353)
  ·
    refine ⟨12644266900812194217395515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16859022534416258956527353 12644266900812194217395515)
    ·
      refine ⟨18966400351218291326093273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12644266900812194217395515 18966400351218291326093273)
      ·
        refine ⟨14224800263413718494569955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18966400351218291326093273 14224800263413718494569955)
        ·
          refine ⟨21337200395120577741854933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14224800263413718494569955 21337200395120577741854933)
          ·
            refine ⟨500090634260638540824725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 21337200395120577741854933 500090634260638540824725)
            ·
              refine ⟨23441748480967431601159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 500090634260638540824725 23441748480967431601159)
              ·
                rfl

theorem cell20_462233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 7, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 7, 6].length) (baseStart_462233 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_462233 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_462233 prefixEnd_462233 := by exact prefixLift 462233
  have htrace : WordTrace (prefixWord ++ tailWord_462233) baseStart_462233 baseEnd_462233 := by
    simpa [prefixWord, tailWord_462233, baseEnd_462233] using wordTrace_append hprefix tailTrace_462233
  have hstable : (prefixWord ++ tailWord_462233).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_462233).length < 2 ^ (prefixWord ++ tailWord_462233).sum := by decide
  have hdescent : baseEnd_462233 < baseStart_462233 := by decide
  rcases family_descends (prefixWord ++ tailWord_462233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_462240 : List Nat := [2, 1, 1, 4, 1, 2, 1, 3, 5]
def baseStart_462240 : Nat := 118140960795 + 462240 * 2 ^ 59
def prefixEnd_462240 : Nat := 4983230072969 + 3 ^ 40 * 462240 * 2
def baseEnd_462240 : Nat := 210978931319445971177069

theorem tailTrace_462240 : CollatzResearch.WordTrace tailWord_462240 prefixEnd_462240 210978931319445971177069 := by
  unfold tailWord_462240
  simp only [CollatzResearch.WordTrace]
  refine ⟨8429638922695449576016087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11239518563593932768021449 8429638922695449576016087)
  ·
    refine ⟨12644458384043174364024131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8429638922695449576016087 12644458384043174364024131)
    ·
      refine ⟨18966687576064761546036197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12644458384043174364024131 18966687576064761546036197)
      ·
        refine ⟨3556253920512142789881787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18966687576064761546036197 3556253920512142789881787)
        ·
          refine ⟨5334380880768214184822681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3556253920512142789881787 5334380880768214184822681)
          ·
            refine ⟨4000785660576160638617011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5334380880768214184822681 4000785660576160638617011)
            ·
              refine ⟨6001178490864240957925517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4000785660576160638617011 6001178490864240957925517)
              ·
                refine ⟨2250441934074090359222069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6001178490864240957925517 2250441934074090359222069)
                ·
                  refine ⟨210978931319445971177069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2250441934074090359222069 210978931319445971177069)
                  ·
                    rfl

theorem cell20_462240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 1, 3, 5].length) (baseStart_462240 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_462240 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_462240 prefixEnd_462240 := by exact prefixLift 462240
  have htrace : WordTrace (prefixWord ++ tailWord_462240) baseStart_462240 baseEnd_462240 := by
    simpa [prefixWord, tailWord_462240, baseEnd_462240] using wordTrace_append hprefix tailTrace_462240
  have hstable : (prefixWord ++ tailWord_462240).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_462240).length < 2 ^ (prefixWord ++ tailWord_462240).sum := by decide
  have hdescent : baseEnd_462240 < baseStart_462240 := by decide
  rcases family_descends (prefixWord ++ tailWord_462240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_462253 : List Nat := [1, 5, 2, 2, 1, 1, 4, 1, 3]
def baseStart_462253 : Nat := 118140960795 + 462253 * 2 ^ 59
def prefixEnd_462253 : Nat := 4983230072969 + 3 ^ 40 * 462253 * 2
def baseEnd_462253 : Nat := 210984864873675703743683

theorem tailTrace_462253 : CollatzResearch.WordTrace tailWord_462253 prefixEnd_462253 210984864873675703743683 := by
  unfold tailWord_462253
  simp only [CollatzResearch.WordTrace]
  refine ⟨16859751994343802372255413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11239834662895868248170275 16859751994343802372255413)
  ·
    refine ⟨1580601749469731472398945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 16859751994343802372255413 1580601749469731472398945)
    ·
      refine ⟨1185451312102298604299209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1580601749469731472398945 1185451312102298604299209)
      ·
        refine ⟨889088484076723953224407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1185451312102298604299209 889088484076723953224407)
        ·
          refine ⟨1333632726115085929836611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 889088484076723953224407 1333632726115085929836611)
          ·
            refine ⟨2000449089172628894754917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1333632726115085929836611 2000449089172628894754917)
            ·
              refine ⟨375084204219867917766547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2000449089172628894754917 375084204219867917766547)
              ·
                refine ⟨562626306329801876649821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 375084204219867917766547 562626306329801876649821)
                ·
                  refine ⟨210984864873675703743683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 562626306329801876649821 210984864873675703743683)
                  ·
                    rfl

theorem cell20_462253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 4, 1, 3].length) (baseStart_462253 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_462253 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_462253 prefixEnd_462253 := by exact prefixLift 462253
  have htrace : WordTrace (prefixWord ++ tailWord_462253) baseStart_462253 baseEnd_462253 := by
    simpa [prefixWord, tailWord_462253, baseEnd_462253] using wordTrace_append hprefix tailTrace_462253
  have hstable : (prefixWord ++ tailWord_462253).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_462253).length < 2 ^ (prefixWord ++ tailWord_462253).sum := by decide
  have hdescent : baseEnd_462253 < baseStart_462253 := by decide
  rcases family_descends (prefixWord ++ tailWord_462253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_462257 : List Nat := [1, 2, 2, 4, 1, 1, 3, 3, 3]
def baseStart_462257 : Nat := 118140960795 + 462257 * 2 ^ 59
def prefixEnd_462257 : Nat := 4983230072969 + 3 ^ 40 * 462257 * 2
def baseEnd_462257 : Nat := 210986690582669467610333

theorem tailTrace_462257 : CollatzResearch.WordTrace tailWord_462257 prefixEnd_462257 210986690582669467610333 := by
  unfold tailWord_462257
  simp only [CollatzResearch.WordTrace]
  refine ⟨16859897886329311055401025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11239931924219540703600683 16859897886329311055401025)
  ·
    refine ⟨12644923414746983291550769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16859897886329311055401025 12644923414746983291550769)
    ·
      refine ⟨9483692561060237468663077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12644923414746983291550769 9483692561060237468663077)
      ·
        refine ⟨1778192355198794525374327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9483692561060237468663077 1778192355198794525374327)
        ·
          refine ⟨2667288532798191788061491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1778192355198794525374327 2667288532798191788061491)
          ·
            refine ⟨4000932799197287682092237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2667288532798191788061491 4000932799197287682092237)
            ·
              refine ⟨1500349799698982880784589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4000932799197287682092237 1500349799698982880784589)
              ·
                refine ⟨562631174887118580294221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1500349799698982880784589 562631174887118580294221)
                ·
                  refine ⟨210986690582669467610333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 562631174887118580294221 210986690582669467610333)
                  ·
                    rfl

theorem cell20_462257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 3, 3, 3].length) (baseStart_462257 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_462257 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_462257 prefixEnd_462257 := by exact prefixLift 462257
  have htrace : WordTrace (prefixWord ++ tailWord_462257) baseStart_462257 baseEnd_462257 := by
    simpa [prefixWord, tailWord_462257, baseEnd_462257] using wordTrace_append hprefix tailTrace_462257
  have hstable : (prefixWord ++ tailWord_462257).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_462257).length < 2 ^ (prefixWord ++ tailWord_462257).sum := by decide
  have hdescent : baseEnd_462257 < baseStart_462257 := by decide
  rcases family_descends (prefixWord ++ tailWord_462257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_462294 : List Nat := [5, 2, 1, 1, 1, 4, 2, 2, 2]
def baseStart_462294 : Nat := 118140960795 + 462294 * 2 ^ 59
def prefixEnd_462294 : Nat := 4983230072969 + 3 ^ 40 * 462294 * 2
def baseEnd_462294 : Nat := 211003578390861783376849

theorem tailTrace_462294 : CollatzResearch.WordTrace tailWord_462294 prefixEnd_462294 211003578390861783376849 := by
  unfold tailWord_462294
  simp only [CollatzResearch.WordTrace]
  refine ⟨1053827961699704148406121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 11240831591463510916331957 1053827961699704148406121)
  ·
    refine ⟨790370971274778111304591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1053827961699704148406121 790370971274778111304591)
    ·
      refine ⟨1185556456912167166956887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 790370971274778111304591 1185556456912167166956887)
      ·
        refine ⟨1778334685368250750435331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1185556456912167166956887 1778334685368250750435331)
        ·
          refine ⟨2667502028052376125652997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1778334685368250750435331 2667502028052376125652997)
          ·
            refine ⟨500156630259820523559937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2667502028052376125652997 500156630259820523559937)
            ·
              refine ⟨375117472694865392669953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 500156630259820523559937 375117472694865392669953)
              ·
                refine ⟨281338104521149044502465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 375117472694865392669953 281338104521149044502465)
                ·
                  refine ⟨211003578390861783376849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 281338104521149044502465 211003578390861783376849)
                  ·
                    rfl

theorem cell20_462294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 4, 2, 2, 2].length) (baseStart_462294 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_462294 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_462294 prefixEnd_462294 := by exact prefixLift 462294
  have htrace : WordTrace (prefixWord ++ tailWord_462294) baseStart_462294 baseEnd_462294 := by
    simpa [prefixWord, tailWord_462294, baseEnd_462294] using wordTrace_append hprefix tailTrace_462294
  have hstable : (prefixWord ++ tailWord_462294).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_462294).length < 2 ^ (prefixWord ++ tailWord_462294).sum := by decide
  have hdescent : baseEnd_462294 < baseStart_462294 := by decide
  rcases family_descends (prefixWord ++ tailWord_462294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_462298 : List Nat := [3, 1, 1, 2, 3, 2, 4, 2, 2]
def baseStart_462298 : Nat := 118140960795 + 462298 * 2 ^ 59
def prefixEnd_462298 : Nat := 4983230072969 + 3 ^ 40 * 462298 * 2
def baseEnd_462298 : Nat := 211005404099855547243499

theorem tailTrace_462298 : CollatzResearch.WordTrace tailWord_462298 prefixEnd_462298 211005404099855547243499 := by
  unfold tailWord_462298
  simp only [CollatzResearch.WordTrace]
  refine ⟨4215348319795193764410887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11240928852787183371762365 4215348319795193764410887)
  ·
    refine ⟨6323022479692790646616331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4215348319795193764410887 6323022479692790646616331)
    ·
      refine ⟨9484533719539185969924497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6323022479692790646616331 9484533719539185969924497)
      ·
        refine ⟨7113400289654389477443373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9484533719539185969924497 7113400289654389477443373)
        ·
          refine ⟨2667525108620396054041265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7113400289654389477443373 2667525108620396054041265)
          ·
            refine ⟨2000643831465297040530949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2667525108620396054041265 2000643831465297040530949)
            ·
              refine ⟨375120718399743195099553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2000643831465297040530949 375120718399743195099553)
              ·
                refine ⟨281340538799807396324665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 375120718399743195099553 281340538799807396324665)
                ·
                  refine ⟨211005404099855547243499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 281340538799807396324665 211005404099855547243499)
                  ·
                    rfl

theorem cell20_462298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 4, 2, 2].length) (baseStart_462298 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_462298 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_462298 prefixEnd_462298 := by exact prefixLift 462298
  have htrace : WordTrace (prefixWord ++ tailWord_462298) baseStart_462298 baseEnd_462298 := by
    simpa [prefixWord, tailWord_462298, baseEnd_462298] using wordTrace_append hprefix tailTrace_462298
  have hstable : (prefixWord ++ tailWord_462298).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_462298).length < 2 ^ (prefixWord ++ tailWord_462298).sum := by decide
  have hdescent : baseEnd_462298 < baseStart_462298 := by decide
  rcases family_descends (prefixWord ++ tailWord_462298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_462342 : List Nat := [6, 2, 1, 1, 3, 1, 1, 2, 3]
def baseStart_462342 : Nat := 118140960795 + 462342 * 2 ^ 59
def prefixEnd_462342 : Nat := 4983230072969 + 3 ^ 40 * 462342 * 2
def baseEnd_462342 : Nat := 211025486898786949776653

theorem tailTrace_462342 : CollatzResearch.WordTrace tailWord_462342 prefixEnd_462342 211025486898786949776653 := by
  unfold tailWord_462342
  simp only [CollatzResearch.WordTrace]
  refine ⟨526968690344417830382665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 11241998727347580381496853 526968690344417830382665)
  ·
    refine ⟨395226517758313372786999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 526968690344417830382665 395226517758313372786999)
    ·
      refine ⟨592839776637470059180499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 395226517758313372786999 592839776637470059180499)
      ·
        refine ⟨889259664956205088770749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 592839776637470059180499 889259664956205088770749)
        ·
          refine ⟨333472374358576908289031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 889259664956205088770749 333472374358576908289031)
          ·
            refine ⟨500208561537865362433547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 333472374358576908289031 500208561537865362433547)
            ·
              refine ⟨750312842306798043650321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 500208561537865362433547 750312842306798043650321)
              ·
                refine ⟨562734631730098532737741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 750312842306798043650321 562734631730098532737741)
                ·
                  refine ⟨211025486898786949776653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 562734631730098532737741 211025486898786949776653)
                  ·
                    rfl

theorem cell20_462342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 3, 1, 1, 2, 3].length) (baseStart_462342 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_462342 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_462342 prefixEnd_462342 := by exact prefixLift 462342
  have htrace : WordTrace (prefixWord ++ tailWord_462342) baseStart_462342 baseEnd_462342 := by
    simpa [prefixWord, tailWord_462342, baseEnd_462342] using wordTrace_append hprefix tailTrace_462342
  have hstable : (prefixWord ++ tailWord_462342).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_462342).length < 2 ^ (prefixWord ++ tailWord_462342).sum := by decide
  have hdescent : baseEnd_462342 < baseStart_462342 := by decide
  rcases family_descends (prefixWord ++ tailWord_462342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_462347 : List Nat := [1, 1, 1, 1, 8, 1, 7]
def baseStart_462347 : Nat := 118140960795 + 462347 * 2 ^ 59
def prefixEnd_462347 : Nat := 4983230072969 + 3 ^ 40 * 462347 * 2
def baseEnd_462347 : Nat := 23447529892781017178885

theorem tailTrace_462347 : CollatzResearch.WordTrace tailWord_462347 prefixEnd_462347 23447529892781017178885 := by
  unfold tailWord_462347
  simp only [CollatzResearch.WordTrace]
  refine ⟨16863180456003256426177295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11242120304002170950784863 16863180456003256426177295)
  ·
    refine ⟨25294770684004884639265943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16863180456003256426177295 25294770684004884639265943)
    ·
      refine ⟨37942156026007326958898915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25294770684004884639265943 37942156026007326958898915)
      ·
        refine ⟨56913234039010990438348373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37942156026007326958898915 56913234039010990438348373)
        ·
          refine ⟨666951961394660044199395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 56913234039010990438348373 666951961394660044199395)
          ·
            refine ⟨1000427942091990066299093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 666951961394660044199395 1000427942091990066299093)
            ·
              refine ⟨23447529892781017178885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1000427942091990066299093 23447529892781017178885)
              ·
                rfl

theorem cell20_462347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 1, 7].length) (baseStart_462347 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_462347 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_462347 prefixEnd_462347 := by exact prefixLift 462347
  have htrace : WordTrace (prefixWord ++ tailWord_462347) baseStart_462347 baseEnd_462347 := by
    simpa [prefixWord, tailWord_462347, baseEnd_462347] using wordTrace_append hprefix tailTrace_462347
  have hstable : (prefixWord ++ tailWord_462347).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_462347).length < 2 ^ (prefixWord ++ tailWord_462347).sum := by decide
  have hdescent : baseEnd_462347 < baseStart_462347 := by decide
  rcases family_descends (prefixWord ++ tailWord_462347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_462357 : List Nat := [1, 3, 2, 1, 3, 2, 2, 4, 2]
def baseStart_462357 : Nat := 118140960795 + 462357 * 2 ^ 59
def prefixEnd_462357 : Nat := 4983230072969 + 3 ^ 40 * 462357 * 2
def baseEnd_462357 : Nat := 211032333307513564276591

theorem tailTrace_462357 : CollatzResearch.WordTrace tailWord_462357 prefixEnd_462357 211032333307513564276591 := by
  unfold tailWord_462357
  simp only [CollatzResearch.WordTrace]
  refine ⟨16863545185967028134041325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11242363457311352089360883 16863545185967028134041325)
  ·
    refine ⟨6323829444737635550265497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16863545185967028134041325 6323829444737635550265497)
    ·
      refine ⟨4742872083553226662699123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6323829444737635550265497 4742872083553226662699123)
      ·
        refine ⟨7114308125329839994048685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4742872083553226662699123 7114308125329839994048685)
        ·
          refine ⟨2667865546998689997768257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7114308125329839994048685 2667865546998689997768257)
          ·
            refine ⟨2000899160249017498326193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2667865546998689997768257 2000899160249017498326193)
            ·
              refine ⟨1500674370186763123744645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2000899160249017498326193 1500674370186763123744645)
              ·
                refine ⟨281376444410018085702121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1500674370186763123744645 281376444410018085702121)
                ·
                  refine ⟨211032333307513564276591, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 281376444410018085702121 211032333307513564276591)
                  ·
                    rfl

theorem cell20_462357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 2, 4, 2].length) (baseStart_462357 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_462357 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_462357 prefixEnd_462357 := by exact prefixLift 462357
  have htrace : WordTrace (prefixWord ++ tailWord_462357) baseStart_462357 baseEnd_462357 := by
    simpa [prefixWord, tailWord_462357, baseEnd_462357] using wordTrace_append hprefix tailTrace_462357
  have hstable : (prefixWord ++ tailWord_462357).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_462357).length < 2 ^ (prefixWord ++ tailWord_462357).sum := by decide
  have hdescent : baseEnd_462357 < baseStart_462357 := by decide
  rcases family_descends (prefixWord ++ tailWord_462357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_462378 : List Nat := [3, 1, 4, 1, 1, 1, 1, 4, 4]
def baseStart_462378 : Nat := 118140960795 + 462378 * 2 ^ 59
def prefixEnd_462378 : Nat := 4983230072969 + 3 ^ 40 * 462378 * 2
def baseEnd_462378 : Nat := 211041918279730824576505

theorem tailTrace_462378 : CollatzResearch.WordTrace tailWord_462378 prefixEnd_462378 211041918279730824576505 := by
  unfold tailWord_462378
  simp only [CollatzResearch.WordTrace]
  refine ⟨4216077779722737180138947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11242874079260632480370525 4216077779722737180138947)
  ·
    refine ⟨6324116669584105770208421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4216077779722737180138947 6324116669584105770208421)
    ·
      refine ⟨1185771875547019831914079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6324116669584105770208421 1185771875547019831914079)
      ·
        refine ⟨1778657813320529747871119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1185771875547019831914079 1778657813320529747871119)
        ·
          refine ⟨2667986719980794621806679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1778657813320529747871119 2667986719980794621806679)
          ·
            refine ⟨4001980079971191932710019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2667986719980794621806679 4001980079971191932710019)
            ·
              refine ⟨6002970119956787899065029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4001980079971191932710019 6002970119956787899065029)
              ·
                refine ⟨1125556897491897731074693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6002970119956787899065029 1125556897491897731074693)
                ·
                  refine ⟨211041918279730824576505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1125556897491897731074693 211041918279730824576505)
                  ·
                    rfl

theorem cell20_462378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 1, 4, 4].length) (baseStart_462378 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_462378 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_462378 prefixEnd_462378 := by exact prefixLift 462378
  have htrace : WordTrace (prefixWord ++ tailWord_462378) baseStart_462378 baseEnd_462378 := by
    simpa [prefixWord, tailWord_462378, baseEnd_462378] using wordTrace_append hprefix tailTrace_462378
  have hstable : (prefixWord ++ tailWord_462378).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_462378).length < 2 ^ (prefixWord ++ tailWord_462378).sum := by decide
  have hdescent : baseEnd_462378 < baseStart_462378 := by decide
  rcases family_descends (prefixWord ++ tailWord_462378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_462392 : List Nat := [2, 1, 2, 1, 4, 2, 1, 2, 5]
def baseStart_462392 : Nat := 118140960795 + 462392 * 2 ^ 59
def prefixEnd_462392 : Nat := 4983230072969 + 3 ^ 40 * 462392 * 2
def baseEnd_462392 : Nat := 211048308261208998109781

theorem tailTrace_462392 : CollatzResearch.WordTrace tailWord_462392 prefixEnd_462392 211048308261208998109781 := by
  unfold tailWord_462392
  simp only [CollatzResearch.WordTrace]
  refine ⟨8432410870420114555782715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11243214493893486074376953 8432410870420114555782715)
  ·
    refine ⟨12648616305630171833674073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8432410870420114555782715 12648616305630171833674073)
    ·
      refine ⟨9486462229222628875255555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12648616305630171833674073 9486462229222628875255555)
      ·
        refine ⟨14229693343833943312883333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9486462229222628875255555 14229693343833943312883333)
        ·
          refine ⟨2668067501968864371165625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14229693343833943312883333 2668067501968864371165625)
          ·
            refine ⟨2001050626476648278374219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2668067501968864371165625 2001050626476648278374219)
            ·
              refine ⟨3001575939714972417561329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2001050626476648278374219 3001575939714972417561329)
              ·
                refine ⟨2251181954786229313170997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3001575939714972417561329 2251181954786229313170997)
                ·
                  refine ⟨211048308261208998109781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2251181954786229313170997 211048308261208998109781)
                  ·
                    rfl

theorem cell20_462392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 1, 2, 5].length) (baseStart_462392 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_462392 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_462392 prefixEnd_462392 := by exact prefixLift 462392
  have htrace : WordTrace (prefixWord ++ tailWord_462392) baseStart_462392 baseEnd_462392 := by
    simpa [prefixWord, tailWord_462392, baseEnd_462392] using wordTrace_append hprefix tailTrace_462392
  have hstable : (prefixWord ++ tailWord_462392).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_462392).length < 2 ^ (prefixWord ++ tailWord_462392).sum := by decide
  have hdescent : baseEnd_462392 < baseStart_462392 := by decide
  rcases family_descends (prefixWord ++ tailWord_462392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_462412 : List Nat := [2, 2, 1, 3, 1, 4, 3, 2, 2]
def baseStart_462412 : Nat := 118140960795 + 462412 * 2 ^ 59
def prefixEnd_462412 : Nat := 4983230072969 + 3 ^ 40 * 462412 * 2
def baseEnd_462412 : Nat := 211057436806177817443033

theorem tailTrace_462412 : CollatzResearch.WordTrace tailWord_462412 prefixEnd_462412 211057436806177817443033 := by
  unfold tailWord_462412
  simp only [CollatzResearch.WordTrace]
  refine ⟨8432775600383886263646745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11243700800511848351528993 8432775600383886263646745)
  ·
    refine ⟨6324581700287914697735059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8432775600383886263646745 6324581700287914697735059)
    ·
      refine ⟨9486872550431872046602589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6324581700287914697735059 9486872550431872046602589)
      ·
        refine ⟨3557577206411952017475971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9486872550431872046602589 3557577206411952017475971)
        ·
          refine ⟨5336365809617928026213957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3557577206411952017475971 5336365809617928026213957)
          ·
            refine ⟨1000568589303361504915117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5336365809617928026213957 1000568589303361504915117)
            ·
              refine ⟨375213220988760564343169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1000568589303361504915117 375213220988760564343169)
              ·
                refine ⟨281409915741570423257377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 375213220988760564343169 281409915741570423257377)
                ·
                  refine ⟨211057436806177817443033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 281409915741570423257377 211057436806177817443033)
                  ·
                    rfl

theorem cell20_462412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 4, 3, 2, 2].length) (baseStart_462412 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_462412 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_462412 prefixEnd_462412 := by exact prefixLift 462412
  have htrace : WordTrace (prefixWord ++ tailWord_462412) baseStart_462412 baseEnd_462412 := by
    simpa [prefixWord, tailWord_462412, baseEnd_462412] using wordTrace_append hprefix tailTrace_462412
  have hstable : (prefixWord ++ tailWord_462412).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_462412).length < 2 ^ (prefixWord ++ tailWord_462412).sum := by decide
  have hdescent : baseEnd_462412 < baseStart_462412 := by decide
  rcases family_descends (prefixWord ++ tailWord_462412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_462422 : List Nat := [5, 2, 2, 2, 1, 1, 1, 3, 3]
def baseStart_462422 : Nat := 118140960795 + 462422 * 2 ^ 59
def prefixEnd_462422 : Nat := 4983230072969 + 3 ^ 40 * 462422 * 2
def baseEnd_462422 : Nat := 211062001078662227109659

theorem tailTrace_462422 : CollatzResearch.WordTrace tailWord_462422 prefixEnd_462422 211062001078662227109659 := by
  unfold tailWord_462422
  simp only [CollatzResearch.WordTrace]
  refine ⟨1054119745670721514697345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 11243943953821029490105013 1054119745670721514697345)
  ·
    refine ⟨790589809253041136023009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1054119745670721514697345 790589809253041136023009)
    ·
      refine ⟨592942356939780852017257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 790589809253041136023009 592942356939780852017257)
      ·
        refine ⟨444706767704835639012943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 592942356939780852017257 444706767704835639012943)
        ·
          refine ⟨667060151557253458519415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 444706767704835639012943 667060151557253458519415)
          ·
            refine ⟨1000590227335880187779123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 667060151557253458519415 1000590227335880187779123)
            ·
              refine ⟨1500885341003820281668685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1000590227335880187779123 1500885341003820281668685)
              ·
                refine ⟨562832002876432605625757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1500885341003820281668685 562832002876432605625757)
                ·
                  refine ⟨211062001078662227109659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 562832002876432605625757 211062001078662227109659)
                  ·
                    rfl

theorem cell20_462422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 1, 1, 3, 3].length) (baseStart_462422 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_462422 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_462422 prefixEnd_462422 := by exact prefixLift 462422
  have htrace : WordTrace (prefixWord ++ tailWord_462422) baseStart_462422 baseEnd_462422 := by
    simpa [prefixWord, tailWord_462422, baseEnd_462422] using wordTrace_append hprefix tailTrace_462422
  have hstable : (prefixWord ++ tailWord_462422).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_462422).length < 2 ^ (prefixWord ++ tailWord_462422).sum := by decide
  have hdescent : baseEnd_462422 < baseStart_462422 := by decide
  rcases family_descends (prefixWord ++ tailWord_462422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_462423 : List Nat := [1, 1, 3, 2, 2, 4, 2, 5]
def baseStart_462423 : Nat := 118140960795 + 462423 * 2 ^ 59
def prefixEnd_462423 : Nat := 4983230072969 + 3 ^ 40 * 462423 * 2
def baseEnd_462423 : Nat := 70354152501970222692107

theorem tailTrace_462423 : CollatzResearch.WordTrace tailWord_462423 prefixEnd_462423 70354152501970222692107 := by
  unfold tailWord_462423
  simp only [CollatzResearch.WordTrace]
  refine ⟨16865952403727921405943923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11243968269151947603962615 16865952403727921405943923)
  ·
    refine ⟨25298928605591882108915885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16865952403727921405943923 25298928605591882108915885)
    ·
      refine ⟨9487098227096955790843457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25298928605591882108915885 9487098227096955790843457)
      ·
        refine ⟨7115323670322716843132593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9487098227096955790843457 7115323670322716843132593)
        ·
          refine ⟨5336492752742037632349445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7115323670322716843132593 5336492752742037632349445)
          ·
            refine ⟨1000592391139132056065521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5336492752742037632349445 1000592391139132056065521)
            ·
              refine ⟨750444293354349042049141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1000592391139132056065521 750444293354349042049141)
              ·
                refine ⟨70354152501970222692107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 750444293354349042049141 70354152501970222692107)
                ·
                  rfl

theorem cell20_462423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 4, 2, 5].length) (baseStart_462423 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_462423 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_462423 prefixEnd_462423 := by exact prefixLift 462423
  have htrace : WordTrace (prefixWord ++ tailWord_462423) baseStart_462423 baseEnd_462423 := by
    simpa [prefixWord, tailWord_462423, baseEnd_462423] using wordTrace_append hprefix tailTrace_462423
  have hstable : (prefixWord ++ tailWord_462423).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_462423).length < 2 ^ (prefixWord ++ tailWord_462423).sum := by decide
  have hdescent : baseEnd_462423 < baseStart_462423 := by decide
  rcases family_descends (prefixWord ++ tailWord_462423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_462471 : List Nat := [1, 1, 4, 2, 1, 4, 1, 4, 2]
def baseStart_462471 : Nat := 118140960795 + 462471 * 2 ^ 59
def prefixEnd_462471 : Nat := 4983230072969 + 3 ^ 40 * 462471 * 2
def baseEnd_462471 : Nat := 211084366013835834476125

theorem tailTrace_462471 : CollatzResearch.WordTrace tailWord_462471 prefixEnd_462471 211084366013835834476125 := by
  unfold tailWord_462471
  simp only [CollatzResearch.WordTrace]
  refine ⟨16867703107554025603691267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11245135405036017069127511 16867703107554025603691267)
  ·
    refine ⟨25301554661331038405536901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16867703107554025603691267 25301554661331038405536901)
    ·
      refine ⟨4744041498999569701038169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 25301554661331038405536901 4744041498999569701038169)
      ·
        refine ⟨3558031124249677275778627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4744041498999569701038169 3558031124249677275778627)
        ·
          refine ⟨5337046686374515913667941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3558031124249677275778627 5337046686374515913667941)
          ·
            refine ⟨1000696253695221733812739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5337046686374515913667941 1000696253695221733812739)
            ·
              refine ⟨1501044380542832600719109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1000696253695221733812739 1501044380542832600719109)
              ·
                refine ⟨281445821351781112634833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1501044380542832600719109 281445821351781112634833)
                ·
                  refine ⟨211084366013835834476125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 281445821351781112634833 211084366013835834476125)
                  ·
                    rfl

theorem cell20_462471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 4, 1, 4, 2].length) (baseStart_462471 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_462471 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_462471 prefixEnd_462471 := by exact prefixLift 462471
  have htrace : WordTrace (prefixWord ++ tailWord_462471) baseStart_462471 baseEnd_462471 := by
    simpa [prefixWord, tailWord_462471, baseEnd_462471] using wordTrace_append hprefix tailTrace_462471
  have hstable : (prefixWord ++ tailWord_462471).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_462471).length < 2 ^ (prefixWord ++ tailWord_462471).sum := by decide
  have hdescent : baseEnd_462471 < baseStart_462471 := by decide
  rcases family_descends (prefixWord ++ tailWord_462471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_462475 : List Nat := [1, 1, 1, 1, 4, 1, 4, 3, 4]
def baseStart_462475 : Nat := 118140960795 + 462475 * 2 ^ 59
def prefixEnd_462475 : Nat := 4983230072969 + 3 ^ 40 * 462475 * 2
def baseEnd_462475 : Nat := 211086191722829598342775

theorem tailTrace_462475 : CollatzResearch.WordTrace tailWord_462475 prefixEnd_462475 211086191722829598342775 := by
  unfold tailWord_462475
  simp only [CollatzResearch.WordTrace]
  refine ⟨16867848999539534286836879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11245232666359689524557919 16867848999539534286836879)
  ·
    refine ⟨25301773499309301430255319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16867848999539534286836879 25301773499309301430255319)
    ·
      refine ⟨37952660248963952145382979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25301773499309301430255319 37952660248963952145382979)
      ·
        refine ⟨56928990373445928218074469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37952660248963952145382979 56928990373445928218074469)
        ·
          refine ⟨10674185695021111540888963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 56928990373445928218074469 10674185695021111540888963)
          ·
            refine ⟨16011278542531667311333445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10674185695021111540888963 16011278542531667311333445)
            ·
              refine ⟨3002114726724687620875021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16011278542531667311333445 3002114726724687620875021)
              ·
                refine ⟨1125793022521757857828133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3002114726724687620875021 1125793022521757857828133)
                ·
                  refine ⟨211086191722829598342775, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1125793022521757857828133 211086191722829598342775)
                  ·
                    rfl

theorem cell20_462475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 4, 3, 4].length) (baseStart_462475 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_462475 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_462475 prefixEnd_462475 := by exact prefixLift 462475
  have htrace : WordTrace (prefixWord ++ tailWord_462475) baseStart_462475 baseEnd_462475 := by
    simpa [prefixWord, tailWord_462475, baseEnd_462475] using wordTrace_append hprefix tailTrace_462475
  have hstable : (prefixWord ++ tailWord_462475).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_462475).length < 2 ^ (prefixWord ++ tailWord_462475).sum := by decide
  have hdescent : baseEnd_462475 < baseStart_462475 := by decide
  rcases family_descends (prefixWord ++ tailWord_462475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_462478 : List Nat := [4, 1, 1, 3, 1, 4, 1, 5]
def baseStart_462478 : Nat := 118140960795 + 462478 * 2 ^ 59
def prefixEnd_462478 : Nat := 4983230072969 + 3 ^ 40 * 462478 * 2
def baseEnd_462478 : Nat := 70362520334858307080921

theorem tailTrace_462478 : CollatzResearch.WordTrace tailWord_462478 prefixEnd_462478 70362520334858307080921 := by
  unfold tailWord_462478
  simp only [CollatzResearch.WordTrace]
  refine ⟨2108494802316083224899511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11245305612352443866130725 2108494802316083224899511)
  ·
    refine ⟨3162742203474124837349267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2108494802316083224899511 3162742203474124837349267)
    ·
      refine ⟨4744113305211187256023901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3162742203474124837349267 4744113305211187256023901)
      ·
        refine ⟨1779042489454195221008963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4744113305211187256023901 1779042489454195221008963)
        ·
          refine ⟨2668563734181292831513445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1779042489454195221008963 2668563734181292831513445)
          ·
            refine ⟨500355700158992405908771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2668563734181292831513445 500355700158992405908771)
            ·
              refine ⟨750533550238488608863157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 500355700158992405908771 750533550238488608863157)
              ·
                refine ⟨70362520334858307080921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 750533550238488608863157 70362520334858307080921)
                ·
                  rfl

theorem cell20_462478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 4, 1, 5].length) (baseStart_462478 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_462478 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_462478 prefixEnd_462478 := by exact prefixLift 462478
  have htrace : WordTrace (prefixWord ++ tailWord_462478) baseStart_462478 baseEnd_462478 := by
    simpa [prefixWord, tailWord_462478, baseEnd_462478] using wordTrace_append hprefix tailTrace_462478
  have hstable : (prefixWord ++ tailWord_462478).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_462478).length < 2 ^ (prefixWord ++ tailWord_462478).sum := by decide
  have hdescent : baseEnd_462478 < baseStart_462478 := by decide
  rcases family_descends (prefixWord ++ tailWord_462478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_462495 : List Nat := [1, 1, 2, 7, 1, 1, 3, 4]
def baseStart_462495 : Nat := 118140960795 + 462495 * 2 ^ 59
def prefixEnd_462495 : Nat := 4983230072969 + 3 ^ 40 * 462495 * 2
def baseEnd_462495 : Nat := 70365106755932805892009

theorem tailTrace_462495 : CollatzResearch.WordTrace tailWord_462495 prefixEnd_462495 70365106755932805892009 := by
  unfold tailWord_462495
  simp only [CollatzResearch.WordTrace]
  refine ⟨16868578459467077702564939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11245718972978051801709959 16868578459467077702564939)
  ·
    refine ⟨25302867689200616553847409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16868578459467077702564939 25302867689200616553847409)
    ·
      refine ⟨18977150766900462415385557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25302867689200616553847409 18977150766900462415385557)
      ·
        refine ⟨444776971099229587860599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 18977150766900462415385557 444776971099229587860599)
        ·
          refine ⟨667165456648844381790899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 444776971099229587860599 667165456648844381790899)
          ·
            refine ⟨1000748184973266572686349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 667165456648844381790899 1000748184973266572686349)
            ·
              refine ⟨375280569364974964757381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1000748184973266572686349 375280569364974964757381)
              ·
                refine ⟨70365106755932805892009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 375280569364974964757381 70365106755932805892009)
                ·
                  rfl

theorem cell20_462495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 1, 3, 4].length) (baseStart_462495 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_462495 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_462495 prefixEnd_462495 := by exact prefixLift 462495
  have htrace : WordTrace (prefixWord ++ tailWord_462495) baseStart_462495 baseEnd_462495 := by
    simpa [prefixWord, tailWord_462495, baseEnd_462495] using wordTrace_append hprefix tailTrace_462495
  have hstable : (prefixWord ++ tailWord_462495).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_462495).length < 2 ^ (prefixWord ++ tailWord_462495).sum := by decide
  have hdescent : baseEnd_462495 < baseStart_462495 := by decide
  rcases family_descends (prefixWord ++ tailWord_462495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_462499 : List Nat := [1, 1, 1, 4, 1, 1, 7, 4]
def baseStart_462499 : Nat := 118140960795 + 462499 * 2 ^ 59
def prefixEnd_462499 : Nat := 4983230072969 + 3 ^ 40 * 462499 * 2
def baseEnd_462499 : Nat := 70365715325597393847559

theorem tailTrace_462499 : CollatzResearch.WordTrace tailWord_462499 prefixEnd_462499 70365715325597393847559 := by
  unfold tailWord_462499
  simp only [CollatzResearch.WordTrace]
  refine ⟨16868724351452586385710551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11245816234301724257140367 16868724351452586385710551)
  ·
    refine ⟨25303086527178879578565827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16868724351452586385710551 25303086527178879578565827)
    ·
      refine ⟨37954629790768319367848741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25303086527178879578565827 37954629790768319367848741)
      ·
        refine ⟨7116493085769059881471639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 37954629790768319367848741 7116493085769059881471639)
        ·
          refine ⟨10674739628653589822207459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7116493085769059881471639 10674739628653589822207459)
          ·
            refine ⟨16012109442980384733311189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10674739628653589822207459 16012109442980384733311189)
            ·
              refine ⟨375283815069852767186981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 16012109442980384733311189 375283815069852767186981)
              ·
                refine ⟨70365715325597393847559, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 375283815069852767186981 70365715325597393847559)
                ·
                  rfl

theorem cell20_462499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 7, 4].length) (baseStart_462499 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_462499 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_462499 prefixEnd_462499 := by exact prefixLift 462499
  have htrace : WordTrace (prefixWord ++ tailWord_462499) baseStart_462499 baseEnd_462499 := by
    simpa [prefixWord, tailWord_462499, baseEnd_462499] using wordTrace_append hprefix tailTrace_462499
  have hstable : (prefixWord ++ tailWord_462499).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_462499).length < 2 ^ (prefixWord ++ tailWord_462499).sum := by decide
  have hdescent : baseEnd_462499 < baseStart_462499 := by decide
  rcases family_descends (prefixWord ++ tailWord_462499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_462551 : List Nat := [1, 1, 3, 2, 1, 3, 1, 4, 4]
def baseStart_462551 : Nat := 118140960795 + 462551 * 2 ^ 59
def prefixEnd_462551 : Nat := 4983230072969 + 3 ^ 40 * 462551 * 2
def baseEnd_462551 : Nat := 211120880193711111809131

theorem tailTrace_462551 : CollatzResearch.WordTrace tailWord_462551 prefixEnd_462551 211120880193711111809131 := by
  unfold tailWord_462551
  simp only [CollatzResearch.WordTrace]
  refine ⟨16870620947264199266603507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11247080631509466177735671 16870620947264199266603507)
  ·
    refine ⟨25305931420896298899905261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16870620947264199266603507 25305931420896298899905261)
    ·
      refine ⟨9489724282836112087464473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25305931420896298899905261 9489724282836112087464473)
      ·
        refine ⟨7117293212127084065598355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9489724282836112087464473 7117293212127084065598355)
        ·
          refine ⟨10675939818190626098397533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7117293212127084065598355 10675939818190626098397533)
          ·
            refine ⟨4003477431821484786899075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10675939818190626098397533 4003477431821484786899075)
            ·
              refine ⟨6005216147732227180348613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4003477431821484786899075 6005216147732227180348613)
              ·
                refine ⟨1125978027699792596315365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6005216147732227180348613 1125978027699792596315365)
                ·
                  refine ⟨211120880193711111809131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1125978027699792596315365 211120880193711111809131)
                  ·
                    rfl

theorem cell20_462551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 1, 4, 4].length) (baseStart_462551 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_462551 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_462551 prefixEnd_462551 := by exact prefixLift 462551
  have htrace : WordTrace (prefixWord ++ tailWord_462551) baseStart_462551 baseEnd_462551 := by
    simpa [prefixWord, tailWord_462551, baseEnd_462551] using wordTrace_append hprefix tailTrace_462551
  have hstable : (prefixWord ++ tailWord_462551).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_462551).length < 2 ^ (prefixWord ++ tailWord_462551).sum := by decide
  have hdescent : baseEnd_462551 < baseStart_462551 := by decide
  rcases family_descends (prefixWord ++ tailWord_462551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_462554 : List Nat := [3, 1, 1, 2, 2, 5, 2, 4]
def baseStart_462554 : Nat := 118140960795 + 462554 * 2 ^ 59
def prefixEnd_462554 : Nat := 4983230072969 + 3 ^ 40 * 462554 * 2
def baseEnd_462554 : Nat := 70374083158485478236373

theorem tailTrace_462554 : CollatzResearch.WordTrace tailWord_462554 prefixEnd_462554 70374083158485478236373 := by
  unfold tailWord_462554
  simp only [CollatzResearch.WordTrace]
  refine ⟨4217682591563332694740679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11247153577502220519308477 4217682591563332694740679)
  ·
    refine ⟨6326523887344999042111019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4217682591563332694740679 6326523887344999042111019)
    ·
      refine ⟨9489785831017498563166529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6326523887344999042111019 9489785831017498563166529)
      ·
        refine ⟨7117339373263123922374897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9489785831017498563166529 7117339373263123922374897)
        ·
          refine ⟨5338004529947342941781173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7117339373263123922374897 5338004529947342941781173)
          ·
            refine ⟨500437924682563400791985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 5338004529947342941781173 500437924682563400791985)
            ·
              refine ⟨375328443511922550593989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 500437924682563400791985 375328443511922550593989)
              ·
                refine ⟨70374083158485478236373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 375328443511922550593989 70374083158485478236373)
                ·
                  rfl

theorem cell20_462554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 5, 2, 4].length) (baseStart_462554 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_462554 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_462554 prefixEnd_462554 := by exact prefixLift 462554
  have htrace : WordTrace (prefixWord ++ tailWord_462554) baseStart_462554 baseEnd_462554 := by
    simpa [prefixWord, tailWord_462554, baseEnd_462554] using wordTrace_append hprefix tailTrace_462554
  have hstable : (prefixWord ++ tailWord_462554).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_462554).length < 2 ^ (prefixWord ++ tailWord_462554).sum := by decide
  have hdescent : baseEnd_462554 < baseStart_462554 := by decide
  rcases family_descends (prefixWord ++ tailWord_462554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_462589 : List Nat := [1, 4, 1, 1, 1, 1, 2, 5, 4]
def baseStart_462589 : Nat := 118140960795 + 462589 * 2 ^ 59
def prefixEnd_462589 : Nat := 4983230072969 + 3 ^ 40 * 462589 * 2
def baseEnd_462589 : Nat := 211138224429151868542309

theorem tailTrace_462589 : CollatzResearch.WordTrace tailWord_462589 prefixEnd_462589 211138224429151868542309 := by
  unfold tailWord_462589
  simp only [CollatzResearch.WordTrace]
  refine ⟨16872006921126531756486821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11248004614084354504324547 16872006921126531756486821)
  ·
    refine ⟨3163501297711224704341279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16872006921126531756486821 3163501297711224704341279)
    ·
      refine ⟨4745251946566837056511919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3163501297711224704341279 4745251946566837056511919)
      ·
        refine ⟨7117877919850255584767879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4745251946566837056511919 7117877919850255584767879)
        ·
          refine ⟨10676816879775383377151819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7117877919850255584767879 10676816879775383377151819)
          ·
            refine ⟨16015225319663075065727729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10676816879775383377151819 16015225319663075065727729)
            ·
              refine ⟨12011418989747306299295797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16015225319663075065727729 12011418989747306299295797)
              ·
                refine ⟨1126070530288809965558981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12011418989747306299295797 1126070530288809965558981)
                ·
                  refine ⟨211138224429151868542309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1126070530288809965558981 211138224429151868542309)
                  ·
                    rfl

theorem cell20_462589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 5, 4].length) (baseStart_462589 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_462589 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_462589 prefixEnd_462589 := by exact prefixLift 462589
  have htrace : WordTrace (prefixWord ++ tailWord_462589) baseStart_462589 baseEnd_462589 := by
    simpa [prefixWord, tailWord_462589, baseEnd_462589] using wordTrace_append hprefix tailTrace_462589
  have hstable : (prefixWord ++ tailWord_462589).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_462589).length < 2 ^ (prefixWord ++ tailWord_462589).sum := by decide
  have hdescent : baseEnd_462589 < baseStart_462589 := by decide
  rcases family_descends (prefixWord ++ tailWord_462589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_462634 : List Nat := [3, 1, 4, 12]
def baseStart_462634 : Nat := 118140960795 + 462634 * 2 ^ 59
def prefixEnd_462634 : Nat := 4983230072969 + 3 ^ 40 * 462634 * 2
def baseEnd_462634 : Nat := 868966105577496757375

theorem tailTrace_462634 : CollatzResearch.WordTrace tailWord_462634 prefixEnd_462634 868966105577496757375 := by
  unfold tailWord_462634
  simp only [CollatzResearch.WordTrace]
  refine ⟨4218412051490876110468739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11249098803975669627916637 4218412051490876110468739)
  ·
    refine ⟨6327618077236314165703109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4218412051490876110468739 6327618077236314165703109)
    ·
      refine ⟨1186428389481808906069333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6327618077236314165703109 1186428389481808906069333)
      ·
        refine ⟨868966105577496757375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 12 1186428389481808906069333 868966105577496757375)
        ·
          rfl

theorem cell20_462634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 12].length) (baseStart_462634 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_462634 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_462634 prefixEnd_462634 := by exact prefixLift 462634
  have htrace : WordTrace (prefixWord ++ tailWord_462634) baseStart_462634 baseEnd_462634 := by
    simpa [prefixWord, tailWord_462634, baseEnd_462634] using wordTrace_append hprefix tailTrace_462634
  have hstable : (prefixWord ++ tailWord_462634).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_462634).length < 2 ^ (prefixWord ++ tailWord_462634).sum := by decide
  have hdescent : baseEnd_462634 < baseStart_462634 := by decide
  rcases family_descends (prefixWord ++ tailWord_462634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_462665 : List Nat := [1, 2, 1, 1, 2, 4, 3, 2, 4]
def baseStart_462665 : Nat := 118140960795 + 462665 * 2 ^ 59
def prefixEnd_462665 : Nat := 4983230072969 + 3 ^ 40 * 462665 * 2
def baseEnd_462665 : Nat := 211172912900033382008665

theorem tailTrace_462665 : CollatzResearch.WordTrace tailWord_462665 prefixEnd_462665 211172912900033382008665 := by
  unfold tailWord_462665
  simp only [CollatzResearch.WordTrace]
  refine ⟨16874778868851196736253449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11249852579234131157502299 16874778868851196736253449)
  ·
    refine ⟨12656084151638397552190087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16874778868851196736253449 12656084151638397552190087)
    ·
      refine ⟨18984126227457596328285131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12656084151638397552190087 18984126227457596328285131)
      ·
        refine ⟨28476189341186394492427697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18984126227457596328285131 28476189341186394492427697)
        ·
          refine ⟨21357142005889795869320773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28476189341186394492427697 21357142005889795869320773)
          ·
            refine ⟨4004464126104336725497645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21357142005889795869320773 4004464126104336725497645)
            ·
              refine ⟨1501674047289126272061617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4004464126104336725497645 1501674047289126272061617)
              ·
                refine ⟨1126255535466844704046213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1501674047289126272061617 1126255535466844704046213)
                ·
                  refine ⟨211172912900033382008665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1126255535466844704046213 211172912900033382008665)
                  ·
                    rfl

theorem cell20_462665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 3, 2, 4].length) (baseStart_462665 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_462665 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_462665 prefixEnd_462665 := by exact prefixLift 462665
  have htrace : WordTrace (prefixWord ++ tailWord_462665) baseStart_462665 baseEnd_462665 := by
    simpa [prefixWord, tailWord_462665, baseEnd_462665] using wordTrace_append hprefix tailTrace_462665
  have hstable : (prefixWord ++ tailWord_462665).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_462665).length < 2 ^ (prefixWord ++ tailWord_462665).sum := by decide
  have hdescent : baseEnd_462665 < baseStart_462665 := by decide
  rcases family_descends (prefixWord ++ tailWord_462665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_462668 : List Nat := [2, 2, 1, 3, 4, 1, 3, 4]
def baseStart_462668 : Nat := 118140960795 + 462668 * 2 ^ 59
def prefixEnd_462668 : Nat := 4983230072969 + 3 ^ 40 * 462668 * 2
def baseEnd_462668 : Nat := 70391427393926234969551

theorem tailTrace_462668 : CollatzResearch.WordTrace tailWord_462668 prefixEnd_462668 70391427393926234969551 := by
  unfold tailWord_462668
  simp only [CollatzResearch.WordTrace]
  refine ⟨8437444143920164124306329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11249925525226885499075105 8437444143920164124306329)
  ·
    refine ⟨6328083107940123093229747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8437444143920164124306329 6328083107940123093229747)
    ·
      refine ⟨9492124661910184639844621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6328083107940123093229747 9492124661910184639844621)
      ·
        refine ⟨3559546748216319239941733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9492124661910184639844621 3559546748216319239941733)
        ·
          refine ⟨667415015290559857489075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3559546748216319239941733 667415015290559857489075)
          ·
            refine ⟨1001122522935839786233613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 667415015290559857489075 1001122522935839786233613)
            ·
              refine ⟨375420946100939919837605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1001122522935839786233613 375420946100939919837605)
              ·
                refine ⟨70391427393926234969551, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 375420946100939919837605 70391427393926234969551)
                ·
                  rfl

theorem cell20_462668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 1, 3, 4].length) (baseStart_462668 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_462668 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_462668 prefixEnd_462668 := by exact prefixLift 462668
  have htrace : WordTrace (prefixWord ++ tailWord_462668) baseStart_462668 baseEnd_462668 := by
    simpa [prefixWord, tailWord_462668, baseEnd_462668] using wordTrace_append hprefix tailTrace_462668
  have hstable : (prefixWord ++ tailWord_462668).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_462668).length < 2 ^ (prefixWord ++ tailWord_462668).sum := by decide
  have hdescent : baseEnd_462668 < baseStart_462668 := by decide
  rcases family_descends (prefixWord ++ tailWord_462668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_462692 : List Nat := [2, 3, 1, 1, 5, 2, 1, 2, 3]
def baseStart_462692 : Nat := 118140960795 + 462692 * 2 ^ 59
def prefixEnd_462692 : Nat := 4983230072969 + 3 ^ 40 * 462692 * 2
def baseEnd_462692 : Nat := 211185236435741288108555

theorem tailTrace_462692 : CollatzResearch.WordTrace tailWord_462692 prefixEnd_462692 211185236435741288108555 := by
  unfold tailWord_462692
  simp only [CollatzResearch.WordTrace]
  refine ⟨8437881819876690173743165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11250509093168920231657553 8437881819876690173743165)
  ·
    refine ⟨3164205682453758815153687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8437881819876690173743165 3164205682453758815153687)
    ·
      refine ⟨4746308523680638222730531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3164205682453758815153687 4746308523680638222730531)
      ·
        refine ⟨7119462785520957334095797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4746308523680638222730531 7119462785520957334095797)
        ·
          refine ⟨667449636142589750071481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 7119462785520957334095797 667449636142589750071481)
          ·
            refine ⟨500587227106942312553611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 667449636142589750071481 500587227106942312553611)
            ·
              refine ⟨750880840660413468830417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 500587227106942312553611 750880840660413468830417)
              ·
                refine ⟨563160630495310101622813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 750880840660413468830417 563160630495310101622813)
                ·
                  refine ⟨211185236435741288108555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 563160630495310101622813 211185236435741288108555)
                  ·
                    rfl

theorem cell20_462692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 2, 1, 2, 3].length) (baseStart_462692 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_462692 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_462692 prefixEnd_462692 := by exact prefixLift 462692
  have htrace : WordTrace (prefixWord ++ tailWord_462692) baseStart_462692 baseEnd_462692 := by
    simpa [prefixWord, tailWord_462692, baseEnd_462692] using wordTrace_append hprefix tailTrace_462692
  have hstable : (prefixWord ++ tailWord_462692).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_462692).length < 2 ^ (prefixWord ++ tailWord_462692).sum := by decide
  have hdescent : baseEnd_462692 < baseStart_462692 := by decide
  rcases family_descends (prefixWord ++ tailWord_462692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_462696 : List Nat := [2, 1, 4, 2, 1, 1, 3, 1, 5]
def baseStart_462696 : Nat := 118140960795 + 462696 * 2 ^ 59
def prefixEnd_462696 : Nat := 4983230072969 + 3 ^ 40 * 462696 * 2
def baseEnd_462696 : Nat := 211187062144735051975205

theorem tailTrace_462696 : CollatzResearch.WordTrace tailWord_462696 prefixEnd_462696 211187062144735051975205 := by
  unfold tailWord_462696
  simp only [CollatzResearch.WordTrace]
  refine ⟨8437954765869444515315971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11250606354492592687087961 8437954765869444515315971)
  ·
    refine ⟨12656932148804166772973957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8437954765869444515315971 12656932148804166772973957)
    ·
      refine ⟨2373174777900781269932617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12656932148804166772973957 2373174777900781269932617)
      ·
        refine ⟨1779881083425585952449463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2373174777900781269932617 1779881083425585952449463)
        ·
          refine ⟨2669821625138378928674195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1779881083425585952449463 2669821625138378928674195)
          ·
            refine ⟨4004732437707568393011293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2669821625138378928674195 4004732437707568393011293)
            ·
              refine ⟨1501774664140338147379235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4004732437707568393011293 1501774664140338147379235)
              ·
                refine ⟨2252661996210507221068853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1501774664140338147379235 2252661996210507221068853)
                ·
                  refine ⟨211187062144735051975205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2252661996210507221068853 211187062144735051975205)
                  ·
                    rfl

theorem cell20_462696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 3, 1, 5].length) (baseStart_462696 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_462696 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_462696 prefixEnd_462696 := by exact prefixLift 462696
  have htrace : WordTrace (prefixWord ++ tailWord_462696) baseStart_462696 baseEnd_462696 := by
    simpa [prefixWord, tailWord_462696, baseEnd_462696] using wordTrace_append hprefix tailTrace_462696
  have hstable : (prefixWord ++ tailWord_462696).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_462696).length < 2 ^ (prefixWord ++ tailWord_462696).sum := by decide
  have hdescent : baseEnd_462696 < baseStart_462696 := by decide
  rcases family_descends (prefixWord ++ tailWord_462696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_462713 : List Nat := [1, 2, 1, 3, 2, 2, 5, 1, 3]
def baseStart_462713 : Nat := 118140960795 + 462713 * 2 ^ 59
def prefixEnd_462713 : Nat := 4983230072969 + 3 ^ 40 * 462713 * 2
def baseEnd_462713 : Nat := 211194821407958548408469

theorem tailTrace_462713 : CollatzResearch.WordTrace tailWord_462713 prefixEnd_462713 211194821407958548408469 := by
  unfold tailWord_462713
  simp only [CollatzResearch.WordTrace]
  refine ⟨16876529572677300934000793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11251019715118200622667195 16876529572677300934000793)
  ·
    refine ⟨12657397179507975700500595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16876529572677300934000793 12657397179507975700500595)
    ·
      refine ⟨18986095769261963550750893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12657397179507975700500595 18986095769261963550750893)
      ·
        refine ⟨7119785913473236331531585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18986095769261963550750893 7119785913473236331531585)
        ·
          refine ⟨5339839435104927248648689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7119785913473236331531585 5339839435104927248648689)
          ·
            refine ⟨4004879576328695436486517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5339839435104927248648689 4004879576328695436486517)
            ·
              refine ⟨375457460280815197170611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4004879576328695436486517 375457460280815197170611)
              ·
                refine ⟨563186190421222795755917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 375457460280815197170611 563186190421222795755917)
                ·
                  refine ⟨211194821407958548408469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 563186190421222795755917 211194821407958548408469)
                  ·
                    rfl

theorem cell20_462713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 5, 1, 3].length) (baseStart_462713 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_462713 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_462713 prefixEnd_462713 := by exact prefixLift 462713
  have htrace : WordTrace (prefixWord ++ tailWord_462713) baseStart_462713 baseEnd_462713 := by
    simpa [prefixWord, tailWord_462713, baseEnd_462713] using wordTrace_append hprefix tailTrace_462713
  have hstable : (prefixWord ++ tailWord_462713).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_462713).length < 2 ^ (prefixWord ++ tailWord_462713).sum := by decide
  have hdescent : baseEnd_462713 < baseStart_462713 := by decide
  rcases family_descends (prefixWord ++ tailWord_462713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_462727 : List Nat := [1, 1, 4, 2, 4, 1, 1, 6]
def baseStart_462727 : Nat := 118140960795 + 462727 * 2 ^ 59
def prefixEnd_462727 : Nat := 4983230072969 + 3 ^ 40 * 462727 * 2
def baseEnd_462727 : Nat := 70400403796478907313915

theorem tailTrace_462727 : CollatzResearch.WordTrace tailWord_462727 prefixEnd_462727 70400403796478907313915 := by
  unfold tailWord_462727
  simp only [CollatzResearch.WordTrace]
  refine ⟨16877040194626581325010435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11251360129751054216673623 16877040194626581325010435)
  ·
    refine ⟨25315560291939871987515653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16877040194626581325010435 25315560291939871987515653)
    ·
      refine ⟨4746667554738725997659185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 25315560291939871987515653 4746667554738725997659185)
      ·
        refine ⟨3560000666054044498244389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4746667554738725997659185 3560000666054044498244389)
        ·
          refine ⟨667500124885133343420823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3560000666054044498244389 667500124885133343420823)
          ·
            refine ⟨1001250187327700015131235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 667500124885133343420823 1001250187327700015131235)
            ·
              refine ⟨1501875280991550022696853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1001250187327700015131235 1501875280991550022696853)
              ·
                refine ⟨70400403796478907313915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1501875280991550022696853 70400403796478907313915)
                ·
                  rfl

theorem cell20_462727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 1, 1, 6].length) (baseStart_462727 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_462727 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_462727 prefixEnd_462727 := by exact prefixLift 462727
  have htrace : WordTrace (prefixWord ++ tailWord_462727) baseStart_462727 baseEnd_462727 := by
    simpa [prefixWord, tailWord_462727, baseEnd_462727] using wordTrace_append hprefix tailTrace_462727
  have hstable : (prefixWord ++ tailWord_462727).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_462727).length < 2 ^ (prefixWord ++ tailWord_462727).sum := by decide
  have hdescent : baseEnd_462727 < baseStart_462727 := by decide
  rcases family_descends (prefixWord ++ tailWord_462727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_462744 : List Nat := [2, 1, 2, 6, 1, 2, 6]
def baseStart_462744 : Nat := 118140960795 + 462744 * 2 ^ 59
def prefixEnd_462744 : Nat := 4983230072969 + 3 ^ 40 * 462744 * 2
def baseEnd_462744 : Nat := 23467663405851135375001

theorem tailTrace_462744 : CollatzResearch.WordTrace tailWord_462744 prefixEnd_462744 23467663405851135375001 := by
  unfold tailWord_462744
  simp only [CollatzResearch.WordTrace]
  refine ⟨8438830117782496614189643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11251773490376662152252857 8438830117782496614189643)
  ·
    refine ⟨12658245176673744921284465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8438830117782496614189643 12658245176673744921284465)
    ·
      refine ⟨9493683882505308690963349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12658245176673744921284465 9493683882505308690963349)
      ·
        refine ⟨445016431992436344888907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 9493683882505308690963349 445016431992436344888907)
        ·
          refine ⟨667524647988654517333361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 445016431992436344888907 667524647988654517333361)
          ·
            refine ⟨500643485991490888000021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 667524647988654517333361 500643485991490888000021)
            ·
              refine ⟨23467663405851135375001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 500643485991490888000021 23467663405851135375001)
              ·
                rfl

theorem cell20_462744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 2, 6].length) (baseStart_462744 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_462744 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_462744 prefixEnd_462744 := by exact prefixLift 462744
  have htrace : WordTrace (prefixWord ++ tailWord_462744) baseStart_462744 baseEnd_462744 := by
    simpa [prefixWord, tailWord_462744, baseEnd_462744] using wordTrace_append hprefix tailTrace_462744
  have hstable : (prefixWord ++ tailWord_462744).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_462744).length < 2 ^ (prefixWord ++ tailWord_462744).sum := by decide
  have hdescent : baseEnd_462744 < baseStart_462744 := by decide
  rcases family_descends (prefixWord ++ tailWord_462744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_462750 : List Nat := [4, 3, 1, 3, 1, 1, 3, 2, 2]
def baseStart_462750 : Nat := 118140960795 + 462750 * 2 ^ 59
def prefixEnd_462750 : Nat := 4983230072969 + 3 ^ 40 * 462750 * 2
def baseEnd_462750 : Nat := 211211709216150864174985

theorem tailTrace_462750 : CollatzResearch.WordTrace tailWord_462750 prefixEnd_462750 211211709216150864174985 := by
  unfold tailWord_462750
  simp only [CollatzResearch.WordTrace]
  refine ⟨2109734884192907031637213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11251919382362170835398469 2109734884192907031637213)
  ·
    refine ⟨791150581572340136863955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2109734884192907031637213 791150581572340136863955)
    ·
      refine ⟨1186725872358510205295933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 791150581572340136863955 1186725872358510205295933)
      ·
        refine ⟨445022202134441326985975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1186725872358510205295933 445022202134441326985975)
        ·
          refine ⟨667533303201661990478963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 445022202134441326985975 667533303201661990478963)
          ·
            refine ⟨1001299954802492985718445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 667533303201661990478963 1001299954802492985718445)
            ·
              refine ⟨375487483050934869644417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1001299954802492985718445 375487483050934869644417)
              ·
                refine ⟨281615612288201152233313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 375487483050934869644417 281615612288201152233313)
                ·
                  refine ⟨211211709216150864174985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 281615612288201152233313 211211709216150864174985)
                  ·
                    rfl

theorem cell20_462750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 1, 3, 2, 2].length) (baseStart_462750 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_462750 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_462750 prefixEnd_462750 := by exact prefixLift 462750
  have htrace : WordTrace (prefixWord ++ tailWord_462750) baseStart_462750 baseEnd_462750 := by
    simpa [prefixWord, tailWord_462750, baseEnd_462750] using wordTrace_append hprefix tailTrace_462750
  have hstable : (prefixWord ++ tailWord_462750).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_462750).length < 2 ^ (prefixWord ++ tailWord_462750).sum := by decide
  have hdescent : baseEnd_462750 < baseStart_462750 := by decide
  rcases family_descends (prefixWord ++ tailWord_462750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_462754 : List Nat := [3, 3, 1, 2, 4, 1, 1, 1, 4]
def baseStart_462754 : Nat := 118140960795 + 462754 * 2 ^ 59
def prefixEnd_462754 : Nat := 4983230072969 + 3 ^ 40 * 462754 * 2
def baseEnd_462754 : Nat := 211213534925144628041635

theorem tailTrace_462754 : CollatzResearch.WordTrace tailWord_462754 prefixEnd_462754 211213534925144628041635 := by
  unfold tailWord_462754
  simp only [CollatzResearch.WordTrace]
  refine ⟨4219506241382191234060829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11252016643685843290828877 4219506241382191234060829)
  ·
    refine ⟨1582314840518321712772811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4219506241382191234060829 1582314840518321712772811)
    ·
      refine ⟨2373472260777482569159217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1582314840518321712772811 2373472260777482569159217)
      ·
        refine ⟨1780104195583111926869413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2373472260777482569159217 1780104195583111926869413)
        ·
          refine ⟨333769536671833486288015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1780104195583111926869413 333769536671833486288015)
          ·
            refine ⟨500654305007750229432023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 333769536671833486288015 500654305007750229432023)
            ·
              refine ⟨750981457511625344148035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 500654305007750229432023 750981457511625344148035)
              ·
                refine ⟨1126472186267438016222053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 750981457511625344148035 1126472186267438016222053)
                ·
                  refine ⟨211213534925144628041635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1126472186267438016222053 211213534925144628041635)
                  ·
                    rfl

theorem cell20_462754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 4, 1, 1, 1, 4].length) (baseStart_462754 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_462754 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_462754 prefixEnd_462754 := by exact prefixLift 462754
  have htrace : WordTrace (prefixWord ++ tailWord_462754) baseStart_462754 baseEnd_462754 := by
    simpa [prefixWord, tailWord_462754, baseEnd_462754] using wordTrace_append hprefix tailTrace_462754
  have hstable : (prefixWord ++ tailWord_462754).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_462754).length < 2 ^ (prefixWord ++ tailWord_462754).sum := by decide
  have hdescent : baseEnd_462754 < baseStart_462754 := by decide
  rcases family_descends (prefixWord ++ tailWord_462754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_462809 : List Nat := [1, 2, 1, 2, 7, 1, 2, 2, 2]
def baseStart_462809 : Nat := 118140960795 + 462809 * 2 ^ 59
def prefixEnd_462809 : Nat := 4983230072969 + 3 ^ 40 * 462809 * 2
def baseEnd_462809 : Nat := 211238638423808881208077

theorem tailTrace_462809 : CollatzResearch.WordTrace tailWord_462809 prefixEnd_462809 211238638423808881208077 := by
  unfold tailWord_462809
  simp only [CollatzResearch.WordTrace]
  refine ⟨16880030980329509329495481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11253353986886339552996987 16880030980329509329495481)
  ·
    refine ⟨12660023235247131997121611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16880030980329509329495481 12660023235247131997121611)
    ·
      refine ⟨18990034852870697995682417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12660023235247131997121611 18990034852870697995682417)
      ·
        refine ⟨14242526139653023496761813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18990034852870697995682417 14242526139653023496761813)
        ·
          refine ⟨333809206398117738205355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 14242526139653023496761813 333809206398117738205355)
          ·
            refine ⟨500713809597176607308033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 333809206398117738205355 500713809597176607308033)
            ·
              refine ⟨375535357197882455481025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 500713809597176607308033 375535357197882455481025)
              ·
                refine ⟨281651517898411841610769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 375535357197882455481025 281651517898411841610769)
                ·
                  refine ⟨211238638423808881208077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 281651517898411841610769 211238638423808881208077)
                  ·
                    rfl

theorem cell20_462809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 7, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 7, 1, 2, 2, 2].length) (baseStart_462809 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_462809 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_462809 prefixEnd_462809 := by exact prefixLift 462809
  have htrace : WordTrace (prefixWord ++ tailWord_462809) baseStart_462809 baseEnd_462809 := by
    simpa [prefixWord, tailWord_462809, baseEnd_462809] using wordTrace_append hprefix tailTrace_462809
  have hstable : (prefixWord ++ tailWord_462809).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_462809).length < 2 ^ (prefixWord ++ tailWord_462809).sum := by decide
  have hdescent : baseEnd_462809 < baseStart_462809 := by decide
  rcases family_descends (prefixWord ++ tailWord_462809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_462841 : List Nat := [1, 2, 1, 3, 1, 5, 3, 4]
def baseStart_462841 : Nat := 118140960795 + 462841 * 2 ^ 59
def prefixEnd_462841 : Nat := 4983230072969 + 3 ^ 40 * 462841 * 2
def baseEnd_462841 : Nat := 70417748031919664047093

theorem tailTrace_462841 : CollatzResearch.WordTrace tailWord_462841 prefixEnd_462841 70417748031919664047093 := by
  unfold tailWord_462841
  simp only [CollatzResearch.WordTrace]
  refine ⟨16881198116213578794660377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11254132077475719196440251 16881198116213578794660377)
  ·
    refine ⟨12660898587160184095995283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16881198116213578794660377 12660898587160184095995283)
    ·
      refine ⟨18991347880740276143992925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12660898587160184095995283 18991347880740276143992925)
      ·
        refine ⟨7121755455277603553997347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18991347880740276143992925 7121755455277603553997347)
        ·
          refine ⟨10682633182916405330996021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7121755455277603553997347 10682633182916405330996021)
          ·
            refine ⟨1001496860898412999780877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 10682633182916405330996021 1001496860898412999780877)
            ·
              refine ⟨375561322836904874917829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1001496860898412999780877 375561322836904874917829)
              ·
                refine ⟨70417748031919664047093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 375561322836904874917829 70417748031919664047093)
                ·
                  rfl

theorem cell20_462841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 5, 3, 4].length) (baseStart_462841 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_462841 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_462841 prefixEnd_462841 := by exact prefixLift 462841
  have htrace : WordTrace (prefixWord ++ tailWord_462841) baseStart_462841 baseEnd_462841 := by
    simpa [prefixWord, tailWord_462841, baseEnd_462841] using wordTrace_append hprefix tailTrace_462841
  have hstable : (prefixWord ++ tailWord_462841).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_462841).length < 2 ^ (prefixWord ++ tailWord_462841).sum := by decide
  have hdescent : baseEnd_462841 < baseStart_462841 := by decide
  rcases family_descends (prefixWord ++ tailWord_462841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_462854 : List Nat := [6, 2, 1, 2, 1, 1, 7]
def baseStart_462854 : Nat := 118140960795 + 462854 * 2 ^ 59
def prefixEnd_462854 : Nat := 4983230072969 + 3 ^ 40 * 462854 * 2
def baseEnd_462854 : Nat := 23473241961109858300877

theorem tailTrace_462854 : CollatzResearch.WordTrace tailWord_462854 prefixEnd_462854 23473241961109858300877 := by
  unfold tailWord_462854
  simp only [CollatzResearch.WordTrace]
  refine ⟨527552258286452562965113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 11254448176777654676589077 527552258286452562965113)
  ·
    refine ⟨395664193714839422223835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 527552258286452562965113 395664193714839422223835)
    ·
      refine ⟨593496290572259133335753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 395664193714839422223835 593496290572259133335753)
      ·
        refine ⟨445122217929194350001815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 593496290572259133335753 445122217929194350001815)
        ·
          refine ⟨667683326893791525002723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 445122217929194350001815 667683326893791525002723)
          ·
            refine ⟨1001524990340687287504085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 667683326893791525002723 1001524990340687287504085)
            ·
              refine ⟨23473241961109858300877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1001524990340687287504085 23473241961109858300877)
              ·
                rfl

theorem cell20_462854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 1, 7].length) (baseStart_462854 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_462854 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_462854 prefixEnd_462854 := by exact prefixLift 462854
  have htrace : WordTrace (prefixWord ++ tailWord_462854) baseStart_462854 baseEnd_462854 := by
    simpa [prefixWord, tailWord_462854, baseEnd_462854] using wordTrace_append hprefix tailTrace_462854
  have hstable : (prefixWord ++ tailWord_462854).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_462854).length < 2 ^ (prefixWord ++ tailWord_462854).sum := by decide
  have hdescent : baseEnd_462854 < baseStart_462854 := by decide
  rcases family_descends (prefixWord ++ tailWord_462854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_462861 : List Nat := [1, 7, 1, 2, 1, 1, 1, 1, 5]
def baseStart_462861 : Nat := 118140960795 + 462861 * 2 ^ 59
def prefixEnd_462861 : Nat := 4983230072969 + 3 ^ 40 * 462861 * 2
def baseEnd_462861 : Nat := 211262372640727811474531

theorem tailTrace_462861 : CollatzResearch.WordTrace tailWord_462861 prefixEnd_462861 211262372640727811474531 := by
  unfold tailWord_462861
  simp only [CollatzResearch.WordTrace]
  refine ⟨16881927576141122210388437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11254618384094081473592291 16881927576141122210388437)
  ·
    refine ⟨395670177565807551805979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 16881927576141122210388437 395670177565807551805979)
    ·
      refine ⟨593505266348711327708969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 395670177565807551805979 593505266348711327708969)
      ·
        refine ⟨445128949761533495781727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 593505266348711327708969 445128949761533495781727)
        ·
          refine ⟨667693424642300243672591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 445128949761533495781727 667693424642300243672591)
          ·
            refine ⟨1001540136963450365508887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 667693424642300243672591 1001540136963450365508887)
            ·
              refine ⟨1502310205445175548263331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1001540136963450365508887 1502310205445175548263331)
              ·
                refine ⟨2253465308167763322394997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1502310205445175548263331 2253465308167763322394997)
                ·
                  refine ⟨211262372640727811474531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2253465308167763322394997 211262372640727811474531)
                  ·
                    rfl

theorem cell20_462861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 1, 1, 1, 5].length) (baseStart_462861 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_462861 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_462861 prefixEnd_462861 := by exact prefixLift 462861
  have htrace : WordTrace (prefixWord ++ tailWord_462861) baseStart_462861 baseEnd_462861 := by
    simpa [prefixWord, tailWord_462861, baseEnd_462861] using wordTrace_append hprefix tailTrace_462861
  have hstable : (prefixWord ++ tailWord_462861).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_462861).length < 2 ^ (prefixWord ++ tailWord_462861).sum := by decide
  have hdescent : baseEnd_462861 < baseStart_462861 := by decide
  rcases family_descends (prefixWord ++ tailWord_462861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_462862 : List Nat := [4, 1, 1, 2, 2, 1, 9]
def baseStart_462862 : Nat := 118140960795 + 462862 * 2 ^ 59
def prefixEnd_462862 : Nat := 4983230072969 + 3 ^ 40 * 462862 * 2
def baseEnd_462862 : Nat := 23473647674219583604577

theorem tailTrace_462862 : CollatzResearch.WordTrace tailWord_462862 prefixEnd_462862 23473647674219583604577 := by
  unfold tailWord_462862
  simp only [CollatzResearch.WordTrace]
  refine ⟨2110245506142187422646855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11254642699424999587449893 2110245506142187422646855)
  ·
    refine ⟨3165368259213281133970283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2110245506142187422646855 3165368259213281133970283)
    ·
      refine ⟨4748052388819921700955425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3165368259213281133970283 4748052388819921700955425)
      ·
        refine ⟨3561039291614941275716569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4748052388819921700955425 3561039291614941275716569)
        ·
          refine ⟨2670779468711205956787427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3561039291614941275716569 2670779468711205956787427)
          ·
            refine ⟨4006169203066808935181141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2670779468711205956787427 4006169203066808935181141)
            ·
              refine ⟨23473647674219583604577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 4006169203066808935181141 23473647674219583604577)
              ·
                rfl

theorem cell20_462862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 9].length) (baseStart_462862 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_462862 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_462862 prefixEnd_462862 := by exact prefixLift 462862
  have htrace : WordTrace (prefixWord ++ tailWord_462862) baseStart_462862 baseEnd_462862 := by
    simpa [prefixWord, tailWord_462862, baseEnd_462862] using wordTrace_append hprefix tailTrace_462862
  have hstable : (prefixWord ++ tailWord_462862).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_462862).length < 2 ^ (prefixWord ++ tailWord_462862).sum := by decide
  have hdescent : baseEnd_462862 < baseStart_462862 := by decide
  rcases family_descends (prefixWord ++ tailWord_462862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan20Incremental
