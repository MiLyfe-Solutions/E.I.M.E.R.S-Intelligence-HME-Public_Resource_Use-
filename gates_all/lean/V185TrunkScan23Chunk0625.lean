import V185TrunkScan23Chunk0624

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_3696281 : List Nat := [1, 2, 1, 2, 1, 2, 2, 4, 1, 5, 2]
def baseStart_3696281 : Nat := 118140960795 + 3696281 * 2 ^ 59
def prefixEnd_3696281 : Nat := 4983230072969 + 3 ^ 40 * 3696281 * 2
def baseEnd_3696281 : Nat := 1897968787081558017288619

theorem tailTrace_3696281 : CollatzResearch.WordTrace tailWord_3696281 prefixEnd_3696281 1897968787081558017288619 := by
  unfold tailWord_3696281
  simp only [CollatzResearch.WordTrace]
  refine ⟨134814443522012686381576697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89876295681341790921051131 134814443522012686381576697)
  ·
    refine ⟨101110832641509514786182523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134814443522012686381576697 101110832641509514786182523)
    ·
      refine ⟨151666248962264272179273785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101110832641509514786182523 151666248962264272179273785)
      ·
        refine ⟨113749686721698204134455339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 151666248962264272179273785 113749686721698204134455339)
        ·
          refine ⟨170624530082547306201683009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113749686721698204134455339 170624530082547306201683009)
          ·
            refine ⟨127968397561910479651262257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 170624530082547306201683009 127968397561910479651262257)
            ·
              refine ⟨95976298171432859738446693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 127968397561910479651262257 95976298171432859738446693)
              ·
                refine ⟨17995555907143661200958755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 95976298171432859738446693 17995555907143661200958755)
                ·
                  refine ⟨26993333860715491801438133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17995555907143661200958755 26993333860715491801438133)
                  ·
                    refine ⟨2530625049442077356384825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 26993333860715491801438133 2530625049442077356384825)
                    ·
                      refine ⟨1897968787081558017288619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2530625049442077356384825 1897968787081558017288619)
                      ·
                        rfl

theorem cell23_3696281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 4, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 4, 1, 5, 2].length) (baseStart_3696281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3696281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3696281 prefixEnd_3696281 := by exact prefixLift 3696281
  have htrace : WordTrace (prefixWord ++ tailWord_3696281) baseStart_3696281 baseEnd_3696281 := by
    simpa [prefixWord, tailWord_3696281, baseEnd_3696281] using wordTrace_append hprefix tailTrace_3696281
  have hstable : (prefixWord ++ tailWord_3696281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3696281).length < 2 ^ (prefixWord ++ tailWord_3696281).sum := by decide
  have hdescent : baseEnd_3696281 < baseStart_3696281 := by decide
  rcases family_descends (prefixWord ++ tailWord_3696281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3696304 : List Nat := [2, 1, 1, 1, 2, 1, 5, 1, 3, 6]
def baseStart_3696304 : Nat := 118140960795 + 3696304 * 2 ^ 59
def prefixEnd_3696304 : Nat := 4983230072969 + 3 ^ 40 * 3696304 * 2
def baseEnd_3696304 : Nat := 632660199045537142433671

theorem tailTrace_3696304 : CollatzResearch.WordTrace tailWord_3696304 prefixEnd_3696304 632660199045537142433671 := by
  unfold tailWord_3696304
  simp only [CollatzResearch.WordTrace]
  refine ⟨67407641200464680654831983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89876854933952907539775977 67407641200464680654831983)
  ·
    refine ⟨101111461800697020982247975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67407641200464680654831983 101111461800697020982247975)
    ·
      refine ⟨151667192701045531473371963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101111461800697020982247975 151667192701045531473371963)
      ·
        refine ⟨227500789051568297210057945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151667192701045531473371963 227500789051568297210057945)
        ·
          refine ⟨170625591788676222907543459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 227500789051568297210057945 170625591788676222907543459)
          ·
            refine ⟨255938387683014334361315189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 170625591788676222907543459 255938387683014334361315189)
            ·
              refine ⟨23994223845282593846373299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 255938387683014334361315189 23994223845282593846373299)
              ·
                refine ⟨35991335767923890769559949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23994223845282593846373299 35991335767923890769559949)
                ·
                  refine ⟨13496750912971459038584981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35991335767923890769559949 13496750912971459038584981)
                  ·
                    refine ⟨632660199045537142433671, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13496750912971459038584981 632660199045537142433671)
                    ·
                      rfl

theorem cell23_3696304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 5, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 5, 1, 3, 6].length) (baseStart_3696304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3696304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3696304 prefixEnd_3696304 := by exact prefixLift 3696304
  have htrace : WordTrace (prefixWord ++ tailWord_3696304) baseStart_3696304 baseEnd_3696304 := by
    simpa [prefixWord, tailWord_3696304, baseEnd_3696304] using wordTrace_append hprefix tailTrace_3696304
  have hstable : (prefixWord ++ tailWord_3696304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3696304).length < 2 ^ (prefixWord ++ tailWord_3696304).sum := by decide
  have hdescent : baseEnd_3696304 < baseStart_3696304 := by decide
  rcases family_descends (prefixWord ++ tailWord_3696304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3696338 : List Nat := [3, 2, 2, 2, 2, 2, 2, 1, 1, 6]
def baseStart_3696338 : Nat := 118140960795 + 3696338 * 2 ^ 59
def prefixEnd_3696338 : Nat := 4983230072969 + 3 ^ 40 * 3696338 * 2
def baseEnd_3696338 : Nat := 632666018492954764758619

theorem tailTrace_3696338 : CollatzResearch.WordTrace tailWord_3696338 prefixEnd_3696338 632666018492954764758619 := by
  unfold tailWord_3696338
  simp only [CollatzResearch.WordTrace]
  refine ⟨33704130620701546279100417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89877681655204123410934445 33704130620701546279100417)
  ·
    refine ⟨25278097965526159709325313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33704130620701546279100417 25278097965526159709325313)
    ·
      refine ⟨18958573474144619781993985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25278097965526159709325313 18958573474144619781993985)
      ·
        refine ⟨14218930105608464836495489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18958573474144619781993985 14218930105608464836495489)
        ·
          refine ⟨10664197579206348627371617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14218930105608464836495489 10664197579206348627371617)
          ·
            refine ⟨7998148184404761470528713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10664197579206348627371617 7998148184404761470528713)
            ·
              refine ⟨5998611138303571102896535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7998148184404761470528713 5998611138303571102896535)
              ·
                refine ⟨8997916707455356654344803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5998611138303571102896535 8997916707455356654344803)
                ·
                  refine ⟨13496875061183034981517205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8997916707455356654344803 13496875061183034981517205)
                  ·
                    refine ⟨632666018492954764758619, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13496875061183034981517205 632666018492954764758619)
                    ·
                      rfl

theorem cell23_3696338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 2, 2, 1, 1, 6].length) (baseStart_3696338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3696338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3696338 prefixEnd_3696338 := by exact prefixLift 3696338
  have htrace : WordTrace (prefixWord ++ tailWord_3696338) baseStart_3696338 baseEnd_3696338 := by
    simpa [prefixWord, tailWord_3696338, baseEnd_3696338] using wordTrace_append hprefix tailTrace_3696338
  have hstable : (prefixWord ++ tailWord_3696338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3696338).length < 2 ^ (prefixWord ++ tailWord_3696338).sum := by decide
  have hdescent : baseEnd_3696338 < baseStart_3696338 := by decide
  rcases family_descends (prefixWord ++ tailWord_3696338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3696345 : List Nat := [1, 2, 1, 2, 3, 4, 1, 2, 3, 2, 2]
def baseStart_3696345 : Nat := 118140960795 + 3696345 * 2 ^ 59
def prefixEnd_3696345 : Nat := 4983230072969 + 3 ^ 40 * 3696345 * 2
def baseEnd_3696345 : Nat := 1898001649843445766888325

theorem tailTrace_3696345 : CollatzResearch.WordTrace tailWord_3696345 prefixEnd_3696345 1898001649843445766888325 := by
  unfold tailWord_3696345
  simp only [CollatzResearch.WordTrace]
  refine ⟨134816777793780825311906489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89877851862520550207937659 134816777793780825311906489)
  ·
    refine ⟨101112583345335618983929867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134816777793780825311906489 101112583345335618983929867)
    ·
      refine ⟨151668875018003428475894801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101112583345335618983929867 151668875018003428475894801)
      ·
        refine ⟨113751656263502571356921101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 151668875018003428475894801 113751656263502571356921101)
        ·
          refine ⟨42656871098813464258845413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 113751656263502571356921101 42656871098813464258845413)
          ·
            refine ⟨7998163331027524548533515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 42656871098813464258845413 7998163331027524548533515)
            ·
              refine ⟨11997244996541286822800273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7998163331027524548533515 11997244996541286822800273)
              ·
                refine ⟨8997933747405965117100205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11997244996541286822800273 8997933747405965117100205)
                ·
                  refine ⟨3374225155277236918912577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8997933747405965117100205 3374225155277236918912577)
                  ·
                    refine ⟨2530668866457927689184433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3374225155277236918912577 2530668866457927689184433)
                    ·
                      refine ⟨1898001649843445766888325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2530668866457927689184433 1898001649843445766888325)
                      ·
                        rfl

theorem cell23_3696345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 4, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 4, 1, 2, 3, 2, 2].length) (baseStart_3696345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3696345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3696345 prefixEnd_3696345 := by exact prefixLift 3696345
  have htrace : WordTrace (prefixWord ++ tailWord_3696345) baseStart_3696345 baseEnd_3696345 := by
    simpa [prefixWord, tailWord_3696345, baseEnd_3696345] using wordTrace_append hprefix tailTrace_3696345
  have hstable : (prefixWord ++ tailWord_3696345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3696345).length < 2 ^ (prefixWord ++ tailWord_3696345).sum := by decide
  have hdescent : baseEnd_3696345 < baseStart_3696345 := by decide
  rcases family_descends (prefixWord ++ tailWord_3696345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3696349 : List Nat := [1, 4, 3, 3, 1, 2, 1, 1, 2, 3, 2]
def baseStart_3696349 : Nat := 118140960795 + 3696349 * 2 ^ 59
def prefixEnd_3696349 : Nat := 4983230072969 + 3 ^ 40 * 3696349 * 2
def baseEnd_3696349 : Nat := 1898003703766063751238307

theorem tailTrace_3696349 : CollatzResearch.WordTrace tailWord_3696349 prefixEnd_3696349 1898003703766063751238307 := by
  unfold tailWord_3696349
  simp only [CollatzResearch.WordTrace]
  refine ⟨134816923685766333995052101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89877949123844222663368067 134816923685766333995052101)
  ·
    refine ⟨25278173191081187624072269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 134816923685766333995052101 25278173191081187624072269)
    ·
      refine ⟨9479314946655445359027101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25278173191081187624072269 9479314946655445359027101)
      ·
        refine ⟨3554743104995792009635163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9479314946655445359027101 3554743104995792009635163)
        ·
          refine ⟨5332114657493688014452745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3554743104995792009635163 5332114657493688014452745)
          ·
            refine ⟨3999085993120266010839559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5332114657493688014452745 3999085993120266010839559)
            ·
              refine ⟨5998628989680399016259339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3999085993120266010839559 5998628989680399016259339)
              ·
                refine ⟨8997943484520598524389009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5998628989680399016259339 8997943484520598524389009)
                ·
                  refine ⟨6748457613390448893291757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8997943484520598524389009 6748457613390448893291757)
                  ·
                    refine ⟨2530671605021418334984409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6748457613390448893291757 2530671605021418334984409)
                    ·
                      refine ⟨1898003703766063751238307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2530671605021418334984409 1898003703766063751238307)
                      ·
                        rfl

theorem cell23_3696349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 2, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 2, 1, 1, 2, 3, 2].length) (baseStart_3696349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3696349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3696349 prefixEnd_3696349 := by exact prefixLift 3696349
  have htrace : WordTrace (prefixWord ++ tailWord_3696349) baseStart_3696349 baseEnd_3696349 := by
    simpa [prefixWord, tailWord_3696349, baseEnd_3696349] using wordTrace_append hprefix tailTrace_3696349
  have hstable : (prefixWord ++ tailWord_3696349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3696349).length < 2 ^ (prefixWord ++ tailWord_3696349).sum := by decide
  have hdescent : baseEnd_3696349 < baseStart_3696349 := by decide
  rcases family_descends (prefixWord ++ tailWord_3696349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3696351 : List Nat := [1, 1, 2, 3, 2, 2, 5, 7]
def baseStart_3696351 : Nat := 118140960795 + 3696351 * 2 ^ 59
def prefixEnd_3696351 : Nat := 4983230072969 + 3 ^ 40 * 3696351 * 2
def baseEnd_3696351 : Nat := 70296471508421212719011

theorem tailTrace_3696351 : CollatzResearch.WordTrace tailWord_3696351 prefixEnd_3696351 70296471508421212719011 := by
  unfold tailWord_3696351
  simp only [CollatzResearch.WordTrace]
  refine ⟨134816996631759088336624907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89877997754506058891083271 134816996631759088336624907)
  ·
    refine ⟨202225494947638632504937361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134816996631759088336624907 202225494947638632504937361)
    ·
      refine ⟨151669121210728974378703021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 202225494947638632504937361 151669121210728974378703021)
      ·
        refine ⟨56875920454023365392013633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 151669121210728974378703021 56875920454023365392013633)
        ·
          refine ⟨42656940340517524044010225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56875920454023365392013633 42656940340517524044010225)
          ·
            refine ⟨31992705255388143033007669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42656940340517524044010225 31992705255388143033007669)
            ·
              refine ⟨2999316117692638409344469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 31992705255388143033007669 2999316117692638409344469)
              ·
                refine ⟨70296471508421212719011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2999316117692638409344469 70296471508421212719011)
                ·
                  rfl

theorem cell23_3696351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 5, 7].length) (baseStart_3696351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3696351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3696351 prefixEnd_3696351 := by exact prefixLift 3696351
  have htrace : WordTrace (prefixWord ++ tailWord_3696351) baseStart_3696351 baseEnd_3696351 := by
    simpa [prefixWord, tailWord_3696351, baseEnd_3696351] using wordTrace_append hprefix tailTrace_3696351
  have hstable : (prefixWord ++ tailWord_3696351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3696351).length < 2 ^ (prefixWord ++ tailWord_3696351).sum := by decide
  have hdescent : baseEnd_3696351 < baseStart_3696351 := by decide
  rcases family_descends (prefixWord ++ tailWord_3696351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3696359 : List Nat := [1, 1, 5, 4, 2, 1, 2, 1, 1, 5]
def baseStart_3696359 : Nat := 118140960795 + 3696359 * 2 ^ 59
def prefixEnd_3696359 : Nat := 4983230072969 + 3 ^ 40 * 3696359 * 2
def baseEnd_3696359 : Nat := 632669612857536237371087

theorem tailTrace_3696359 : CollatzResearch.WordTrace tailWord_3696359 prefixEnd_3696359 632669612857536237371087 := by
  unfold tailWord_3696359
  simp only [CollatzResearch.WordTrace]
  refine ⟨134817288415730105702916131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89878192277153403801944087 134817288415730105702916131)
  ·
    refine ⟨202225932623595158554374197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134817288415730105702916131 202225932623595158554374197)
    ·
      refine ⟨18958681183462046114472581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 202225932623595158554374197 18958681183462046114472581)
      ·
        refine ⟨3554752721899133646463609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18958681183462046114472581 3554752721899133646463609)
        ·
          refine ⟨2666064541424350234847707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3554752721899133646463609 2666064541424350234847707)
          ·
            refine ⟨3999096812136525352271561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2666064541424350234847707 3999096812136525352271561)
            ·
              refine ⟨2999322609102394014203671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3999096812136525352271561 2999322609102394014203671)
              ·
                refine ⟨4498983913653591021305507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2999322609102394014203671 4498983913653591021305507)
                ·
                  refine ⟨6748475870480386531958261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4498983913653591021305507 6748475870480386531958261)
                  ·
                    refine ⟨632669612857536237371087, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6748475870480386531958261 632669612857536237371087)
                    ·
                      rfl

theorem cell23_3696359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 2, 1, 2, 1, 1, 5].length) (baseStart_3696359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3696359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3696359 prefixEnd_3696359 := by exact prefixLift 3696359
  have htrace : WordTrace (prefixWord ++ tailWord_3696359) baseStart_3696359 baseEnd_3696359 := by
    simpa [prefixWord, tailWord_3696359, baseEnd_3696359] using wordTrace_append hprefix tailTrace_3696359
  have hstable : (prefixWord ++ tailWord_3696359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3696359).length < 2 ^ (prefixWord ++ tailWord_3696359).sum := by decide
  have hdescent : baseEnd_3696359 < baseStart_3696359 := by decide
  rcases family_descends (prefixWord ++ tailWord_3696359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3696362 : List Nat := [3, 1, 3, 1, 1, 1, 3, 5, 1, 2, 2]
def baseStart_3696362 : Nat := 118140960795 + 3696362 * 2 ^ 59
def prefixEnd_3696362 : Nat := 4983230072969 + 3 ^ 40 * 3696362 * 2
def baseEnd_3696362 : Nat := 1898010379014572200375747

theorem tailTrace_3696362 : CollatzResearch.WordTrace tailWord_3696362 prefixEnd_3696362 1898010379014572200375747 := by
  unfold tailWord_3696362
  simp only [CollatzResearch.WordTrace]
  refine ⟨33704349458679809303818835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89878265223146158143516893 33704349458679809303818835)
  ·
    refine ⟨50556524188019713955728253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33704349458679809303818835 50556524188019713955728253)
    ·
      refine ⟨18958696570507392733398095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50556524188019713955728253 18958696570507392733398095)
      ·
        refine ⟨28438044855761089100097143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18958696570507392733398095 28438044855761089100097143)
        ·
          refine ⟨42657067283641633650145715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28438044855761089100097143 42657067283641633650145715)
          ·
            refine ⟨63985600925462450475218573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42657067283641633650145715 63985600925462450475218573)
            ·
              refine ⟨23994600347048418928206965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 63985600925462450475218573 23994600347048418928206965)
              ·
                refine ⟨2249493782535789274519403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 23994600347048418928206965 2249493782535789274519403)
                ·
                  refine ⟨3374240673803683911779105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2249493782535789274519403 3374240673803683911779105)
                  ·
                    refine ⟨2530680505352762933834329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3374240673803683911779105 2530680505352762933834329)
                    ·
                      refine ⟨1898010379014572200375747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2530680505352762933834329 1898010379014572200375747)
                      ·
                        rfl

theorem cell23_3696362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 3, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 3, 5, 1, 2, 2].length) (baseStart_3696362 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3696362 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3696362 prefixEnd_3696362 := by exact prefixLift 3696362
  have htrace : WordTrace (prefixWord ++ tailWord_3696362) baseStart_3696362 baseEnd_3696362 := by
    simpa [prefixWord, tailWord_3696362, baseEnd_3696362] using wordTrace_append hprefix tailTrace_3696362
  have hstable : (prefixWord ++ tailWord_3696362).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3696362).length < 2 ^ (prefixWord ++ tailWord_3696362).sum := by decide
  have hdescent : baseEnd_3696362 < baseStart_3696362 := by decide
  rcases family_descends (prefixWord ++ tailWord_3696362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3696365 : List Nat := [1, 5, 1, 2, 1, 3, 1, 3, 1, 2, 3]
def baseStart_3696365 : Nat := 118140960795 + 3696365 * 2 ^ 59
def prefixEnd_3696365 : Nat := 4983230072969 + 3 ^ 40 * 3696365 * 2
def baseEnd_3696365 : Nat := 1898011919456535688638233

theorem tailTrace_3696365 : CollatzResearch.WordTrace tailWord_3696365 prefixEnd_3696365 1898011919456535688638233 := by
  unfold tailWord_3696365
  simp only [CollatzResearch.WordTrace]
  refine ⟨134817507253708368727634549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89878338169138912485089699 134817507253708368727634549)
  ·
    refine ⟨12639141305035159568215739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 134817507253708368727634549 12639141305035159568215739)
    ·
      refine ⟨18958711957552739352323609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12639141305035159568215739 18958711957552739352323609)
      ·
        refine ⟨14219033968164554514242707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18958711957552739352323609 14219033968164554514242707)
        ·
          refine ⟨21328550952246831771364061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14219033968164554514242707 21328550952246831771364061)
          ·
            refine ⟨7998206607092561914261523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21328550952246831771364061 7998206607092561914261523)
            ·
              refine ⟨11997309910638842871392285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7998206607092561914261523 11997309910638842871392285)
              ·
                refine ⟨4498991216489566076772107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11997309910638842871392285 4498991216489566076772107)
                ·
                  refine ⟨6748486824734349115158161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4498991216489566076772107 6748486824734349115158161)
                  ·
                    refine ⟨5061365118550761836368621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6748486824734349115158161 5061365118550761836368621)
                    ·
                      refine ⟨1898011919456535688638233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5061365118550761836368621 1898011919456535688638233)
                      ·
                        rfl

theorem cell23_3696365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 3, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 3, 1, 3, 1, 2, 3].length) (baseStart_3696365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3696365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3696365 prefixEnd_3696365 := by exact prefixLift 3696365
  have htrace : WordTrace (prefixWord ++ tailWord_3696365) baseStart_3696365 baseEnd_3696365 := by
    simpa [prefixWord, tailWord_3696365, baseEnd_3696365] using wordTrace_append hprefix tailTrace_3696365
  have hstable : (prefixWord ++ tailWord_3696365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3696365).length < 2 ^ (prefixWord ++ tailWord_3696365).sum := by decide
  have hdescent : baseEnd_3696365 < baseStart_3696365 := by decide
  rcases family_descends (prefixWord ++ tailWord_3696365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3696372 : List Nat := [2, 6, 1, 1, 1, 2, 1, 1, 4, 4]
def baseStart_3696372 : Nat := 118140960795 + 3696372 * 2 ^ 59
def prefixEnd_3696372 : Nat := 4983230072969 + 3 ^ 40 * 3696372 * 2
def baseEnd_3696372 : Nat := 632671837940372387083567

theorem tailTrace_3696372 : CollatzResearch.WordTrace tailWord_3696372 prefixEnd_3696372 632671837940372387083567 := by
  unfold tailWord_3696372
  simp only [CollatzResearch.WordTrace]
  refine ⟨67408881282341504461569685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89878508376455339282092913 67408881282341504461569685)
  ·
    refine ⟨3159791310109758021636079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 67408881282341504461569685 3159791310109758021636079)
    ·
      refine ⟨4739686965164637032454119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3159791310109758021636079 4739686965164637032454119)
      ·
        refine ⟨7109530447746955548681179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4739686965164637032454119 7109530447746955548681179)
        ·
          refine ⟨10664295671620433323021769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7109530447746955548681179 10664295671620433323021769)
          ·
            refine ⟨7998221753715324992266327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10664295671620433323021769 7998221753715324992266327)
            ·
              refine ⟨11997332630572987488399491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7998221753715324992266327 11997332630572987488399491)
              ·
                refine ⟨17995998945859481232599237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11997332630572987488399491 17995998945859481232599237)
                ·
                  refine ⟨3374249802348652731112357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17995998945859481232599237 3374249802348652731112357)
                  ·
                    refine ⟨632671837940372387083567, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3374249802348652731112357 632671837940372387083567)
                    ·
                      rfl

theorem cell23_3696372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 2, 1, 1, 4, 4].length) (baseStart_3696372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3696372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3696372 prefixEnd_3696372 := by exact prefixLift 3696372
  have htrace : WordTrace (prefixWord ++ tailWord_3696372) baseStart_3696372 baseEnd_3696372 := by
    simpa [prefixWord, tailWord_3696372, baseEnd_3696372] using wordTrace_append hprefix tailTrace_3696372
  have hstable : (prefixWord ++ tailWord_3696372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3696372).length < 2 ^ (prefixWord ++ tailWord_3696372).sum := by decide
  have hdescent : baseEnd_3696372 < baseStart_3696372 := by decide
  rcases family_descends (prefixWord ++ tailWord_3696372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3696405 : List Nat := [1, 3, 2, 1, 2, 3, 1, 4, 1, 3, 2]
def baseStart_3696405 : Nat := 118140960795 + 3696405 * 2 ^ 59
def prefixEnd_3696405 : Nat := 4983230072969 + 3 ^ 40 * 3696405 * 2
def baseEnd_3696405 : Nat := 1898032458682715532138049

theorem tailTrace_3696405 : CollatzResearch.WordTrace tailWord_3696405 prefixEnd_3696405 1898032458682715532138049 := by
  unfold tailWord_3696405
  simp only [CollatzResearch.WordTrace]
  refine ⟨134818966173563455559090669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89879310782375637039393779 134818966173563455559090669)
  ·
    refine ⟨50557112315086295834659001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 134818966173563455559090669 50557112315086295834659001)
    ·
      refine ⟨37917834236314721875994251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50557112315086295834659001 37917834236314721875994251)
      ·
        refine ⟨56876751354472082813991377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37917834236314721875994251 56876751354472082813991377)
        ·
          refine ⟨42657563515854062110493533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56876751354472082813991377 42657563515854062110493533)
          ·
            refine ⟨15996586318445273291435075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42657563515854062110493533 15996586318445273291435075)
            ·
              refine ⟨23994879477667909937152613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15996586318445273291435075 23994879477667909937152613)
              ·
                refine ⟨4499039902062733113216115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23994879477667909937152613 4499039902062733113216115)
                ·
                  refine ⟨6748559853094099669824173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4499039902062733113216115 6748559853094099669824173)
                  ·
                    refine ⟨2530709944910287376184065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6748559853094099669824173 2530709944910287376184065)
                    ·
                      refine ⟨1898032458682715532138049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2530709944910287376184065 1898032458682715532138049)
                      ·
                        rfl

theorem cell23_3696405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 1, 4, 1, 3, 2].length) (baseStart_3696405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3696405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3696405 prefixEnd_3696405 := by exact prefixLift 3696405
  have htrace : WordTrace (prefixWord ++ tailWord_3696405) baseStart_3696405 baseEnd_3696405 := by
    simpa [prefixWord, tailWord_3696405, baseEnd_3696405] using wordTrace_append hprefix tailTrace_3696405
  have hstable : (prefixWord ++ tailWord_3696405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3696405).length < 2 ^ (prefixWord ++ tailWord_3696405).sum := by decide
  have hdescent : baseEnd_3696405 < baseStart_3696405 := by decide
  rcases family_descends (prefixWord ++ tailWord_3696405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3696421 : List Nat := [1, 3, 1, 2, 3, 2, 1, 1, 1, 3, 5]
def baseStart_3696421 : Nat := 118140960795 + 3696421 * 2 ^ 59
def prefixEnd_3696421 : Nat := 4983230072969 + 3 ^ 40 * 3696421 * 2
def baseEnd_3696421 : Nat := 1898040674373187469537975

theorem tailTrace_3696421 : CollatzResearch.WordTrace tailWord_3696421 prefixEnd_3696421 1898040674373187469537975 := by
  unfold tailWord_3696421
  simp only [CollatzResearch.WordTrace]
  refine ⟨134819549741505490291673117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89879699827670326861115411 134819549741505490291673117)
  ·
    refine ⟨50557331153064558859377419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 134819549741505490291673117 50557331153064558859377419)
    ·
      refine ⟨75835996729596838289066129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50557331153064558859377419 75835996729596838289066129)
      ·
        refine ⟨56876997547197628716799597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75835996729596838289066129 56876997547197628716799597)
        ·
          refine ⟨21328874080199110768799849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56876997547197628716799597 21328874080199110768799849)
          ·
            refine ⟨15996655560149333076599887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21328874080199110768799849 15996655560149333076599887)
            ·
              refine ⟨23994983340223999614899831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15996655560149333076599887 23994983340223999614899831)
              ·
                refine ⟨35992475010335999422349747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23994983340223999614899831 35992475010335999422349747)
                ·
                  refine ⟨53988712515503999133524621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35992475010335999422349747 53988712515503999133524621)
                  ·
                    refine ⟨20245767193313999675071733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 53988712515503999133524621 20245767193313999675071733)
                    ·
                      refine ⟨1898040674373187469537975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20245767193313999675071733 1898040674373187469537975)
                      ·
                        rfl

theorem cell23_3696421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 1, 1, 1, 3, 5].length) (baseStart_3696421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3696421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3696421 prefixEnd_3696421 := by exact prefixLift 3696421
  have htrace : WordTrace (prefixWord ++ tailWord_3696421) baseStart_3696421 baseEnd_3696421 := by
    simpa [prefixWord, tailWord_3696421, baseEnd_3696421] using wordTrace_append hprefix tailTrace_3696421
  have hstable : (prefixWord ++ tailWord_3696421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3696421).length < 2 ^ (prefixWord ++ tailWord_3696421).sum := by decide
  have hdescent : baseEnd_3696421 < baseStart_3696421 := by decide
  rcases family_descends (prefixWord ++ tailWord_3696421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3696481 : List Nat := [1, 2, 3, 1, 1, 1, 3, 1, 3, 2, 5]
def baseStart_3696481 : Nat := 118140960795 + 3696481 * 2 ^ 59
def prefixEnd_3696481 : Nat := 4983230072969 + 3 ^ 40 * 3696481 * 2
def baseEnd_3696481 : Nat := 1898071483212457234787699

theorem tailTrace_3696481 : CollatzResearch.WordTrace tailWord_3696481 prefixEnd_3696481 1898071483212457234787699 := by
  unfold tailWord_3696481
  simp only [CollatzResearch.WordTrace]
  refine ⟨134821738121288120538857297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89881158747525413692571531 134821738121288120538857297)
  ·
    refine ⟨101116303590966090404142973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134821738121288120538857297 101116303590966090404142973)
    ·
      refine ⟨37918613846612283901553615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 101116303590966090404142973 37918613846612283901553615)
      ·
        refine ⟨56877920769918425852330423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37918613846612283901553615 56877920769918425852330423)
        ·
          refine ⟨85316881154877638778495635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56877920769918425852330423 85316881154877638778495635)
          ·
            refine ⟨127975321732316458167743453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85316881154877638778495635 127975321732316458167743453)
            ·
              refine ⟨47990745649618671812903795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 127975321732316458167743453 47990745649618671812903795)
              ·
                refine ⟨71986118474428007719355693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47990745649618671812903795 71986118474428007719355693)
                ·
                  refine ⟨26994794427910502894758385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 71986118474428007719355693 26994794427910502894758385)
                  ·
                    refine ⟨20246095820932877171068789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26994794427910502894758385 20246095820932877171068789)
                    ·
                      refine ⟨1898071483212457234787699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20246095820932877171068789 1898071483212457234787699)
                      ·
                        rfl

theorem cell23_3696481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 3, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 3, 1, 3, 2, 5].length) (baseStart_3696481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3696481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3696481 prefixEnd_3696481 := by exact prefixLift 3696481
  have htrace : WordTrace (prefixWord ++ tailWord_3696481) baseStart_3696481 baseEnd_3696481 := by
    simpa [prefixWord, tailWord_3696481, baseEnd_3696481] using wordTrace_append hprefix tailTrace_3696481
  have hstable : (prefixWord ++ tailWord_3696481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3696481).length < 2 ^ (prefixWord ++ tailWord_3696481).sum := by decide
  have hdescent : baseEnd_3696481 < baseStart_3696481 := by decide
  rcases family_descends (prefixWord ++ tailWord_3696481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3696488 : List Nat := [2, 1, 4, 2, 1, 1, 1, 4, 2, 5]
def baseStart_3696488 : Nat := 118140960795 + 3696488 * 2 ^ 59
def prefixEnd_3696488 : Nat := 4983230072969 + 3 ^ 40 * 3696488 * 2
def baseEnd_3696488 : Nat := 632691692525679569133389

theorem tailTrace_3696488 : CollatzResearch.WordTrace tailWord_3696488 prefixEnd_3696488 632691692525679569133389 := by
  unfold tailWord_3696488
  simp only [CollatzResearch.WordTrace]
  refine ⟨67410996716131380367181059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89881328954841840489574745 67410996716131380367181059)
  ·
    refine ⟨101116495074197070550771589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67410996716131380367181059 101116495074197070550771589)
    ·
      refine ⟨18959342826411950728269673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 101116495074197070550771589 18959342826411950728269673)
      ·
        refine ⟨14219507119808963046202255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18959342826411950728269673 14219507119808963046202255)
        ·
          refine ⟨21329260679713444569303383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14219507119808963046202255 21329260679713444569303383)
          ·
            refine ⟨31993891019570166853955075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21329260679713444569303383 31993891019570166853955075)
            ·
              refine ⟨47990836529355250280932613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31993891019570166853955075 47990836529355250280932613)
              ·
                refine ⟨8998281849254109427674865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 47990836529355250280932613 8998281849254109427674865)
                ·
                  refine ⟨6748711386940582070756149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8998281849254109427674865 6748711386940582070756149)
                  ·
                    refine ⟨632691692525679569133389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6748711386940582070756149 632691692525679569133389)
                    ·
                      rfl

theorem cell23_3696488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 1, 4, 2, 5].length) (baseStart_3696488 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3696488 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3696488 prefixEnd_3696488 := by exact prefixLift 3696488
  have htrace : WordTrace (prefixWord ++ tailWord_3696488) baseStart_3696488 baseEnd_3696488 := by
    simpa [prefixWord, tailWord_3696488, baseEnd_3696488] using wordTrace_append hprefix tailTrace_3696488
  have hstable : (prefixWord ++ tailWord_3696488).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3696488).length < 2 ^ (prefixWord ++ tailWord_3696488).sum := by decide
  have hdescent : baseEnd_3696488 < baseStart_3696488 := by decide
  rcases family_descends (prefixWord ++ tailWord_3696488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3696491 : List Nat := [1, 1, 1, 1, 2, 2, 3, 2, 3, 3, 4]
def baseStart_3696491 : Nat := 118140960795 + 3696491 * 2 ^ 59
def prefixEnd_3696491 : Nat := 4983230072969 + 3 ^ 40 * 3696491 * 2
def baseEnd_3696491 : Nat := 1898076618019002195662653

theorem tailTrace_3696491 : CollatzResearch.WordTrace tailWord_3696491 prefixEnd_3696491 1898076618019002195662653 := by
  unfold tailWord_3696491
  simp only [CollatzResearch.WordTrace]
  refine ⟨134822102851251892246721327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89881401900834594831147551 134822102851251892246721327)
  ·
    refine ⟨202233154276877838370081991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134822102851251892246721327 202233154276877838370081991)
    ·
      refine ⟨303349731415316757555122987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 202233154276877838370081991 303349731415316757555122987)
      ·
        refine ⟨455024597122975136332684481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 303349731415316757555122987 455024597122975136332684481)
        ·
          refine ⟨341268447842231352249513361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 455024597122975136332684481 341268447842231352249513361)
          ·
            refine ⟨255951335881673514187135021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 341268447842231352249513361 255951335881673514187135021)
            ·
              refine ⟨95981750955627567820175633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 255951335881673514187135021 95981750955627567820175633)
              ·
                refine ⟨71986313216720675865131725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 95981750955627567820175633 71986313216720675865131725)
                ·
                  refine ⟨26994867456270253449424397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 71986313216720675865131725 26994867456270253449424397)
                  ·
                    refine ⟨10123075296101345043534149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26994867456270253449424397 10123075296101345043534149)
                    ·
                      refine ⟨1898076618019002195662653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10123075296101345043534149 1898076618019002195662653)
                      ·
                        rfl

theorem cell23_3696491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 2, 3, 3, 4].length) (baseStart_3696491 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3696491 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3696491 prefixEnd_3696491 := by exact prefixLift 3696491
  have htrace : WordTrace (prefixWord ++ tailWord_3696491) baseStart_3696491 baseEnd_3696491 := by
    simpa [prefixWord, tailWord_3696491, baseEnd_3696491] using wordTrace_append hprefix tailTrace_3696491
  have hstable : (prefixWord ++ tailWord_3696491).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3696491).length < 2 ^ (prefixWord ++ tailWord_3696491).sum := by decide
  have hdescent : baseEnd_3696491 < baseStart_3696491 := by decide
  rcases family_descends (prefixWord ++ tailWord_3696491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3696492 : List Nat := [2, 2, 1, 1, 4, 4, 2, 2, 5]
def baseStart_3696492 : Nat := 118140960795 + 3696492 * 2 ^ 59
def prefixEnd_3696492 : Nat := 4983230072969 + 3 ^ 40 * 3696492 * 2
def baseEnd_3696492 : Nat := 210897459055517410194461

theorem tailTrace_3696492 : CollatzResearch.WordTrace tailWord_3696492 prefixEnd_3696492 210897459055517410194461 := by
  unfold tailWord_3696492
  simp only [CollatzResearch.WordTrace]
  refine ⟨67411069662124134708753865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89881426216165512945005153 67411069662124134708753865)
  ·
    refine ⟨50558302246593101031565399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67411069662124134708753865 50558302246593101031565399)
    ·
      refine ⟨75837453369889651547348099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50558302246593101031565399 75837453369889651547348099)
      ·
        refine ⟨113756180054834477321022149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75837453369889651547348099 113756180054834477321022149)
        ·
          refine ⟨21329283760281464497691653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 113756180054834477321022149 21329283760281464497691653)
          ·
            refine ⟨3999240705052774593317185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21329283760281464497691653 3999240705052774593317185)
            ·
              refine ⟨2999430528789580944987889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3999240705052774593317185 2999430528789580944987889)
              ·
                refine ⟨2249572896592185708740917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2999430528789580944987889 2249572896592185708740917)
                ·
                  refine ⟨210897459055517410194461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2249572896592185708740917 210897459055517410194461)
                  ·
                    rfl

theorem cell23_3696492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 4, 2, 2, 5].length) (baseStart_3696492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3696492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3696492 prefixEnd_3696492 := by exact prefixLift 3696492
  have htrace : WordTrace (prefixWord ++ tailWord_3696492) baseStart_3696492 baseEnd_3696492 := by
    simpa [prefixWord, tailWord_3696492, baseEnd_3696492] using wordTrace_append hprefix tailTrace_3696492
  have hstable : (prefixWord ++ tailWord_3696492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3696492).length < 2 ^ (prefixWord ++ tailWord_3696492).sum := by decide
  have hdescent : baseEnd_3696492 < baseStart_3696492 := by decide
  rcases family_descends (prefixWord ++ tailWord_3696492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3696502 : List Nat := [5, 1, 1, 3, 2, 1, 1, 1, 2, 3, 3]
def baseStart_3696502 : Nat := 118140960795 + 3696502 * 2 ^ 59
def prefixEnd_3696502 : Nat := 4983230072969 + 3 ^ 40 * 3696502 * 2
def baseEnd_3696502 : Nat := 1898082266306201652625103

theorem tailTrace_3696502 : CollatzResearch.WordTrace tailWord_3696502 prefixEnd_3696502 1898082266306201652625103 := by
  unfold tailWord_3696502
  simp only [CollatzResearch.WordTrace]
  refine ⟨8426406503388252570335735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 89881669369474694083581173 8426406503388252570335735)
  ·
    refine ⟨12639609755082378855503603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8426406503388252570335735 12639609755082378855503603)
    ·
      refine ⟨18959414632623568283255405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12639609755082378855503603 18959414632623568283255405)
      ·
        refine ⟨7109780487233838106220777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18959414632623568283255405 7109780487233838106220777)
        ·
          refine ⟨5332335365425378579665583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7109780487233838106220777 5332335365425378579665583)
          ·
            refine ⟨7998503048138067869498375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5332335365425378579665583 7998503048138067869498375)
            ·
              refine ⟨11997754572207101804247563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7998503048138067869498375 11997754572207101804247563)
              ·
                refine ⟨17996631858310652706371345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11997754572207101804247563 17996631858310652706371345)
                ·
                  refine ⟨13497473893732989529778509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17996631858310652706371345 13497473893732989529778509)
                  ·
                    refine ⟨5061552710149871073666941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13497473893732989529778509 5061552710149871073666941)
                    ·
                      refine ⟨1898082266306201652625103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5061552710149871073666941 1898082266306201652625103)
                      ·
                        rfl

theorem cell23_3696502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 1, 1, 1, 2, 3, 3].length) (baseStart_3696502 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3696502 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3696502 prefixEnd_3696502 := by exact prefixLift 3696502
  have htrace : WordTrace (prefixWord ++ tailWord_3696502) baseStart_3696502 baseEnd_3696502 := by
    simpa [prefixWord, tailWord_3696502, baseEnd_3696502] using wordTrace_append hprefix tailTrace_3696502
  have hstable : (prefixWord ++ tailWord_3696502).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3696502).length < 2 ^ (prefixWord ++ tailWord_3696502).sum := by decide
  have hdescent : baseEnd_3696502 < baseStart_3696502 := by decide
  rcases family_descends (prefixWord ++ tailWord_3696502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3696522 : List Nat := [3, 1, 2, 4, 2, 2, 1, 1, 2, 5]
def baseStart_3696522 : Nat := 118140960795 + 3696522 * 2 ^ 59
def prefixEnd_3696522 : Nat := 4983230072969 + 3 ^ 40 * 3696522 * 2
def baseEnd_3696522 : Nat := 632697511973097191458337

theorem tailTrace_3696522 : CollatzResearch.WordTrace tailWord_3696522 prefixEnd_3696522 632697511973097191458337 := by
  unfold tailWord_3696522
  simp only [CollatzResearch.WordTrace]
  refine ⟨33705808378534896135274955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89882155676093056360733213 33705808378534896135274955)
  ·
    refine ⟨50558712567802344202912433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33705808378534896135274955 50558712567802344202912433)
    ·
      refine ⟨37919034425851758152184325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50558712567802344202912433 37919034425851758152184325)
      ·
        refine ⟨7109818954847204653534561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 37919034425851758152184325 7109818954847204653534561)
        ·
          refine ⟨5332364216135403490150921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7109818954847204653534561 5332364216135403490150921)
          ·
            refine ⟨3999273162101552617613191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5332364216135403490150921 3999273162101552617613191)
            ·
              refine ⟨5998909743152328926419787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3999273162101552617613191 5998909743152328926419787)
              ·
                refine ⟨8998364614728493389629681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5998909743152328926419787 8998364614728493389629681)
                ·
                  refine ⟨6748773461046370042222261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8998364614728493389629681 6748773461046370042222261)
                  ·
                    refine ⟨632697511973097191458337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6748773461046370042222261 632697511973097191458337)
                    ·
                      rfl

theorem cell23_3696522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 2, 1, 1, 2, 5].length) (baseStart_3696522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3696522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3696522 prefixEnd_3696522 := by exact prefixLift 3696522
  have htrace : WordTrace (prefixWord ++ tailWord_3696522) baseStart_3696522 baseEnd_3696522 := by
    simpa [prefixWord, tailWord_3696522, baseEnd_3696522] using wordTrace_append hprefix tailTrace_3696522
  have hstable : (prefixWord ++ tailWord_3696522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3696522).length < 2 ^ (prefixWord ++ tailWord_3696522).sum := by decide
  have hdescent : baseEnd_3696522 < baseStart_3696522 := by decide
  rcases family_descends (prefixWord ++ tailWord_3696522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3696538 : List Nat := [3, 1, 1, 4, 2, 1, 1, 1, 2, 1, 6]
def baseStart_3696538 : Nat := 118140960795 + 3696538 * 2 ^ 59
def prefixEnd_3696538 : Nat := 4983230072969 + 3 ^ 40 * 3696538 * 2
def baseEnd_3696538 : Nat := 1898100751609763511774937

theorem tailTrace_3696538 : CollatzResearch.WordTrace tailWord_3696538 prefixEnd_3696538 1898100751609763511774937 := by
  unfold tailWord_3696538
  simp only [CollatzResearch.WordTrace]
  refine ⟨33705954270520404818420567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89882544721387746182454845 33705954270520404818420567)
  ·
    refine ⟨50558931405780607227630851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33705954270520404818420567 50558931405780607227630851)
    ·
      refine ⟨75838397108670910841446277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50558931405780607227630851 75838397108670910841446277)
      ·
        refine ⟨14219699457875795782771177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 75838397108670910841446277 14219699457875795782771177)
        ·
          refine ⟨10664774593406846837078383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14219699457875795782771177 10664774593406846837078383)
          ·
            refine ⟨15997161890110270255617575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10664774593406846837078383 15997161890110270255617575)
            ·
              refine ⟨23995742835165405383426363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15997161890110270255617575 23995742835165405383426363)
              ·
                refine ⟨35993614252748108075139545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23995742835165405383426363 35993614252748108075139545)
                ·
                  refine ⟨26995210689561081056354659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35993614252748108075139545 26995210689561081056354659)
                  ·
                    refine ⟨40492816034341621584531989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26995210689561081056354659 40492816034341621584531989)
                    ·
                      refine ⟨1898100751609763511774937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 40492816034341621584531989 1898100751609763511774937)
                      ·
                        rfl

theorem cell23_3696538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 1, 1, 2, 1, 6].length) (baseStart_3696538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3696538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3696538 prefixEnd_3696538 := by exact prefixLift 3696538
  have htrace : WordTrace (prefixWord ++ tailWord_3696538) baseStart_3696538 baseEnd_3696538 := by
    simpa [prefixWord, tailWord_3696538, baseEnd_3696538] using wordTrace_append hprefix tailTrace_3696538
  have hstable : (prefixWord ++ tailWord_3696538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3696538).length < 2 ^ (prefixWord ++ tailWord_3696538).sum := by decide
  have hdescent : baseEnd_3696538 < baseStart_3696538 := by decide
  rcases family_descends (prefixWord ++ tailWord_3696538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3696548 : List Nat := [2, 3, 1, 2, 1, 4, 1, 1, 8]
def baseStart_3696548 : Nat := 118140960795 + 3696548 * 2 ^ 59
def prefixEnd_3696548 : Nat := 4983230072969 + 3 ^ 40 * 3696548 * 2
def baseEnd_3696548 : Nat := 210900654046256496961099

theorem tailTrace_3696548 : CollatzResearch.WordTrace tailWord_3696548 prefixEnd_3696548 210900654046256496961099 := by
  unfold tailWord_3696548
  simp only [CollatzResearch.WordTrace]
  refine ⟨67412090906022695490773149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89882787874696927321030865 67412090906022695490773149)
  ·
    refine ⟨25279534089758510809039931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67412090906022695490773149 25279534089758510809039931)
    ·
      refine ⟨37919301134637766213559897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25279534089758510809039931 37919301134637766213559897)
      ·
        refine ⟨28439475850978324660169923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37919301134637766213559897 28439475850978324660169923)
        ·
          refine ⟨42659213776467486990254885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28439475850978324660169923 42659213776467486990254885)
          ·
            refine ⟨7998602583087653810672791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 42659213776467486990254885 7998602583087653810672791)
            ·
              refine ⟨11997903874631480716009187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7998602583087653810672791 11997903874631480716009187)
              ·
                refine ⟨17996855811947221074013781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11997903874631480716009187 17996855811947221074013781)
                ·
                  refine ⟨210900654046256496961099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 17996855811947221074013781 210900654046256496961099)
                  ·
                    rfl

theorem cell23_3696548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 4, 1, 1, 8].length) (baseStart_3696548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3696548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3696548 prefixEnd_3696548 := by exact prefixLift 3696548
  have htrace : WordTrace (prefixWord ++ tailWord_3696548) baseStart_3696548 baseEnd_3696548 := by
    simpa [prefixWord, tailWord_3696548, baseEnd_3696548] using wordTrace_append hprefix tailTrace_3696548
  have hstable : (prefixWord ++ tailWord_3696548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3696548).length < 2 ^ (prefixWord ++ tailWord_3696548).sum := by decide
  have hdescent : baseEnd_3696548 < baseStart_3696548 := by decide
  rcases family_descends (prefixWord ++ tailWord_3696548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3696571 : List Nat := [1, 1, 1, 1, 1, 2, 2, 3, 1, 3, 7]
def baseStart_3696571 : Nat := 118140960795 + 3696571 * 2 ^ 59
def prefixEnd_3696571 : Nat := 4983230072969 + 3 ^ 40 * 3696571 * 2
def baseEnd_3696571 : Nat := 1898117696471361882662285

theorem tailTrace_3696571 : CollatzResearch.WordTrace tailWord_3696571 prefixEnd_3696571 1898117696471361882662285 := by
  unfold tailWord_3696571
  simp only [CollatzResearch.WordTrace]
  refine ⟨134825020690962065909633567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89883347127308043939755711 134825020690962065909633567)
  ·
    refine ⟨202237531036443098864450351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134825020690962065909633567 202237531036443098864450351)
    ·
      refine ⟨303356296554664648296675527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 202237531036443098864450351 303356296554664648296675527)
      ·
        refine ⟨455034444831996972445013291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 303356296554664648296675527 455034444831996972445013291)
        ·
          refine ⟨682551667247995458667519937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 455034444831996972445013291 682551667247995458667519937)
          ·
            refine ⟨511913750435996594000639953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 682551667247995458667519937 511913750435996594000639953)
            ·
              refine ⟨383935312826997445500479965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 511913750435996594000639953 383935312826997445500479965)
              ·
                refine ⟨143975742310124042062679987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 383935312826997445500479965 143975742310124042062679987)
                ·
                  refine ⟨215963613465186063094019981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 143975742310124042062679987 215963613465186063094019981)
                  ·
                    refine ⟨80986355049444773660257493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 215963613465186063094019981 80986355049444773660257493)
                    ·
                      refine ⟨1898117696471361882662285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 80986355049444773660257493 1898117696471361882662285)
                      ·
                        rfl

theorem cell23_3696571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 3, 1, 3, 7].length) (baseStart_3696571 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3696571 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3696571 prefixEnd_3696571 := by exact prefixLift 3696571
  have htrace : WordTrace (prefixWord ++ tailWord_3696571) baseStart_3696571 baseEnd_3696571 := by
    simpa [prefixWord, tailWord_3696571, baseEnd_3696571] using wordTrace_append hprefix tailTrace_3696571
  have hstable : (prefixWord ++ tailWord_3696571).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3696571).length < 2 ^ (prefixWord ++ tailWord_3696571).sum := by decide
  have hdescent : baseEnd_3696571 < baseStart_3696571 := by decide
  rcases family_descends (prefixWord ++ tailWord_3696571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3696575 : List Nat := [1, 1, 2, 2, 2, 1, 3, 4, 3, 1, 3]
def baseStart_3696575 : Nat := 118140960795 + 3696575 * 2 ^ 59
def prefixEnd_3696575 : Nat := 4983230072969 + 3 ^ 40 * 3696575 * 2
def baseEnd_3696575 : Nat := 1898119750393979867012267

theorem tailTrace_3696575 : CollatzResearch.WordTrace tailWord_3696575 prefixEnd_3696575 1898119750393979867012267 := by
  unfold tailWord_3696575
  simp only [CollatzResearch.WordTrace]
  refine ⟨134825166582947574592779179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89883444388631716395186119 134825166582947574592779179)
  ·
    refine ⟨202237749874421361889168769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134825166582947574592779179 202237749874421361889168769)
    ·
      refine ⟨151678312405816021416876577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 202237749874421361889168769 151678312405816021416876577)
      ·
        refine ⟨113758734304362016062657433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 151678312405816021416876577 113758734304362016062657433)
        ·
          refine ⟨85319050728271512046993075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 113758734304362016062657433 85319050728271512046993075)
          ·
            refine ⟨127978576092407268070489613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85319050728271512046993075 127978576092407268070489613)
            ·
              refine ⟨47991966034652725526433605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 127978576092407268070489613 47991966034652725526433605)
              ·
                refine ⟨8998493631497386036206301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 47991966034652725526433605 8998493631497386036206301)
                ·
                  refine ⟨3374435111811519763577363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8998493631497386036206301 3374435111811519763577363)
                  ·
                    refine ⟨5061652667717279645366045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3374435111811519763577363 5061652667717279645366045)
                    ·
                      refine ⟨1898119750393979867012267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5061652667717279645366045 1898119750393979867012267)
                      ·
                        rfl

theorem cell23_3696575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 3, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 3, 4, 3, 1, 3].length) (baseStart_3696575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3696575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3696575 prefixEnd_3696575 := by exact prefixLift 3696575
  have htrace : WordTrace (prefixWord ++ tailWord_3696575) baseStart_3696575 baseEnd_3696575 := by
    simpa [prefixWord, tailWord_3696575, baseEnd_3696575] using wordTrace_append hprefix tailTrace_3696575
  have hstable : (prefixWord ++ tailWord_3696575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3696575).length < 2 ^ (prefixWord ++ tailWord_3696575).sum := by decide
  have hdescent : baseEnd_3696575 < baseStart_3696575 := by decide
  rcases family_descends (prefixWord ++ tailWord_3696575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3696632 : List Nat := [2, 1, 2, 1, 1, 3, 2, 4, 3, 2, 2]
def baseStart_3696632 : Nat := 118140960795 + 3696632 * 2 ^ 59
def prefixEnd_3696632 : Nat := 4983230072969 + 3 ^ 40 * 3696632 * 2
def baseEnd_3696632 : Nat := 1898149018791286143999505

theorem tailTrace_3696632 : CollatzResearch.WordTrace tailWord_3696632 prefixEnd_3696632 1898149018791286143999505 := by
  unfold tailWord_3696632
  simp only [CollatzResearch.WordTrace]
  refine ⟨67413622771870536663802075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89884830362494048885069433 67413622771870536663802075)
  ·
    refine ⟨101120434157805804995703113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67413622771870536663802075 101120434157805804995703113)
    ·
      refine ⟨75840325618354353746777335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101120434157805804995703113 75840325618354353746777335)
      ·
        refine ⟨113760488427531530620166003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75840325618354353746777335 113760488427531530620166003)
        ·
          refine ⟨170640732641297295930249005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113760488427531530620166003 170640732641297295930249005)
          ·
            refine ⟨63990274740486485973843377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 170640732641297295930249005 63990274740486485973843377)
            ·
              refine ⟨47992706055364864480382533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63990274740486485973843377 47992706055364864480382533)
              ·
                refine ⟨8998632385380912090071725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 47992706055364864480382533 8998632385380912090071725)
                ·
                  refine ⟨3374487144517842033776897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8998632385380912090071725 3374487144517842033776897)
                  ·
                    refine ⟨2530865358388381525332673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3374487144517842033776897 2530865358388381525332673)
                    ·
                      refine ⟨1898149018791286143999505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2530865358388381525332673 1898149018791286143999505)
                      ·
                        rfl

theorem cell23_3696632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 2, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 2, 4, 3, 2, 2].length) (baseStart_3696632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3696632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3696632 prefixEnd_3696632 := by exact prefixLift 3696632
  have htrace : WordTrace (prefixWord ++ tailWord_3696632) baseStart_3696632 baseEnd_3696632 := by
    simpa [prefixWord, tailWord_3696632, baseEnd_3696632] using wordTrace_append hprefix tailTrace_3696632
  have hstable : (prefixWord ++ tailWord_3696632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3696632).length < 2 ^ (prefixWord ++ tailWord_3696632).sum := by decide
  have hdescent : baseEnd_3696632 < baseStart_3696632 := by decide
  rcases family_descends (prefixWord ++ tailWord_3696632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3696645 : List Nat := [1, 3, 1, 1, 2, 5, 1, 2, 1, 2, 4]
def baseStart_3696645 : Nat := 118140960795 + 3696645 * 2 ^ 59
def prefixEnd_3696645 : Nat := 4983230072969 + 3 ^ 40 * 3696645 * 2
def baseEnd_3696645 : Nat := 1898155694039794593136945

theorem tailTrace_3696645 : CollatzResearch.WordTrace tailWord_3696645 prefixEnd_3696645 1898155694039794593136945 := by
  unfold tailWord_3696645
  simp only [CollatzResearch.WordTrace]
  refine ⟨134827719692693976547827389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89885146461795984365218259 134827719692693976547827389)
  ·
    refine ⟨50560394884760241205435271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 134827719692693976547827389 50560394884760241205435271)
    ·
      refine ⟨75840592327140361808152907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50560394884760241205435271 75840592327140361808152907)
      ·
        refine ⟨113760888490710542712229361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75840592327140361808152907 113760888490710542712229361)
        ·
          refine ⟨85320666368032907034172021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 113760888490710542712229361 85320666368032907034172021)
          ·
            refine ⟨7998812472003085034453627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 85320666368032907034172021 7998812472003085034453627)
            ·
              refine ⟨11998218708004627551680441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7998812472003085034453627 11998218708004627551680441)
              ·
                refine ⟨8998664031003470663760331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11998218708004627551680441 8998664031003470663760331)
                ·
                  refine ⟨13497996046505205995640497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8998664031003470663760331 13497996046505205995640497)
                  ·
                    refine ⟨10123497034878904496730373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13497996046505205995640497 10123497034878904496730373)
                    ·
                      refine ⟨1898155694039794593136945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10123497034878904496730373 1898155694039794593136945)
                      ·
                        rfl

theorem cell23_3696645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 5, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 5, 1, 2, 1, 2, 4].length) (baseStart_3696645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3696645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3696645 prefixEnd_3696645 := by exact prefixLift 3696645
  have htrace : WordTrace (prefixWord ++ tailWord_3696645) baseStart_3696645 baseEnd_3696645 := by
    simpa [prefixWord, tailWord_3696645, baseEnd_3696645] using wordTrace_append hprefix tailTrace_3696645
  have hstable : (prefixWord ++ tailWord_3696645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3696645).length < 2 ^ (prefixWord ++ tailWord_3696645).sum := by decide
  have hdescent : baseEnd_3696645 < baseStart_3696645 := by decide
  rcases family_descends (prefixWord ++ tailWord_3696645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3696666 : List Nat := [3, 1, 1, 3, 1, 4, 1, 4, 1, 2, 2]
def baseStart_3696666 : Nat := 118140960795 + 3696666 * 2 ^ 59
def prefixEnd_3696666 : Nat := 4983230072969 + 3 ^ 40 * 3696666 * 2
def baseEnd_3696666 : Nat := 1898166477133539010974349

theorem tailTrace_3696666 : CollatzResearch.WordTrace tailWord_3696666 prefixEnd_3696666 1898166477133539010974349 := by
  unfold tailWord_3696666
  simp only [CollatzResearch.WordTrace]
  refine ⟨33707121406404474283585463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89885657083745264756227901 33707121406404474283585463)
  ·
    refine ⟨50560682109606711425378195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33707121406404474283585463 50560682109606711425378195)
    ·
      refine ⟨75841023164410067138067293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50560682109606711425378195 75841023164410067138067293)
      ·
        refine ⟨28440383686653775176775235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 75841023164410067138067293 28440383686653775176775235)
        ·
          refine ⟨42660575529980662765162853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28440383686653775176775235 42660575529980662765162853)
          ·
            refine ⟨7998857911871374268468035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 42660575529980662765162853 7998857911871374268468035)
            ·
              refine ⟨11998286867807061402702053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7998857911871374268468035 11998286867807061402702053)
              ·
                refine ⟨2249678787713824013006635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11998286867807061402702053 2249678787713824013006635)
                ·
                  refine ⟨3374518181570736019509953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2249678787713824013006635 3374518181570736019509953)
                  ·
                    refine ⟨2530888636178052014632465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3374518181570736019509953 2530888636178052014632465)
                    ·
                      refine ⟨1898166477133539010974349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2530888636178052014632465 1898166477133539010974349)
                      ·
                        rfl

theorem cell23_3696666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 4, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 4, 1, 4, 1, 2, 2].length) (baseStart_3696666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3696666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3696666 prefixEnd_3696666 := by exact prefixLift 3696666
  have htrace : WordTrace (prefixWord ++ tailWord_3696666) baseStart_3696666 baseEnd_3696666 := by
    simpa [prefixWord, tailWord_3696666, baseEnd_3696666] using wordTrace_append hprefix tailTrace_3696666
  have hstable : (prefixWord ++ tailWord_3696666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3696666).length < 2 ^ (prefixWord ++ tailWord_3696666).sum := by decide
  have hdescent : baseEnd_3696666 < baseStart_3696666 := by decide
  rcases family_descends (prefixWord ++ tailWord_3696666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3696679 : List Nat := [1, 1, 7, 1, 2, 1, 2, 1, 1, 2, 4]
def baseStart_3696679 : Nat := 118140960795 + 3696679 * 2 ^ 59
def prefixEnd_3696679 : Nat := 4983230072969 + 3 ^ 40 * 3696679 * 2
def baseEnd_3696679 : Nat := 1898173152382047460111789

theorem tailTrace_3696679 : CollatzResearch.WordTrace tailWord_3696679 prefixEnd_3696679 1898173152382047460111789 := by
  unfold tailWord_3696679
  simp only [CollatzResearch.WordTrace]
  refine ⟨134828959774570800354565091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89885973183047200236376727 134828959774570800354565091)
  ·
    refine ⟨202243439661856200531847637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134828959774570800354565091 202243439661856200531847637)
    ·
      refine ⟨4740080617074754699965179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 202243439661856200531847637 4740080617074754699965179)
      ·
        refine ⟨7110120925612132049947769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4740080617074754699965179 7110120925612132049947769)
        ·
          refine ⟨5332590694209099037460827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7110120925612132049947769 5332590694209099037460827)
          ·
            refine ⟨7998886041313648556191241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5332590694209099037460827 7998886041313648556191241)
            ·
              refine ⟨5999164530985236417143431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7998886041313648556191241 5999164530985236417143431)
              ·
                refine ⟨8998746796477854625715147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5999164530985236417143431 8998746796477854625715147)
                ·
                  refine ⟨13498120194716781938572721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8998746796477854625715147 13498120194716781938572721)
                  ·
                    refine ⟨10123590146037586453929541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13498120194716781938572721 10123590146037586453929541)
                    ·
                      refine ⟨1898173152382047460111789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10123590146037586453929541 1898173152382047460111789)
                      ·
                        rfl

theorem cell23_3696679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 1, 2, 1, 1, 2, 4].length) (baseStart_3696679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3696679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3696679 prefixEnd_3696679 := by exact prefixLift 3696679
  have htrace : WordTrace (prefixWord ++ tailWord_3696679) baseStart_3696679 baseEnd_3696679 := by
    simpa [prefixWord, tailWord_3696679, baseEnd_3696679] using wordTrace_append hprefix tailTrace_3696679
  have hstable : (prefixWord ++ tailWord_3696679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3696679).length < 2 ^ (prefixWord ++ tailWord_3696679).sum := by decide
  have hdescent : baseEnd_3696679 < baseStart_3696679 := by decide
  rcases family_descends (prefixWord ++ tailWord_3696679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3696682 : List Nat := [3, 1, 4, 1, 2, 1, 1, 3, 1, 3, 3]
def baseStart_3696682 : Nat := 118140960795 + 3696682 * 2 ^ 59
def prefixEnd_3696682 : Nat := 4983230072969 + 3 ^ 40 * 3696682 * 2
def baseEnd_3696682 : Nat := 1898174692824010948374275

theorem tailTrace_3696682 : CollatzResearch.WordTrace tailWord_3696682 prefixEnd_3696682 1898174692824010948374275 := by
  unfold tailWord_3696682
  simp only [CollatzResearch.WordTrace]
  refine ⟨33707267298389982966731075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89886046129039954577949533 33707267298389982966731075)
  ·
    refine ⟨50560900947584974450096613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33707267298389982966731075 50560900947584974450096613)
    ·
      refine ⟨9480168927672182709393115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 50560900947584974450096613 9480168927672182709393115)
      ·
        refine ⟨14220253391508274064089673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9480168927672182709393115 14220253391508274064089673)
        ·
          refine ⟨10665190043631205548067255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14220253391508274064089673 10665190043631205548067255)
          ·
            refine ⟨15997785065446808322100883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10665190043631205548067255 15997785065446808322100883)
            ·
              refine ⟨23996677598170212483151325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15997785065446808322100883 23996677598170212483151325)
              ·
                refine ⟨8998754099313829681181747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23996677598170212483151325 8998754099313829681181747)
                ·
                  refine ⟨13498131148970744521772621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8998754099313829681181747 13498131148970744521772621)
                  ·
                    refine ⟨5061799180864029195664733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13498131148970744521772621 5061799180864029195664733)
                    ·
                      refine ⟨1898174692824010948374275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5061799180864029195664733 1898174692824010948374275)
                      ·
                        rfl

theorem cell23_3696682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 1, 3, 1, 3, 3].length) (baseStart_3696682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3696682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3696682 prefixEnd_3696682 := by exact prefixLift 3696682
  have htrace : WordTrace (prefixWord ++ tailWord_3696682) baseStart_3696682 baseEnd_3696682 := by
    simpa [prefixWord, tailWord_3696682, baseEnd_3696682] using wordTrace_append hprefix tailTrace_3696682
  have hstable : (prefixWord ++ tailWord_3696682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3696682).length < 2 ^ (prefixWord ++ tailWord_3696682).sum := by decide
  have hdescent : baseEnd_3696682 < baseStart_3696682 := by decide
  rcases family_descends (prefixWord ++ tailWord_3696682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3696698 : List Nat := [3, 1, 1, 1, 3, 1, 1, 1, 3, 8]
def baseStart_3696698 : Nat := 118140960795 + 3696698 * 2 ^ 59
def prefixEnd_3696698 : Nat := 4983230072969 + 3 ^ 40 * 3696698 * 2
def baseEnd_3696698 : Nat := 632727636171494295258067

theorem tailTrace_3696698 : CollatzResearch.WordTrace tailWord_3696698 prefixEnd_3696698 632727636171494295258067 := by
  unfold tailWord_3696698
  simp only [CollatzResearch.WordTrace]
  refine ⟨33707413190375491649876687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89886435174334644399671165 33707413190375491649876687)
  ·
    refine ⟨50561119785563237474815031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33707413190375491649876687 50561119785563237474815031)
    ·
      refine ⟨75841679678344856212222547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50561119785563237474815031 75841679678344856212222547)
      ·
        refine ⟨113762519517517284318333821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75841679678344856212222547 113762519517517284318333821)
        ·
          refine ⟨42660944819068981619375183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 113762519517517284318333821 42660944819068981619375183)
          ·
            refine ⟨63991417228603472429062775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42660944819068981619375183 63991417228603472429062775)
            ·
              refine ⟨95987125842905208643594163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63991417228603472429062775 95987125842905208643594163)
              ·
                refine ⟨143980688764357812965391245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 95987125842905208643594163 143980688764357812965391245)
                ·
                  refine ⟨53992758286634179862021717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 143980688764357812965391245 53992758286634179862021717)
                  ·
                    refine ⟨632727636171494295258067, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 53992758286634179862021717 632727636171494295258067)
                    ·
                      rfl

theorem cell23_3696698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 1, 3, 8].length) (baseStart_3696698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3696698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3696698 prefixEnd_3696698 := by exact prefixLift 3696698
  have htrace : WordTrace (prefixWord ++ tailWord_3696698) baseStart_3696698 baseEnd_3696698 := by
    simpa [prefixWord, tailWord_3696698, baseEnd_3696698] using wordTrace_append hprefix tailTrace_3696698
  have hstable : (prefixWord ++ tailWord_3696698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3696698).length < 2 ^ (prefixWord ++ tailWord_3696698).sum := by decide
  have hdescent : baseEnd_3696698 < baseStart_3696698 := by decide
  rcases family_descends (prefixWord ++ tailWord_3696698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3696733 : List Nat := [1, 4, 4, 1, 1, 2, 3, 1, 2, 1, 3]
def baseStart_3696733 : Nat := 118140960795 + 3696733 * 2 ^ 59
def prefixEnd_3696733 : Nat := 4983230072969 + 3 ^ 40 * 3696733 * 2
def baseEnd_3696733 : Nat := 1898200880337390248836541

theorem tailTrace_3696733 : CollatzResearch.WordTrace tailWord_3696733 prefixEnd_3696733 1898200880337390248836541 := by
  unfold tailWord_3696733
  simp only [CollatzResearch.WordTrace]
  refine ⟨134830929316375167577030853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89887286210916778384687235 134830929316375167577030853)
  ·
    refine ⟨25280799246820343920693285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 134830929316375167577030853 25280799246820343920693285)
    ·
      refine ⟨4740149858778814485129991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 25280799246820343920693285 4740149858778814485129991)
      ·
        refine ⟨7110224788168221727694987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4740149858778814485129991 7110224788168221727694987)
        ·
          refine ⟨10665337182252332591542481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7110224788168221727694987 10665337182252332591542481)
          ·
            refine ⟨7999002886689249443656861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10665337182252332591542481 7999002886689249443656861)
            ·
              refine ⟨2999626082508468541371323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7999002886689249443656861 2999626082508468541371323)
              ·
                refine ⟨4499439123762702812056985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2999626082508468541371323 4499439123762702812056985)
                ·
                  refine ⟨3374579342822027109042739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4499439123762702812056985 3374579342822027109042739)
                  ·
                    refine ⟨5061869014233040663564109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3374579342822027109042739 5061869014233040663564109)
                    ·
                      refine ⟨1898200880337390248836541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5061869014233040663564109 1898200880337390248836541)
                      ·
                        rfl

theorem cell23_3696733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 2, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 2, 3, 1, 2, 1, 3].length) (baseStart_3696733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3696733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3696733 prefixEnd_3696733 := by exact prefixLift 3696733
  have htrace : WordTrace (prefixWord ++ tailWord_3696733) baseStart_3696733 baseEnd_3696733 := by
    simpa [prefixWord, tailWord_3696733, baseEnd_3696733] using wordTrace_append hprefix tailTrace_3696733
  have hstable : (prefixWord ++ tailWord_3696733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3696733).length < 2 ^ (prefixWord ++ tailWord_3696733).sum := by decide
  have hdescent : baseEnd_3696733 < baseStart_3696733 := by decide
  rcases family_descends (prefixWord ++ tailWord_3696733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3696739 : List Nat := [1, 1, 1, 5, 1, 1, 2, 5, 2, 2, 2]
def baseStart_3696739 : Nat := 118140960795 + 3696739 * 2 ^ 59
def prefixEnd_3696739 : Nat := 4983230072969 + 3 ^ 40 * 3696739 * 2
def baseEnd_3696739 : Nat := 1898203961221317225361513

theorem tailTrace_3696739 : CollatzResearch.WordTrace tailWord_3696739 prefixEnd_3696739 1898203961221317225361513 := by
  unfold tailWord_3696739
  simp only [CollatzResearch.WordTrace]
  refine ⟨134831148154353430601749271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89887432102902287067832847 134831148154353430601749271)
  ·
    refine ⟨202246722231530145902623907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134831148154353430601749271 202246722231530145902623907)
    ·
      refine ⟨303370083347295218853935861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 202246722231530145902623907 303370083347295218853935861)
      ·
        refine ⟨28440945313808926767556487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 303370083347295218853935861 28440945313808926767556487)
        ·
          refine ⟨42661417970713390151334731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28440945313808926767556487 42661417970713390151334731)
          ·
            refine ⟨63992126956070085227002097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42661417970713390151334731 63992126956070085227002097)
            ·
              refine ⟨47994095217052563920251573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63992126956070085227002097 47994095217052563920251573)
              ·
                refine ⟨4499446426598677867523585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 47994095217052563920251573 4499446426598677867523585)
                ·
                  refine ⟨3374584819949008400642689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4499446426598677867523585 3374584819949008400642689)
                  ·
                    refine ⟨2530938614961756300482017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3374584819949008400642689 2530938614961756300482017)
                    ·
                      refine ⟨1898203961221317225361513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2530938614961756300482017 1898203961221317225361513)
                      ·
                        rfl

theorem cell23_3696739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 2, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 2, 5, 2, 2, 2].length) (baseStart_3696739 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3696739 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3696739 prefixEnd_3696739 := by exact prefixLift 3696739
  have htrace : WordTrace (prefixWord ++ tailWord_3696739) baseStart_3696739 baseEnd_3696739 := by
    simpa [prefixWord, tailWord_3696739, baseEnd_3696739] using wordTrace_append hprefix tailTrace_3696739
  have hstable : (prefixWord ++ tailWord_3696739).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3696739).length < 2 ^ (prefixWord ++ tailWord_3696739).sum := by decide
  have hdescent : baseEnd_3696739 < baseStart_3696739 := by decide
  rcases family_descends (prefixWord ++ tailWord_3696739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3696775 : List Nat := [1, 1, 4, 2, 1, 1, 3, 1, 4, 5]
def baseStart_3696775 : Nat := 118140960795 + 3696775 * 2 ^ 59
def prefixEnd_3696775 : Nat := 4983230072969 + 3 ^ 40 * 3696775 * 2
def baseEnd_3696775 : Nat := 632740815508293028170449

theorem tailTrace_3696775 : CollatzResearch.WordTrace tailWord_3696775 prefixEnd_3696775 632740815508293028170449 := by
  unfold tailWord_3696775
  simp only [CollatzResearch.WordTrace]
  refine ⟨134832461182223008750059779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89888307454815339166706519 134832461182223008750059779)
  ·
    refine ⟨202248691773334513125089669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134832461182223008750059779 202248691773334513125089669)
    ·
      refine ⟨37921629707500221210954313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 202248691773334513125089669 37921629707500221210954313)
      ·
        refine ⟨28441222280625165908215735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37921629707500221210954313 28441222280625165908215735)
        ·
          refine ⟨42661833420937748862323603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28441222280625165908215735 42661833420937748862323603)
          ·
            refine ⟨63992750131406623293485405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42661833420937748862323603 63992750131406623293485405)
            ·
              refine ⟨23997281299277483735057027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 63992750131406623293485405 23997281299277483735057027)
              ·
                refine ⟨35995921948916225602585541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23997281299277483735057027 35995921948916225602585541)
                ·
                  refine ⟨6749235365421792300484789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35995921948916225602585541 6749235365421792300484789)
                  ·
                    refine ⟨632740815508293028170449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6749235365421792300484789 632740815508293028170449)
                    ·
                      rfl

theorem cell23_3696775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 3, 1, 4, 5].length) (baseStart_3696775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3696775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3696775 prefixEnd_3696775 := by exact prefixLift 3696775
  have htrace : WordTrace (prefixWord ++ tailWord_3696775) baseStart_3696775 baseEnd_3696775 := by
    simpa [prefixWord, tailWord_3696775, baseEnd_3696775] using wordTrace_append hprefix tailTrace_3696775
  have hstable : (prefixWord ++ tailWord_3696775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3696775).length < 2 ^ (prefixWord ++ tailWord_3696775).sum := by decide
  have hdescent : baseEnd_3696775 < baseStart_3696775 := by decide
  rcases family_descends (prefixWord ++ tailWord_3696775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3696795 : List Nat := [1, 1, 1, 1, 1, 1, 2, 6, 4, 1, 4]
def baseStart_3696795 : Nat := 118140960795 + 3696795 * 2 ^ 59
def prefixEnd_3696795 : Nat := 4983230072969 + 3 ^ 40 * 3696795 * 2
def baseEnd_3696795 : Nat := 1898232716137969006261255

theorem tailTrace_3696795 : CollatzResearch.WordTrace tailWord_3696795 prefixEnd_3696795 1898232716137969006261255 := by
  unfold tailWord_3696795
  simp only [CollatzResearch.WordTrace]
  refine ⟨134833190642150552165787839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89888793761433701443858559 134833190642150552165787839)
  ·
    refine ⟨202249785963225828248681759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134833190642150552165787839 202249785963225828248681759)
    ·
      refine ⟨303374678944838742373022639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 202249785963225828248681759 303374678944838742373022639)
      ·
        refine ⟨455062018417258113559533959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 303374678944838742373022639 455062018417258113559533959)
        ·
          refine ⟨682593027625887170339300939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 455062018417258113559533959 682593027625887170339300939)
          ·
            refine ⟨1023889541438830755508951409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 682593027625887170339300939 1023889541438830755508951409)
            ·
              refine ⟨767917156079123066631713557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1023889541438830755508951409 767917156079123066631713557)
              ·
                refine ⟨35996116691208893748361573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 767917156079123066631713557 35996116691208893748361573)
                ·
                  refine ⟨6749271879601667577817795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35996116691208893748361573 6749271879601667577817795)
                  ·
                    refine ⟨10123907819402501366726693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6749271879601667577817795 10123907819402501366726693)
                    ·
                      refine ⟨1898232716137969006261255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10123907819402501366726693 1898232716137969006261255)
                      ·
                        rfl

theorem cell23_3696795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 6, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 6, 4, 1, 4].length) (baseStart_3696795 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3696795 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3696795 prefixEnd_3696795 := by exact prefixLift 3696795
  have htrace : WordTrace (prefixWord ++ tailWord_3696795) baseStart_3696795 baseEnd_3696795 := by
    simpa [prefixWord, tailWord_3696795, baseEnd_3696795] using wordTrace_append hprefix tailTrace_3696795
  have hstable : (prefixWord ++ tailWord_3696795).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3696795).length < 2 ^ (prefixWord ++ tailWord_3696795).sum := by decide
  have hdescent : baseEnd_3696795 < baseStart_3696795 := by decide
  rcases family_descends (prefixWord ++ tailWord_3696795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3696825 : List Nat := [1, 2, 1, 4, 1, 2, 2, 1, 2, 1, 6]
def baseStart_3696825 : Nat := 118140960795 + 3696825 * 2 ^ 59
def prefixEnd_3696825 : Nat := 4983230072969 + 3 ^ 40 * 3696825 * 2
def baseEnd_3696825 : Nat := 1898248120557603888886117

theorem tailTrace_3696825 : CollatzResearch.WordTrace tailWord_3696825 prefixEnd_3696825 1898248120557603888886117 := by
  unfold tailWord_3696825
  simp only [CollatzResearch.WordTrace]
  refine ⟨134834284832041867289379929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89889523221361244859586619 134834284832041867289379929)
  ·
    refine ⟨101125713624031400467034947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134834284832041867289379929 101125713624031400467034947)
    ·
      refine ⟨151688570436047100700552421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101125713624031400467034947 151688570436047100700552421)
      ·
        refine ⟨28441606956758831381353579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 151688570436047100700552421 28441606956758831381353579)
        ·
          refine ⟨42662410435138247072030369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28441606956758831381353579 42662410435138247072030369)
          ·
            refine ⟨31996807826353685304022777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42662410435138247072030369 31996807826353685304022777)
            ·
              refine ⟨23997605869765263978017083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31996807826353685304022777 23997605869765263978017083)
              ·
                refine ⟨35996408804647895967025625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23997605869765263978017083 35996408804647895967025625)
                ·
                  refine ⟨26997306603485921975269219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35996408804647895967025625 26997306603485921975269219)
                  ·
                    refine ⟨40495959905228882962903829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26997306603485921975269219 40495959905228882962903829)
                    ·
                      refine ⟨1898248120557603888886117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 40495959905228882962903829 1898248120557603888886117)
                      ·
                        rfl

theorem cell23_3696825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 2, 1, 2, 1, 6].length) (baseStart_3696825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3696825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3696825 prefixEnd_3696825 := by exact prefixLift 3696825
  have htrace : WordTrace (prefixWord ++ tailWord_3696825) baseStart_3696825 baseEnd_3696825 := by
    simpa [prefixWord, tailWord_3696825, baseEnd_3696825] using wordTrace_append hprefix tailTrace_3696825
  have hstable : (prefixWord ++ tailWord_3696825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3696825).length < 2 ^ (prefixWord ++ tailWord_3696825).sum := by decide
  have hdescent : baseEnd_3696825 < baseStart_3696825 := by decide
  rcases family_descends (prefixWord ++ tailWord_3696825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3696896 : List Nat := [2, 1, 1, 2, 1, 1, 6, 4, 1, 1, 3]
def baseStart_3696896 : Nat := 118140960795 + 3696896 * 2 ^ 59
def prefixEnd_3696896 : Nat := 4983230072969 + 3 ^ 40 * 3696896 * 2
def baseEnd_3696896 : Nat := 1898284577684073111098291

theorem tailTrace_3696896 : CollatzResearch.WordTrace tailWord_3696896 prefixEnd_3696896 1898284577684073111098291 := by
  unfold tailWord_3696896
  simp only [CollatzResearch.WordTrace]
  refine ⟨67418437207392323207607271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89891249609856430943476361 67418437207392323207607271)
  ·
    refine ⟨101127655811088484811410907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67418437207392323207607271 101127655811088484811410907)
    ·
      refine ⟨151691483716632727217116361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101127655811088484811410907 151691483716632727217116361)
      ·
        refine ⟨113768612787474545412837271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 151691483716632727217116361 113768612787474545412837271)
        ·
          refine ⟨170652919181211818119255907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113768612787474545412837271 170652919181211818119255907)
          ·
            refine ⟨255979378771817727178883861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 170652919181211818119255907 255979378771817727178883861)
            ·
              refine ⟨11999033379928955961510181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 255979378771817727178883861 11999033379928955961510181)
              ·
                refine ⟨2249818758736679242783159, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11999033379928955961510181 2249818758736679242783159)
                ·
                  refine ⟨3374728138105018864174739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2249818758736679242783159 3374728138105018864174739)
                  ·
                    refine ⟨5062092207157528296262109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3374728138105018864174739 5062092207157528296262109)
                    ·
                      refine ⟨1898284577684073111098291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5062092207157528296262109 1898284577684073111098291)
                      ·
                        rfl

theorem cell23_3696896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 6, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 6, 4, 1, 1, 3].length) (baseStart_3696896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3696896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3696896 prefixEnd_3696896 := by exact prefixLift 3696896
  have htrace : WordTrace (prefixWord ++ tailWord_3696896) baseStart_3696896 baseEnd_3696896 := by
    simpa [prefixWord, tailWord_3696896, baseEnd_3696896] using wordTrace_append hprefix tailTrace_3696896
  have hstable : (prefixWord ++ tailWord_3696896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3696896).length < 2 ^ (prefixWord ++ tailWord_3696896).sum := by decide
  have hdescent : baseEnd_3696896 < baseStart_3696896 := by decide
  rcases family_descends (prefixWord ++ tailWord_3696896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3696919 : List Nat := [1, 1, 3, 4, 1, 2, 1, 4, 1, 1, 4]
def baseStart_3696919 : Nat := 118140960795 + 3696919 * 2 ^ 59
def prefixEnd_3696919 : Nat := 4983230072969 + 3 ^ 40 * 3696919 * 2
def baseEnd_3696919 : Nat := 1898296387739126521110685

theorem tailTrace_3696919 : CollatzResearch.WordTrace tailWord_3696919 prefixEnd_3696919 1898296387739126521110685 := by
  unfold tailWord_3696919
  simp only [CollatzResearch.WordTrace]
  refine ⟨134837713293701321343301811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89891808862467547562201207 134837713293701321343301811)
  ·
    refine ⟨202256569940551982014952717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134837713293701321343301811 202256569940551982014952717)
    ·
      refine ⟨75846213727706993255607269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 202256569940551982014952717 75846213727706993255607269)
      ·
        refine ⟨14221165073945061235426363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 75846213727706993255607269 14221165073945061235426363)
        ·
          refine ⟨21331747610917591853139545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14221165073945061235426363 21331747610917591853139545)
          ·
            refine ⟨15998810708188193889854659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21331747610917591853139545 15998810708188193889854659)
            ·
              refine ⟨23998216062282290834781989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15998810708188193889854659 23998216062282290834781989)
              ·
                refine ⟨4499665511677929531521623, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23998216062282290834781989 4499665511677929531521623)
                ·
                  refine ⟨6749498267516894297282435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4499665511677929531521623 6749498267516894297282435)
                  ·
                    refine ⟨10124247401275341445923653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6749498267516894297282435 10124247401275341445923653)
                    ·
                      refine ⟨1898296387739126521110685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10124247401275341445923653 1898296387739126521110685)
                      ·
                        rfl

theorem cell23_3696919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 1, 4, 1, 1, 4].length) (baseStart_3696919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3696919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3696919 prefixEnd_3696919 := by exact prefixLift 3696919
  have htrace : WordTrace (prefixWord ++ tailWord_3696919) baseStart_3696919 baseEnd_3696919 := by
    simpa [prefixWord, tailWord_3696919, baseEnd_3696919] using wordTrace_append hprefix tailTrace_3696919
  have hstable : (prefixWord ++ tailWord_3696919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3696919).length < 2 ^ (prefixWord ++ tailWord_3696919).sum := by decide
  have hdescent : baseEnd_3696919 < baseStart_3696919 := by decide
  rcases family_descends (prefixWord ++ tailWord_3696919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3696930 : List Nat := [3, 3, 1, 1, 3, 3, 1, 3, 1, 1, 3]
def baseStart_3696930 : Nat := 118140960795 + 3696930 * 2 ^ 59
def prefixEnd_3696930 : Nat := 4983230072969 + 3 ^ 40 * 3696930 * 2
def baseEnd_3696930 : Nat := 1898302036026325978073135

theorem tailTrace_3696930 : CollatzResearch.WordTrace tailWord_3696930 prefixEnd_3696930 1898302036026325978073135 := by
  unfold tailWord_3696930
  simp only [CollatzResearch.WordTrace]
  refine ⟨33709528624165367555488061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89892076331107646814634829 33709528624165367555488061)
  ·
    refine ⟨12641073234062012833308023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33709528624165367555488061 12641073234062012833308023)
    ·
      refine ⟨18961609851093019249962035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12641073234062012833308023 18961609851093019249962035)
      ·
        refine ⟨28442414776639528874943053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18961609851093019249962035 28442414776639528874943053)
        ·
          refine ⟨10665905541239823328103645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28442414776639528874943053 10665905541239823328103645)
          ·
            refine ⟨3999714577964933748038867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10665905541239823328103645 3999714577964933748038867)
            ·
              refine ⟨5999571866947400622058301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3999714577964933748038867 5999571866947400622058301)
              ·
                refine ⟨2249839450105275233271863, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5999571866947400622058301 2249839450105275233271863)
                ·
                  refine ⟨3374759175157912849907795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2249839450105275233271863 3374759175157912849907795)
                  ·
                    refine ⟨5062138762736869274861693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3374759175157912849907795 5062138762736869274861693)
                    ·
                      refine ⟨1898302036026325978073135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5062138762736869274861693 1898302036026325978073135)
                      ·
                        rfl

theorem cell23_3696930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 3, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 3, 1, 3, 1, 1, 3].length) (baseStart_3696930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3696930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3696930 prefixEnd_3696930 := by exact prefixLift 3696930
  have htrace : WordTrace (prefixWord ++ tailWord_3696930) baseStart_3696930 baseEnd_3696930 := by
    simpa [prefixWord, tailWord_3696930, baseEnd_3696930] using wordTrace_append hprefix tailTrace_3696930
  have hstable : (prefixWord ++ tailWord_3696930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3696930).length < 2 ^ (prefixWord ++ tailWord_3696930).sum := by decide
  have hdescent : baseEnd_3696930 < baseStart_3696930 := by decide
  rcases family_descends (prefixWord ++ tailWord_3696930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3696953 : List Nat := [1, 2, 1, 6, 1, 1, 3, 1, 3, 2, 2]
def baseStart_3696953 : Nat := 118140960795 + 3696953 * 2 ^ 59
def prefixEnd_3696953 : Nat := 4983230072969 + 3 ^ 40 * 3696953 * 2
def baseEnd_3696953 : Nat := 1898313846081379388085529

theorem tailTrace_3696953 : CollatzResearch.WordTrace tailWord_3696953 prefixEnd_3696953 1898313846081379388085529 := by
  unfold tailWord_3696953
  simp only [CollatzResearch.WordTrace]
  refine ⟨134838953375578145150039513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89892635583718763433359675 134838953375578145150039513)
  ·
    refine ⟨101129215031683608862529635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134838953375578145150039513 101129215031683608862529635)
    ·
      refine ⟨151693822547525413293794453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101129215031683608862529635 151693822547525413293794453)
      ·
        refine ⟨7110647931915253748146615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 151693822547525413293794453 7110647931915253748146615)
        ·
          refine ⟨10665971897872880622219923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7110647931915253748146615 10665971897872880622219923)
          ·
            refine ⟨15998957846809320933329885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10665971897872880622219923 15998957846809320933329885)
            ·
              refine ⟨5999609192553495349998707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15998957846809320933329885 5999609192553495349998707)
              ·
                refine ⟨8999413788830243024998061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5999609192553495349998707 8999413788830243024998061)
                ·
                  refine ⟨3374780170811341134374273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8999413788830243024998061 3374780170811341134374273)
                  ·
                    refine ⟨2531085128108505850780705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3374780170811341134374273 2531085128108505850780705)
                    ·
                      refine ⟨1898313846081379388085529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2531085128108505850780705 1898313846081379388085529)
                      ·
                        rfl

theorem cell23_3696953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 3, 1, 3, 2, 2].length) (baseStart_3696953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3696953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3696953 prefixEnd_3696953 := by exact prefixLift 3696953
  have htrace : WordTrace (prefixWord ++ tailWord_3696953) baseStart_3696953 baseEnd_3696953 := by
    simpa [prefixWord, tailWord_3696953, baseEnd_3696953] using wordTrace_append hprefix tailTrace_3696953
  have hstable : (prefixWord ++ tailWord_3696953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3696953).length < 2 ^ (prefixWord ++ tailWord_3696953).sum := by decide
  have hdescent : baseEnd_3696953 < baseStart_3696953 := by decide
  rcases family_descends (prefixWord ++ tailWord_3696953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3697004 : List Nat := [2, 2, 1, 1, 7, 1, 2, 2, 1, 2, 2]
def baseStart_3697004 : Nat := 118140960795 + 3697004 * 2 ^ 59
def prefixEnd_3697004 : Nat := 4983230072969 + 3 ^ 40 * 3697004 * 2
def baseEnd_3697004 : Nat := 1898340033594758688547795

theorem tailTrace_3697004 : CollatzResearch.WordTrace tailWord_3697004 prefixEnd_3697004 1898340033594758688547795 := by
  unfold tailWord_3697004
  simp only [CollatzResearch.WordTrace]
  refine ⟨67420406749196690430073033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89893875665595587240097377 67420406749196690430073033)
  ·
    refine ⟨50565305061897517822554775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67420406749196690430073033 50565305061897517822554775)
    ·
      refine ⟨75847957592846276733832163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50565305061897517822554775 75847957592846276733832163)
      ·
        refine ⟨113771936389269415100748245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75847957592846276733832163 113771936389269415100748245)
        ·
          refine ⟨2666529759123501916423787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 113771936389269415100748245 2666529759123501916423787)
          ·
            refine ⟨3999794638685252874635681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2666529759123501916423787 3999794638685252874635681)
            ·
              refine ⟨2999845979013939655976761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3999794638685252874635681 2999845979013939655976761)
              ·
                refine ⟨2249884484260454741982571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2999845979013939655976761 2249884484260454741982571)
                ·
                  refine ⟨3374826726390682112973857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2249884484260454741982571 3374826726390682112973857)
                  ·
                    refine ⟨2531120044793011584730393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3374826726390682112973857 2531120044793011584730393)
                    ·
                      refine ⟨1898340033594758688547795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2531120044793011584730393 1898340033594758688547795)
                      ·
                        rfl

theorem cell23_3697004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 7, 1, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 7, 1, 2, 2, 1, 2, 2].length) (baseStart_3697004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3697004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3697004 prefixEnd_3697004 := by exact prefixLift 3697004
  have htrace : WordTrace (prefixWord ++ tailWord_3697004) baseStart_3697004 baseEnd_3697004 := by
    simpa [prefixWord, tailWord_3697004, baseEnd_3697004] using wordTrace_append hprefix tailTrace_3697004
  have hstable : (prefixWord ++ tailWord_3697004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3697004).length < 2 ^ (prefixWord ++ tailWord_3697004).sum := by decide
  have hdescent : baseEnd_3697004 < baseStart_3697004 := by decide
  rcases family_descends (prefixWord ++ tailWord_3697004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3697009 : List Nat := [1, 2, 2, 2, 1, 2, 1, 1, 5, 4, 2]
def baseStart_3697009 : Nat := 118140960795 + 3697009 * 2 ^ 59
def prefixEnd_3697009 : Nat := 4983230072969 + 3 ^ 40 * 3697009 * 2
def baseEnd_3697009 : Nat := 1898342600998031168985271

theorem tailTrace_3697009 : CollatzResearch.WordTrace tailWord_3697009 prefixEnd_3697009 1898342600998031168985271 := by
  unfold tailWord_3697009
  simp only [CollatzResearch.WordTrace]
  refine ⟨134840995863375266714078081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89893997242250177809385387 134840995863375266714078081)
  ·
    refine ⟨101130746897531450035558561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134840995863375266714078081 101130746897531450035558561)
    ·
      refine ⟨75848060173148587526668921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101130746897531450035558561 75848060173148587526668921)
      ·
        refine ⟨56886045129861440645001691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75848060173148587526668921 56886045129861440645001691)
        ·
          refine ⟨85329067694792160967502537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56886045129861440645001691 85329067694792160967502537)
          ·
            refine ⟨63996800771094120725626903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85329067694792160967502537 63996800771094120725626903)
            ·
              refine ⟨95995201156641181088440355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63996800771094120725626903 95995201156641181088440355)
              ·
                refine ⟨143992801734961771632660533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 95995201156641181088440355 143992801734961771632660533)
                ·
                  refine ⟨13499325162652666090561925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 143992801734961771632660533 13499325162652666090561925)
                  ·
                    refine ⟨2531123467997374891980361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13499325162652666090561925 2531123467997374891980361)
                    ·
                      refine ⟨1898342600998031168985271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2531123467997374891980361 1898342600998031168985271)
                      ·
                        rfl

theorem cell23_3697009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 1, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 1, 5, 4, 2].length) (baseStart_3697009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3697009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3697009 prefixEnd_3697009 := by exact prefixLift 3697009
  have htrace : WordTrace (prefixWord ++ tailWord_3697009) baseStart_3697009 baseEnd_3697009 := by
    simpa [prefixWord, tailWord_3697009, baseEnd_3697009] using wordTrace_append hprefix tailTrace_3697009
  have hstable : (prefixWord ++ tailWord_3697009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3697009).length < 2 ^ (prefixWord ++ tailWord_3697009).sum := by decide
  have hdescent : baseEnd_3697009 < baseStart_3697009 := by decide
  rcases family_descends (prefixWord ++ tailWord_3697009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3697059 : List Nat := [1, 1, 1, 4, 1, 4, 1, 2, 2, 3, 3]
def baseStart_3697059 : Nat := 118140960795 + 3697059 * 2 ^ 59
def prefixEnd_3697059 : Nat := 4983230072969 + 3 ^ 40 * 3697059 * 2
def baseEnd_3697059 : Nat := 1898368275030755973360041

theorem tailTrace_3697059 : CollatzResearch.WordTrace tailWord_3697059 prefixEnd_3697059 1898368275030755973360041 := by
  unfold tailWord_3697059
  simp only [CollatzResearch.WordTrace]
  refine ⟨134842819513194125253398231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89895213008796083502265487 134842819513194125253398231)
  ·
    refine ⟨202264229269791187880097347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134842819513194125253398231 202264229269791187880097347)
    ·
      refine ⟨303396343904686781820146021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 202264229269791187880097347 303396343904686781820146021)
      ·
        refine ⟨56886814482128771591277379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 303396343904686781820146021 56886814482128771591277379)
        ·
          refine ⟨85330221723193157386916069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56886814482128771591277379 85330221723193157386916069)
          ·
            refine ⟨15999416573098717010046763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 85330221723193157386916069 15999416573098717010046763)
            ·
              refine ⟨23999124859648075515070145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15999416573098717010046763 23999124859648075515070145)
              ·
                refine ⟨17999343644736056636302609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23999124859648075515070145 17999343644736056636302609)
                ·
                  refine ⟨13499507733552042477226957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17999343644736056636302609 13499507733552042477226957)
                  ·
                    refine ⟨5062315400082015928960109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13499507733552042477226957 5062315400082015928960109)
                    ·
                      refine ⟨1898368275030755973360041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5062315400082015928960109 1898368275030755973360041)
                      ·
                        rfl

theorem cell23_3697059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 1, 2, 2, 3, 3].length) (baseStart_3697059 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3697059 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3697059 prefixEnd_3697059 := by exact prefixLift 3697059
  have htrace : WordTrace (prefixWord ++ tailWord_3697059) baseStart_3697059 baseEnd_3697059 := by
    simpa [prefixWord, tailWord_3697059, baseEnd_3697059] using wordTrace_append hprefix tailTrace_3697059
  have hstable : (prefixWord ++ tailWord_3697059).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3697059).length < 2 ^ (prefixWord ++ tailWord_3697059).sum := by decide
  have hdescent : baseEnd_3697059 < baseStart_3697059 := by decide
  rcases family_descends (prefixWord ++ tailWord_3697059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3697072 : List Nat := [2, 1, 1, 1, 2, 1, 1, 2, 5, 2, 5]
def baseStart_3697072 : Nat := 118140960795 + 3697072 * 2 ^ 59
def prefixEnd_3697072 : Nat := 4983230072969 + 3 ^ 40 * 3697072 * 2
def baseEnd_3697072 : Nat := 1898374950279264422497481

theorem tailTrace_3697072 : CollatzResearch.WordTrace tailWord_3697072 prefixEnd_3697072 1898374950279264422497481 := by
  unfold tailWord_3697072
  simp only [CollatzResearch.WordTrace]
  refine ⟨67421646831073514236810735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89895529108098018982414313 67421646831073514236810735)
  ·
    refine ⟨101132470246610271355216103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67421646831073514236810735 101132470246610271355216103)
    ·
      refine ⟨151698705369915407032824155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101132470246610271355216103 151698705369915407032824155)
      ·
        refine ⟨227548058054873110549236233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151698705369915407032824155 227548058054873110549236233)
        ·
          refine ⟨170661043541154832911927175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 227548058054873110549236233 170661043541154832911927175)
          ·
            refine ⟨255991565311732249367890763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 170661043541154832911927175 255991565311732249367890763)
            ·
              refine ⟨383987347967598374051836145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 255991565311732249367890763 383987347967598374051836145)
              ·
                refine ⟨287990510975698780538877109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 383987347967598374051836145 287990510975698780538877109)
                ·
                  refine ⟨26999110403971760675519729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 287990510975698780538877109 26999110403971760675519729)
                  ·
                    refine ⟨20249332802978820506639797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26999110403971760675519729 20249332802978820506639797)
                    ·
                      refine ⟨1898374950279264422497481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20249332802978820506639797 1898374950279264422497481)
                      ·
                        rfl

theorem cell23_3697072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 2, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 2, 5, 2, 5].length) (baseStart_3697072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3697072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3697072 prefixEnd_3697072 := by exact prefixLift 3697072
  have htrace : WordTrace (prefixWord ++ tailWord_3697072) baseStart_3697072 baseEnd_3697072 := by
    simpa [prefixWord, tailWord_3697072, baseEnd_3697072] using wordTrace_append hprefix tailTrace_3697072
  have hstable : (prefixWord ++ tailWord_3697072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3697072).length < 2 ^ (prefixWord ++ tailWord_3697072).sum := by decide
  have hdescent : baseEnd_3697072 < baseStart_3697072 := by decide
  rcases family_descends (prefixWord ++ tailWord_3697072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3697077 : List Nat := [1, 3, 3, 2, 3, 1, 3, 1, 2, 2, 2]
def baseStart_3697077 : Nat := 118140960795 + 3697077 * 2 ^ 59
def prefixEnd_3697077 : Nat := 4983230072969 + 3 ^ 40 * 3697077 * 2
def baseEnd_3697077 : Nat := 1898377517682536902934959

theorem tailTrace_3697077 : CollatzResearch.WordTrace tailWord_3697077 prefixEnd_3697077 1898377517682536902934959 := by
  unfold tailWord_3697077
  simp only [CollatzResearch.WordTrace]
  refine ⟨134843476027128914327553485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89895650684752609551702323 134843476027128914327553485)
  ·
    refine ⟨50566303510173342872832557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 134843476027128914327553485 50566303510173342872832557)
    ·
      refine ⟨18962363816315003577312209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50566303510173342872832557 18962363816315003577312209)
      ·
        refine ⟨14221772862236252682984157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18962363816315003577312209 14221772862236252682984157)
        ·
          refine ⟨5333164823338594756119059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14221772862236252682984157 5333164823338594756119059)
          ·
            refine ⟨7999747235007892134178589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5333164823338594756119059 7999747235007892134178589)
            ·
              refine ⟨2999905213127959550316971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7999747235007892134178589 2999905213127959550316971)
              ·
                refine ⟨4499857819691939325475457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2999905213127959550316971 4499857819691939325475457)
                ·
                  refine ⟨3374893364768954494106593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4499857819691939325475457 3374893364768954494106593)
                  ·
                    refine ⟨2531170023576715870579945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3374893364768954494106593 2531170023576715870579945)
                    ·
                      refine ⟨1898377517682536902934959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2531170023576715870579945 1898377517682536902934959)
                      ·
                        rfl

theorem cell23_3697077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 1, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 1, 3, 1, 2, 2, 2].length) (baseStart_3697077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3697077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3697077 prefixEnd_3697077 := by exact prefixLift 3697077
  have htrace : WordTrace (prefixWord ++ tailWord_3697077) baseStart_3697077 baseEnd_3697077 := by
    simpa [prefixWord, tailWord_3697077, baseEnd_3697077] using wordTrace_append hprefix tailTrace_3697077
  have hstable : (prefixWord ++ tailWord_3697077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3697077).length < 2 ^ (prefixWord ++ tailWord_3697077).sum := by decide
  have hdescent : baseEnd_3697077 < baseStart_3697077 := by decide
  rcases family_descends (prefixWord ++ tailWord_3697077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3697086 : List Nat := [4, 2, 1, 1, 1, 1, 2, 2, 2, 5, 2]
def baseStart_3697086 : Nat := 118140960795 + 3697086 * 2 ^ 59
def prefixEnd_3697086 : Nat := 4983230072969 + 3 ^ 40 * 3697086 * 2
def baseEnd_3697086 : Nat := 1898382139008427367722417

theorem tailTrace_3697086 : CollatzResearch.WordTrace tailWord_3697086 prefixEnd_3697086 1898382139008427367722417 := by
  unfold tailWord_3697086
  simp only [CollatzResearch.WordTrace]
  refine ⟨16855475535512038608078889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 89895869522730872576420741 16855475535512038608078889)
  ·
    refine ⟨12641606651634028956059167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16855475535512038608078889 12641606651634028956059167)
    ·
      refine ⟨18962409977451043434088751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12641606651634028956059167 18962409977451043434088751)
      ·
        refine ⟨28443614966176565151133127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18962409977451043434088751 28443614966176565151133127)
        ·
          refine ⟨42665422449264847726699691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28443614966176565151133127 42665422449264847726699691)
          ·
            refine ⟨63998133673897271590049537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42665422449264847726699691 63998133673897271590049537)
            ·
              refine ⟨47998600255422953692537153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63998133673897271590049537 47998600255422953692537153)
              ·
                refine ⟨35998950191567215269402865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47998600255422953692537153 35998950191567215269402865)
                ·
                  refine ⟨26999212643675411452052149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35998950191567215269402865 26999212643675411452052149)
                  ·
                    refine ⟨2531176185344569823629889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 26999212643675411452052149 2531176185344569823629889)
                    ·
                      refine ⟨1898382139008427367722417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2531176185344569823629889 1898382139008427367722417)
                      ·
                        rfl

theorem cell23_3697086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 2, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 2, 2, 2, 5, 2].length) (baseStart_3697086 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3697086 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3697086 prefixEnd_3697086 := by exact prefixLift 3697086
  have htrace : WordTrace (prefixWord ++ tailWord_3697086) baseStart_3697086 baseEnd_3697086 := by
    simpa [prefixWord, tailWord_3697086, baseEnd_3697086] using wordTrace_append hprefix tailTrace_3697086
  have hstable : (prefixWord ++ tailWord_3697086).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3697086).length < 2 ^ (prefixWord ++ tailWord_3697086).sum := by decide
  have hdescent : baseEnd_3697086 < baseStart_3697086 := by decide
  rcases family_descends (prefixWord ++ tailWord_3697086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3697099 : List Nat := [1, 1, 1, 1, 3, 3, 1, 5, 2, 1, 4]
def baseStart_3697099 : Nat := 118140960795 + 3697099 * 2 ^ 59
def prefixEnd_3697099 : Nat := 4983230072969 + 3 ^ 40 * 3697099 * 2
def baseEnd_3697099 : Nat := 1898388814256935816859857

theorem tailTrace_3697099 : CollatzResearch.WordTrace tailWord_3697099 prefixEnd_3697099 1898388814256935816859857 := by
  unfold tailWord_3697099
  simp only [CollatzResearch.WordTrace]
  refine ⟨134844278433049212084854351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89896185622032808056569567 134844278433049212084854351)
  ·
    refine ⟨202266417649573818127281527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134844278433049212084854351 202266417649573818127281527)
    ·
      refine ⟨303399626474360727190922291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 202266417649573818127281527 303399626474360727190922291)
      ·
        refine ⟨455099439711541090786383437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 303399626474360727190922291 455099439711541090786383437)
        ·
          refine ⟨170662289891827909044893789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 455099439711541090786383437 170662289891827909044893789)
          ·
            refine ⟨63998358709435465891835171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 170662289891827909044893789 63998358709435465891835171)
            ·
              refine ⟨95997538064153198837752757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63998358709435465891835171 95997538064153198837752757)
              ·
                refine ⟨8999769193514362391039321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 95997538064153198837752757 8999769193514362391039321)
                ·
                  refine ⟨6749826895135771793279491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8999769193514362391039321 6749826895135771793279491)
                  ·
                    refine ⟨10124740342703657689919237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6749826895135771793279491 10124740342703657689919237)
                    ·
                      refine ⟨1898388814256935816859857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10124740342703657689919237 1898388814256935816859857)
                      ·
                        rfl

theorem cell23_3697099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 5, 2, 1, 4].length) (baseStart_3697099 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3697099 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3697099 prefixEnd_3697099 := by exact prefixLift 3697099
  have htrace : WordTrace (prefixWord ++ tailWord_3697099) baseStart_3697099 baseEnd_3697099 := by
    simpa [prefixWord, tailWord_3697099, baseEnd_3697099] using wordTrace_append hprefix tailTrace_3697099
  have hstable : (prefixWord ++ tailWord_3697099).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3697099).length < 2 ^ (prefixWord ++ tailWord_3697099).sum := by decide
  have hdescent : baseEnd_3697099 < baseStart_3697099 := by decide
  rcases family_descends (prefixWord ++ tailWord_3697099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3697100 : List Nat := [2, 2, 1, 4, 4, 1, 1, 3, 5]
def baseStart_3697100 : Nat := 118140960795 + 3697100 * 2 ^ 59
def prefixEnd_3697100 : Nat := 4983230072969 + 3 ^ 40 * 3697100 * 2
def baseEnd_3697100 : Nat := 210932147526398923660817

theorem tailTrace_3697100 : CollatzResearch.WordTrace tailWord_3697100 prefixEnd_3697100 210932147526398923660817 := by
  unfold tailWord_3697100
  simp only [CollatzResearch.WordTrace]
  refine ⟨67422157453022794627820377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89896209937363726170427169 67422157453022794627820377)
  ·
    refine ⟨50566618089767095970865283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67422157453022794627820377 50566618089767095970865283)
    ·
      refine ⟨75849927134650643956297925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50566618089767095970865283 75849927134650643956297925)
      ·
        refine ⟨14221861337746995741805861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 75849927134650643956297925 14221861337746995741805861)
        ·
          refine ⟨2666599000827561701588599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14221861337746995741805861 2666599000827561701588599)
          ·
            refine ⟨3999898501241342552382899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2666599000827561701588599 3999898501241342552382899)
            ·
              refine ⟨5999847751862013828574349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3999898501241342552382899 5999847751862013828574349)
              ·
                refine ⟨2249942906948255185715381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5999847751862013828574349 2249942906948255185715381)
                ·
                  refine ⟨210932147526398923660817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2249942906948255185715381 210932147526398923660817)
                  ·
                    rfl

theorem cell23_3697100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 4, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 4, 1, 1, 3, 5].length) (baseStart_3697100 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3697100 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3697100 prefixEnd_3697100 := by exact prefixLift 3697100
  have htrace : WordTrace (prefixWord ++ tailWord_3697100) baseStart_3697100 baseEnd_3697100 := by
    simpa [prefixWord, tailWord_3697100, baseEnd_3697100] using wordTrace_append hprefix tailTrace_3697100
  have hstable : (prefixWord ++ tailWord_3697100).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3697100).length < 2 ^ (prefixWord ++ tailWord_3697100).sum := by decide
  have hdescent : baseEnd_3697100 < baseStart_3697100 := by decide
  rcases family_descends (prefixWord ++ tailWord_3697100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3697139 : List Nat := [1, 1, 1, 2, 2, 2, 5, 3, 6]
def baseStart_3697139 : Nat := 118140960795 + 3697139 * 2 ^ 59
def prefixEnd_3697139 : Nat := 4983230072969 + 3 ^ 40 * 3697139 * 2
def baseEnd_3697139 : Nat := 210934372609235073373297

theorem tailTrace_3697139 : CollatzResearch.WordTrace tailWord_3697139 prefixEnd_3697139 210934372609235073373297 := by
  unfold tailWord_3697139
  simp only [CollatzResearch.WordTrace]
  refine ⟨134845737352904298916310471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89897158235269532610873647 134845737352904298916310471)
  ·
    refine ⟨202268606029356448374465707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134845737352904298916310471 202268606029356448374465707)
    ·
      refine ⟨303402909044034672561698561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 202268606029356448374465707 303402909044034672561698561)
      ·
        refine ⟨227552181783026004421273921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 303402909044034672561698561 227552181783026004421273921)
        ·
          refine ⟨170664136337269503315955441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 227552181783026004421273921 170664136337269503315955441)
          ·
            refine ⟨127998102252952127486966581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 170664136337269503315955441 127998102252952127486966581)
            ·
              refine ⟨11999822086214261951903117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 127998102252952127486966581 11999822086214261951903117)
              ·
                refine ⟨4499933282330348231963669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11999822086214261951903117 4499933282330348231963669)
                ·
                  refine ⟨210934372609235073373297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4499933282330348231963669 210934372609235073373297)
                  ·
                    rfl

theorem cell23_3697139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 5, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 5, 3, 6].length) (baseStart_3697139 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3697139 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3697139 prefixEnd_3697139 := by exact prefixLift 3697139
  have htrace : WordTrace (prefixWord ++ tailWord_3697139) baseStart_3697139 baseEnd_3697139 := by
    simpa [prefixWord, tailWord_3697139, baseEnd_3697139] using wordTrace_append hprefix tailTrace_3697139
  have hstable : (prefixWord ++ tailWord_3697139).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3697139).length < 2 ^ (prefixWord ++ tailWord_3697139).sum := by decide
  have hdescent : baseEnd_3697139 < baseStart_3697139 := by decide
  rcases family_descends (prefixWord ++ tailWord_3697139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3697153 : List Nat := [1, 2, 4, 1, 3, 2, 2, 1, 2, 2, 3]
def baseStart_3697153 : Nat := 118140960795 + 3697153 * 2 ^ 59
def prefixEnd_3697153 : Nat := 4983230072969 + 3 ^ 40 * 3697153 * 2
def baseEnd_3697153 : Nat := 1898416542212278605584609

theorem tailTrace_3697153 : CollatzResearch.WordTrace tailWord_3697153 prefixEnd_3697153 1898416542212278605584609 := by
  unfold tailWord_3697153
  simp only [CollatzResearch.WordTrace]
  refine ⟨134846247974853579307320113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89897498649902386204880075 134846247974853579307320113)
  ·
    refine ⟨101134685981140184480490085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134846247974853579307320113 101134685981140184480490085)
    ·
      refine ⟨18962753621463784590091891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 101134685981140184480490085 18962753621463784590091891)
      ·
        refine ⟨28444130432195676885137837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18962753621463784590091891 28444130432195676885137837)
        ·
          refine ⟨10666548912073378831926689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28444130432195676885137837 10666548912073378831926689)
          ·
            refine ⟨7999911684055034123945017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10666548912073378831926689 7999911684055034123945017)
            ·
              refine ⟨5999933763041275592958763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7999911684055034123945017 5999933763041275592958763)
              ·
                refine ⟨8999900644561913389438145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5999933763041275592958763 8999900644561913389438145)
                ·
                  refine ⟨6749925483421435042078609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8999900644561913389438145 6749925483421435042078609)
                  ·
                    refine ⟨5062444112566076281558957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6749925483421435042078609 5062444112566076281558957)
                    ·
                      refine ⟨1898416542212278605584609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5062444112566076281558957 1898416542212278605584609)
                      ·
                        rfl

theorem cell23_3697153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 2, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 2, 2, 1, 2, 2, 3].length) (baseStart_3697153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3697153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3697153 prefixEnd_3697153 := by exact prefixLift 3697153
  have htrace : WordTrace (prefixWord ++ tailWord_3697153) baseStart_3697153 baseEnd_3697153 := by
    simpa [prefixWord, tailWord_3697153, baseEnd_3697153] using wordTrace_append hprefix tailTrace_3697153
  have hstable : (prefixWord ++ tailWord_3697153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3697153).length < 2 ^ (prefixWord ++ tailWord_3697153).sum := by decide
  have hdescent : baseEnd_3697153 < baseStart_3697153 := by decide
  rcases family_descends (prefixWord ++ tailWord_3697153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3697204 : List Nat := [2, 5, 1, 3, 2, 1, 1, 1, 2, 2, 3]
def baseStart_3697204 : Nat := 118140960795 + 3697204 * 2 ^ 59
def prefixEnd_3697204 : Nat := 4983230072969 + 3 ^ 40 * 3697204 * 2
def baseEnd_3697204 : Nat := 1898442729725657906046875

theorem tailTrace_3697204 : CollatzResearch.WordTrace tailWord_3697204 prefixEnd_3697204 1898442729725657906046875 := by
  unfold tailWord_3697204
  simp only [CollatzResearch.WordTrace]
  refine ⟨67424054048834407508713333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89898738731779210011617777 67424054048834407508713333)
  ·
    refine ⟨6321005067078225703941875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 67424054048834407508713333 6321005067078225703941875)
    ·
      refine ⟨9481507600617338555912813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6321005067078225703941875 9481507600617338555912813)
      ·
        refine ⟨3555565350231501958467305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9481507600617338555912813 3555565350231501958467305)
        ·
          refine ⟨2666674012673626468850479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3555565350231501958467305 2666674012673626468850479)
          ·
            refine ⟨4000011019010439703275719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2666674012673626468850479 4000011019010439703275719)
            ·
              refine ⟨6000016528515659554913579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4000011019010439703275719 6000016528515659554913579)
              ·
                refine ⟨9000024792773489332370369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6000016528515659554913579 9000024792773489332370369)
                ·
                  refine ⟨6750018594580116999277777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9000024792773489332370369 6750018594580116999277777)
                  ·
                    refine ⟨5062513945935087749458333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6750018594580116999277777 5062513945935087749458333)
                    ·
                      refine ⟨1898442729725657906046875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5062513945935087749458333 1898442729725657906046875)
                      ·
                        rfl

theorem cell23_3697204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 2, 1, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 2, 1, 1, 1, 2, 2, 3].length) (baseStart_3697204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3697204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3697204 prefixEnd_3697204 := by exact prefixLift 3697204
  have htrace : WordTrace (prefixWord ++ tailWord_3697204) baseStart_3697204 baseEnd_3697204 := by
    simpa [prefixWord, tailWord_3697204, baseEnd_3697204] using wordTrace_append hprefix tailTrace_3697204
  have hstable : (prefixWord ++ tailWord_3697204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3697204).length < 2 ^ (prefixWord ++ tailWord_3697204).sum := by decide
  have hdescent : baseEnd_3697204 < baseStart_3697204 := by decide
  rcases family_descends (prefixWord ++ tailWord_3697204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3697210 : List Nat := [3, 1, 1, 1, 3, 5, 1, 1, 2, 3, 2]
def baseStart_3697210 : Nat := 118140960795 + 3697210 * 2 ^ 59
def prefixEnd_3697210 : Nat := 4983230072969 + 3 ^ 40 * 3697210 * 2
def baseEnd_3697210 : Nat := 1898445810609584882571847

theorem tailTrace_3697210 : CollatzResearch.WordTrace tailWord_3697210 prefixEnd_3697210 1898445810609584882571847 := by
  unfold tailWord_3697210
  simp only [CollatzResearch.WordTrace]
  refine ⟨33712081733911769510536271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89898884623764718694763389 33712081733911769510536271)
  ·
    refine ⟨50568122600867654265804407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33712081733911769510536271 50568122600867654265804407)
    ·
      refine ⟨75852183901301481398706611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50568122600867654265804407 75852183901301481398706611)
      ·
        refine ⟨113778275851952222098059917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75852183901301481398706611 113778275851952222098059917)
        ·
          refine ⟨42666853444482083286772469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 113778275851952222098059917 42666853444482083286772469)
          ·
            refine ⟨4000017510420195308134919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 42666853444482083286772469 4000017510420195308134919)
            ·
              refine ⟨6000026265630292962202379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4000017510420195308134919 6000026265630292962202379)
              ·
                refine ⟨9000039398445439443303569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6000026265630292962202379 9000039398445439443303569)
                ·
                  refine ⟨6750029548834079582477677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9000039398445439443303569 6750029548834079582477677)
                  ·
                    refine ⟨2531261080812779843429129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6750029548834079582477677 2531261080812779843429129)
                    ·
                      refine ⟨1898445810609584882571847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2531261080812779843429129 1898445810609584882571847)
                      ·
                        rfl

theorem cell23_3697210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 5, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 5, 1, 1, 2, 3, 2].length) (baseStart_3697210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3697210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3697210 prefixEnd_3697210 := by exact prefixLift 3697210
  have htrace : WordTrace (prefixWord ++ tailWord_3697210) baseStart_3697210 baseEnd_3697210 := by
    simpa [prefixWord, tailWord_3697210, baseEnd_3697210] using wordTrace_append hprefix tailTrace_3697210
  have hstable : (prefixWord ++ tailWord_3697210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3697210).length < 2 ^ (prefixWord ++ tailWord_3697210).sum := by decide
  have hdescent : baseEnd_3697210 < baseStart_3697210 := by decide
  rcases family_descends (prefixWord ++ tailWord_3697210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3697217 : List Nat := [1, 2, 5, 1, 1, 3, 2, 3, 1, 1, 3]
def baseStart_3697217 : Nat := 118140960795 + 3697217 * 2 ^ 59
def prefixEnd_3697217 : Nat := 4983230072969 + 3 ^ 40 * 3697217 * 2
def baseEnd_3697217 : Nat := 1898449404974166355184315

theorem tailTrace_3697217 : CollatzResearch.WordTrace tailWord_3697217 prefixEnd_3697217 1898449404974166355184315 := by
  unfold tailWord_3697217
  simp only [CollatzResearch.WordTrace]
  refine ⟨134848582246621718237649905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89899054831081145491766603 134848582246621718237649905)
  ·
    refine ⟨101136436684966288678237429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134848582246621718237649905 101136436684966288678237429)
    ·
      refine ⟨9481540939215589563584759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 101136436684966288678237429 9481540939215589563584759)
      ·
        refine ⟨14222311408823384345377139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9481540939215589563584759 14222311408823384345377139)
        ·
          refine ⟨21333467113235076518065709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14222311408823384345377139 21333467113235076518065709)
          ·
            refine ⟨8000050167463153694274641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21333467113235076518065709 8000050167463153694274641)
            ·
              refine ⟨6000037625597365270705981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8000050167463153694274641 6000037625597365270705981)
              ·
                refine ⟨2250014109599011976514743, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6000037625597365270705981 2250014109599011976514743)
                ·
                  refine ⟨3375021164398517964772115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2250014109599011976514743 3375021164398517964772115)
                  ·
                    refine ⟨5062531746597776947158173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3375021164398517964772115 5062531746597776947158173)
                    ·
                      refine ⟨1898449404974166355184315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5062531746597776947158173 1898449404974166355184315)
                      ·
                        rfl

theorem cell23_3697217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 3, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 3, 2, 3, 1, 1, 3].length) (baseStart_3697217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3697217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3697217 prefixEnd_3697217 := by exact prefixLift 3697217
  have htrace : WordTrace (prefixWord ++ tailWord_3697217) baseStart_3697217 baseEnd_3697217 := by
    simpa [prefixWord, tailWord_3697217, baseEnd_3697217] using wordTrace_append hprefix tailTrace_3697217
  have hstable : (prefixWord ++ tailWord_3697217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3697217).length < 2 ^ (prefixWord ++ tailWord_3697217).sum := by decide
  have hdescent : baseEnd_3697217 < baseStart_3697217 := by decide
  rcases family_descends (prefixWord ++ tailWord_3697217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3697223 : List Nat := [1, 1, 4, 1, 4, 2, 1, 3, 1, 1, 4]
def baseStart_3697223 : Nat := 118140960795 + 3697223 * 2 ^ 59
def prefixEnd_3697223 : Nat := 4983230072969 + 3 ^ 40 * 3697223 * 2
def baseEnd_3697223 : Nat := 1898452485858093331709287

theorem tailTrace_3697223 : CollatzResearch.WordTrace tailWord_3697223 prefixEnd_3697223 1898452485858093331709287 := by
  unfold tailWord_3697223
  simp only [CollatzResearch.WordTrace]
  refine ⟨134848801084599981262368323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89899200723066654174912215 134848801084599981262368323)
  ·
    refine ⟨202273201626899971893552485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134848801084599981262368323 202273201626899971893552485)
    ·
      refine ⟨37926225305043744730041091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 202273201626899971893552485 37926225305043744730041091)
      ·
        refine ⟨56889337957565617095061637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37926225305043744730041091 56889337957565617095061637)
        ·
          refine ⟨10666750867043553205324057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 56889337957565617095061637 10666750867043553205324057)
          ·
            refine ⟨8000063150282664903993043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10666750867043553205324057 8000063150282664903993043)
            ·
              refine ⟨12000094725423997355989565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8000063150282664903993043 12000094725423997355989565)
              ·
                refine ⟨4500035522033999008496087, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12000094725423997355989565 4500035522033999008496087)
                ·
                  refine ⟨6750053283050998512744131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4500035522033999008496087 6750053283050998512744131)
                  ·
                    refine ⟨10125079924576497769116197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6750053283050998512744131 10125079924576497769116197)
                    ·
                      refine ⟨1898452485858093331709287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10125079924576497769116197 1898452485858093331709287)
                      ·
                        rfl

theorem cell23_3697223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 2, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 2, 1, 3, 1, 1, 4].length) (baseStart_3697223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3697223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3697223 prefixEnd_3697223 := by exact prefixLift 3697223
  have htrace : WordTrace (prefixWord ++ tailWord_3697223) baseStart_3697223 baseEnd_3697223 := by
    simpa [prefixWord, tailWord_3697223, baseEnd_3697223] using wordTrace_append hprefix tailTrace_3697223
  have hstable : (prefixWord ++ tailWord_3697223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3697223).length < 2 ^ (prefixWord ++ tailWord_3697223).sum := by decide
  have hdescent : baseEnd_3697223 < baseStart_3697223 := by decide
  rcases family_descends (prefixWord ++ tailWord_3697223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3697233 : List Nat := [1, 2, 2, 1, 3, 3, 3, 2, 2, 4]
def baseStart_3697233 : Nat := 118140960795 + 3697233 * 2 ^ 59
def prefixEnd_3697233 : Nat := 4983230072969 + 3 ^ 40 * 3697233 * 2
def baseEnd_3697233 : Nat := 632819206888212764194747

theorem tailTrace_3697233 : CollatzResearch.WordTrace tailWord_3697233 prefixEnd_3697233 632819206888212764194747 := by
  unfold tailWord_3697233
  simp only [CollatzResearch.WordTrace]
  refine ⟨134849165814563752970232353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89899443876375835313488235 134849165814563752970232353)
  ·
    refine ⟨101136874360922814727674265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134849165814563752970232353 101136874360922814727674265)
    ·
      refine ⟨75852655770692111045755699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101136874360922814727674265 75852655770692111045755699)
      ·
        refine ⟨113778983656038166568633549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75852655770692111045755699 113778983656038166568633549)
        ·
          refine ⟨42667118871014312463237581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 113778983656038166568633549 42667118871014312463237581)
          ·
            refine ⟨16000169576630367173714093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42667118871014312463237581 16000169576630367173714093)
            ·
              refine ⟨6000063591236387690142785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16000169576630367173714093 6000063591236387690142785)
              ·
                refine ⟨4500047693427290767607089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6000063591236387690142785 4500047693427290767607089)
                ·
                  refine ⟨3375035770070468075705317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4500047693427290767607089 3375035770070468075705317)
                  ·
                    refine ⟨632819206888212764194747, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3375035770070468075705317 632819206888212764194747)
                    ·
                      rfl

theorem cell23_3697233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 3, 2, 2, 4].length) (baseStart_3697233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3697233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3697233 prefixEnd_3697233 := by exact prefixLift 3697233
  have htrace : WordTrace (prefixWord ++ tailWord_3697233) baseStart_3697233 baseEnd_3697233 := by
    simpa [prefixWord, tailWord_3697233, baseEnd_3697233] using wordTrace_append hprefix tailTrace_3697233
  have hstable : (prefixWord ++ tailWord_3697233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3697233).length < 2 ^ (prefixWord ++ tailWord_3697233).sum := by decide
  have hdescent : baseEnd_3697233 < baseStart_3697233 := by decide
  rcases family_descends (prefixWord ++ tailWord_3697233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3697273 : List Nat := [1, 2, 1, 3, 3, 2, 1, 2, 4, 1, 3]
def baseStart_3697273 : Nat := 118140960795 + 3697273 * 2 ^ 59
def prefixEnd_3697273 : Nat := 4983230072969 + 3 ^ 40 * 3697273 * 2
def baseEnd_3697273 : Nat := 1898478159890818136084057

theorem tailTrace_3697273 : CollatzResearch.WordTrace tailWord_3697273 prefixEnd_3697273 1898478159890818136084057 := by
  unfold tailWord_3697273
  simp only [CollatzResearch.WordTrace]
  refine ⟨134850624734418839801688473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89900416489612559867792315 134850624734418839801688473)
  ·
    refine ⟨101137968550814129851266355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134850624734418839801688473 101137968550814129851266355)
    ·
      refine ⟨151706952826221194776899533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101137968550814129851266355 151706952826221194776899533)
      ·
        refine ⟨56890107309832948041337325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 151706952826221194776899533 56890107309832948041337325)
        ·
          refine ⟨21333790241187355515501497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56890107309832948041337325 21333790241187355515501497)
          ·
            refine ⟨16000342680890516636626123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21333790241187355515501497 16000342680890516636626123)
            ·
              refine ⟨24000514021335774954939185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16000342680890516636626123 24000514021335774954939185)
              ·
                refine ⟨18000385516001831216204389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24000514021335774954939185 18000385516001831216204389)
                ·
                  refine ⟨3375072284250343353038323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18000385516001831216204389 3375072284250343353038323)
                  ·
                    refine ⟨5062608426375515029557485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3375072284250343353038323 5062608426375515029557485)
                    ·
                      refine ⟨1898478159890818136084057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5062608426375515029557485 1898478159890818136084057)
                      ·
                        rfl

theorem cell23_3697273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 1, 2, 4, 1, 3].length) (baseStart_3697273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3697273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3697273 prefixEnd_3697273 := by exact prefixLift 3697273
  have htrace : WordTrace (prefixWord ++ tailWord_3697273) baseStart_3697273 baseEnd_3697273 := by
    simpa [prefixWord, tailWord_3697273, baseEnd_3697273] using wordTrace_append hprefix tailTrace_3697273
  have hstable : (prefixWord ++ tailWord_3697273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3697273).length < 2 ^ (prefixWord ++ tailWord_3697273).sum := by decide
  have hdescent : baseEnd_3697273 < baseStart_3697273 := by decide
  rcases family_descends (prefixWord ++ tailWord_3697273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3697316 : List Nat := [2, 3, 1, 2, 2, 1, 1, 1, 4, 1, 5]
def baseStart_3697316 : Nat := 118140960795 + 3697316 * 2 ^ 59
def prefixEnd_3697316 : Nat := 4983230072969 + 3 ^ 40 * 3697316 * 2
def baseEnd_3697316 : Nat := 1898500239558961467846359

theorem tailTrace_3697316 : CollatzResearch.WordTrace tailWord_3697316 prefixEnd_3697316 1898500239558961467846359 := by
  unfold tailWord_3697316
  simp only [CollatzResearch.WordTrace]
  refine ⟨67426096536631529072751901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89901462048842038763669201 67426096536631529072751901)
  ·
    refine ⟨25284786201236823402281963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67426096536631529072751901 25284786201236823402281963)
    ·
      refine ⟨37927179301855235103422945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25284786201236823402281963 37927179301855235103422945)
      ·
        refine ⟨28445384476391426327567209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37927179301855235103422945 28445384476391426327567209)
        ·
          refine ⟨21334038357293569745675407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28445384476391426327567209 21334038357293569745675407)
          ·
            refine ⟨32001057535940354618513111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21334038357293569745675407 32001057535940354618513111)
            ·
              refine ⟨48001586303910531927769667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32001057535940354618513111 48001586303910531927769667)
              ·
                refine ⟨72002379455865797891654501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48001586303910531927769667 72002379455865797891654501)
                ·
                  refine ⟨13500446147974837104685219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 72002379455865797891654501 13500446147974837104685219)
                  ·
                    refine ⟨20250669221962255657027829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13500446147974837104685219 20250669221962255657027829)
                    ·
                      refine ⟨1898500239558961467846359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20250669221962255657027829 1898500239558961467846359)
                      ·
                        rfl

theorem cell23_3697316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 1, 1, 4, 1, 5].length) (baseStart_3697316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3697316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3697316 prefixEnd_3697316 := by exact prefixLift 3697316
  have htrace : WordTrace (prefixWord ++ tailWord_3697316) baseStart_3697316 baseEnd_3697316 := by
    simpa [prefixWord, tailWord_3697316, baseEnd_3697316] using wordTrace_append hprefix tailTrace_3697316
  have hstable : (prefixWord ++ tailWord_3697316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3697316).length < 2 ^ (prefixWord ++ tailWord_3697316).sum := by decide
  have hdescent : baseEnd_3697316 < baseStart_3697316 := by decide
  rcases family_descends (prefixWord ++ tailWord_3697316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3697333 : List Nat := [1, 3, 3, 3, 1, 1, 2, 1, 2, 1, 5]
def baseStart_3697333 : Nat := 118140960795 + 3697333 * 2 ^ 59
def prefixEnd_3697333 : Nat := 4983230072969 + 3 ^ 40 * 3697333 * 2
def baseEnd_3697333 : Nat := 1898508968730087901333781

theorem tailTrace_3697333 : CollatzResearch.WordTrace tailWord_3697333 prefixEnd_3697333 1898508968730087901333781 := by
  unfold tailWord_3697333
  simp only [CollatzResearch.WordTrace]
  refine ⟨134852813114201470048872653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89901875409467646699248435 134852813114201470048872653)
  ·
    refine ⟨50569804917825551268327245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 134852813114201470048872653 50569804917825551268327245)
    ·
      refine ⟨18963676844184581725622717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50569804917825551268327245 18963676844184581725622717)
      ·
        refine ⟨7111378816569218147108519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18963676844184581725622717 7111378816569218147108519)
        ·
          refine ⟨10667068224853827220662779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7111378816569218147108519 10667068224853827220662779)
          ·
            refine ⟨16000602337280740830994169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10667068224853827220662779 16000602337280740830994169)
            ·
              refine ⟨12000451752960555623245627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16000602337280740830994169 12000451752960555623245627)
              ·
                refine ⟨18000677629440833434868441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12000451752960555623245627 18000677629440833434868441)
                ·
                  refine ⟨13500508222080625076151331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18000677629440833434868441 13500508222080625076151331)
                  ·
                    refine ⟨20250762333120937614226997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13500508222080625076151331 20250762333120937614226997)
                    ·
                      refine ⟨1898508968730087901333781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20250762333120937614226997 1898508968730087901333781)
                      ·
                        rfl

theorem cell23_3697333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 2, 1, 2, 1, 5].length) (baseStart_3697333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3697333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3697333 prefixEnd_3697333 := by exact prefixLift 3697333
  have htrace : WordTrace (prefixWord ++ tailWord_3697333) baseStart_3697333 baseEnd_3697333 := by
    simpa [prefixWord, tailWord_3697333, baseEnd_3697333] using wordTrace_append hprefix tailTrace_3697333
  have hstable : (prefixWord ++ tailWord_3697333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3697333).length < 2 ^ (prefixWord ++ tailWord_3697333).sum := by decide
  have hdescent : baseEnd_3697333 < baseStart_3697333 := by decide
  rcases family_descends (prefixWord ++ tailWord_3697333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3697480 : List Nat := [2, 1, 3, 1, 1, 3, 1, 2, 4, 3, 2]
def baseStart_3697480 : Nat := 118140960795 + 3697480 * 2 ^ 59
def prefixEnd_3697480 : Nat := 4983230072969 + 3 ^ 40 * 3697480 * 2
def baseEnd_3697480 : Nat := 1898584450386298826195605

theorem tailTrace_3697480 : CollatzResearch.WordTrace tailWord_3697480 prefixEnd_3697480 1898584450386298826195605 := by
  unfold tailWord_3697480
  simp only [CollatzResearch.WordTrace]
  refine ⟨67429087322334457077236947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89905449763112609436315929 67429087322334457077236947)
  ·
    refine ⟨101143630983501685615855421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67429087322334457077236947 101143630983501685615855421)
    ·
      refine ⟨37928861618813132105945783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 101143630983501685615855421 37928861618813132105945783)
      ·
        refine ⟨56893292428219698158918675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37928861618813132105945783 56893292428219698158918675)
        ·
          refine ⟨85339938642329547238378013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56893292428219698158918675 85339938642329547238378013)
          ·
            refine ⟨32002476990873580214391755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 85339938642329547238378013 32002476990873580214391755)
            ·
              refine ⟨48003715486310370321587633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32002476990873580214391755 48003715486310370321587633)
              ·
                refine ⟨36002786614732777741190725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48003715486310370321587633 36002786614732777741190725)
                ·
                  refine ⟨6750522490262395826473261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36002786614732777741190725 6750522490262395826473261)
                  ·
                    refine ⟨2531445933848398434927473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6750522490262395826473261 2531445933848398434927473)
                    ·
                      refine ⟨1898584450386298826195605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2531445933848398434927473 1898584450386298826195605)
                      ·
                        rfl

theorem cell23_3697480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 1, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 1, 2, 4, 3, 2].length) (baseStart_3697480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3697480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3697480 prefixEnd_3697480 := by exact prefixLift 3697480
  have htrace : WordTrace (prefixWord ++ tailWord_3697480) baseStart_3697480 baseEnd_3697480 := by
    simpa [prefixWord, tailWord_3697480, baseEnd_3697480] using wordTrace_append hprefix tailTrace_3697480
  have hstable : (prefixWord ++ tailWord_3697480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3697480).length < 2 ^ (prefixWord ++ tailWord_3697480).sum := by decide
  have hdescent : baseEnd_3697480 < baseStart_3697480 := by decide
  rcases family_descends (prefixWord ++ tailWord_3697480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3697497 : List Nat := [1, 2, 1, 2, 2, 5, 2, 1, 2, 3, 2]
def baseStart_3697497 : Nat := 118140960795 + 3697497 * 2 ^ 59
def prefixEnd_3697497 : Nat := 4983230072969 + 3 ^ 40 * 3697497 * 2
def baseEnd_3697497 : Nat := 1898593179557425259683027

theorem tailTrace_3697497 : CollatzResearch.WordTrace tailWord_3697497 prefixEnd_3697497 1898593179557425259683027 := by
  unfold tailWord_3697497
  simp only [CollatzResearch.WordTrace]
  refine ⟨134858794685607326057842745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89905863123738217371895163 134858794685607326057842745)
  ·
    refine ⟨101144096014205494543382059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134858794685607326057842745 101144096014205494543382059)
    ·
      refine ⟨151716144021308241815073089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101144096014205494543382059 151716144021308241815073089)
      ·
        refine ⟨113787108015981181361304817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 151716144021308241815073089 113787108015981181361304817)
        ·
          refine ⟨85340331011985886020978613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 113787108015981181361304817 85340331011985886020978613)
          ·
            refine ⟨8000656032373676814466745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 85340331011985886020978613 8000656032373676814466745)
            ·
              refine ⟨6000492024280257610850059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8000656032373676814466745 6000492024280257610850059)
              ·
                refine ⟨9000738036420386416275089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6000492024280257610850059 9000738036420386416275089)
                ·
                  refine ⟨6750553527315289812206317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9000738036420386416275089 6750553527315289812206317)
                  ·
                    refine ⟨2531457572743233679577369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6750553527315289812206317 2531457572743233679577369)
                    ·
                      refine ⟨1898593179557425259683027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2531457572743233679577369 1898593179557425259683027)
                      ·
                        rfl

theorem cell23_3697497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 5, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 5, 2, 1, 2, 3, 2].length) (baseStart_3697497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3697497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3697497 prefixEnd_3697497 := by exact prefixLift 3697497
  have htrace : WordTrace (prefixWord ++ tailWord_3697497) baseStart_3697497 baseEnd_3697497 := by
    simpa [prefixWord, tailWord_3697497, baseEnd_3697497] using wordTrace_append hprefix tailTrace_3697497
  have hstable : (prefixWord ++ tailWord_3697497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3697497).length < 2 ^ (prefixWord ++ tailWord_3697497).sum := by decide
  have hdescent : baseEnd_3697497 < baseStart_3697497 := by decide
  rcases family_descends (prefixWord ++ tailWord_3697497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3697503 : List Nat := [1, 1, 2, 3, 1, 3, 3, 2, 1, 6]
def baseStart_3697503 : Nat := 118140960795 + 3697503 * 2 ^ 59
def prefixEnd_3697503 : Nat := 4983230072969 + 3 ^ 40 * 3697503 * 2
def baseEnd_3697503 : Nat := 632865420147117412069333

theorem tailTrace_3697503 : CollatzResearch.WordTrace tailWord_3697503 prefixEnd_3697503 632865420147117412069333 := by
  unfold tailWord_3697503
  simp only [CollatzResearch.WordTrace]
  refine ⟨134859013523585589082561163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89906009015723726055040775 134859013523585589082561163)
  ·
    refine ⟨202288520285378383623841745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134859013523585589082561163 202288520285378383623841745)
    ·
      refine ⟨151716390214033787717881309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 202288520285378383623841745 151716390214033787717881309)
      ·
        refine ⟨56893646330262670394205491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 151716390214033787717881309 56893646330262670394205491)
        ·
          refine ⟨85340469495394005591308237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56893646330262670394205491 85340469495394005591308237)
          ·
            refine ⟨32002676060772752096740589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 85340469495394005591308237 32002676060772752096740589)
            ·
              refine ⟨12001003522789782036277721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32002676060772752096740589 12001003522789782036277721)
              ·
                refine ⟨9000752642092336527208291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12001003522789782036277721 9000752642092336527208291)
                ·
                  refine ⟨13501128963138504790812437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9000752642092336527208291 13501128963138504790812437)
                  ·
                    refine ⟨632865420147117412069333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13501128963138504790812437 632865420147117412069333)
                    ·
                      rfl

theorem cell23_3697503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 3, 2, 1, 6].length) (baseStart_3697503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3697503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3697503 prefixEnd_3697503 := by exact prefixLift 3697503
  have htrace : WordTrace (prefixWord ++ tailWord_3697503) baseStart_3697503 baseEnd_3697503 := by
    simpa [prefixWord, tailWord_3697503, baseEnd_3697503] using wordTrace_append hprefix tailTrace_3697503
  have hstable : (prefixWord ++ tailWord_3697503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3697503).length < 2 ^ (prefixWord ++ tailWord_3697503).sum := by decide
  have hdescent : baseEnd_3697503 < baseStart_3697503 := by decide
  rcases family_descends (prefixWord ++ tailWord_3697503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3697507 : List Nat := [1, 1, 1, 5, 3, 2, 3, 1, 1, 5]
def baseStart_3697507 : Nat := 118140960795 + 3697507 * 2 ^ 59
def prefixEnd_3697507 : Nat := 4983230072969 + 3 ^ 40 * 3697507 * 2
def baseEnd_3697507 : Nat := 632866104787990073519327

theorem tailTrace_3697507 : CollatzResearch.WordTrace tailWord_3697507 prefixEnd_3697507 632866104787990073519327 := by
  unfold tailWord_3697507
  simp only [CollatzResearch.WordTrace]
  refine ⟨134859159415571097765706775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89906106277047398510471183 134859159415571097765706775)
  ·
    refine ⟨202288739123356646648560163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134859159415571097765706775 202288739123356646648560163)
    ·
      refine ⟨303433108685034969972840245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 202288739123356646648560163 303433108685034969972840245)
      ·
        refine ⟨28446853939222028434953773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 303433108685034969972840245 28446853939222028434953773)
        ·
          refine ⟨10667570227208260663107665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28446853939222028434953773 10667570227208260663107665)
          ·
            refine ⟨8000677670406195497330749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10667570227208260663107665 8000677670406195497330749)
            ·
              refine ⟨3000254126402323311499031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8000677670406195497330749 3000254126402323311499031)
              ·
                refine ⟨4500381189603484967248547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3000254126402323311499031 4500381189603484967248547)
                ·
                  refine ⟨6750571784405227450872821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4500381189603484967248547 6750571784405227450872821)
                  ·
                    refine ⟨632866104787990073519327, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6750571784405227450872821 632866104787990073519327)
                    ·
                      rfl

theorem cell23_3697507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 2, 3, 1, 1, 5].length) (baseStart_3697507 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3697507 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3697507 prefixEnd_3697507 := by exact prefixLift 3697507
  have htrace : WordTrace (prefixWord ++ tailWord_3697507) baseStart_3697507 baseEnd_3697507 := by
    simpa [prefixWord, tailWord_3697507, baseEnd_3697507] using wordTrace_append hprefix tailTrace_3697507
  have hstable : (prefixWord ++ tailWord_3697507).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3697507).length < 2 ^ (prefixWord ++ tailWord_3697507).sum := by decide
  have hdescent : baseEnd_3697507 < baseStart_3697507 := by decide
  rcases family_descends (prefixWord ++ tailWord_3697507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3697520 : List Nat := [2, 1, 1, 1, 4, 1, 3, 4, 2, 4]
def baseStart_3697520 : Nat := 118140960795 + 3697520 * 2 ^ 59
def prefixEnd_3697520 : Nat := 4983230072969 + 3 ^ 40 * 3697520 * 2
def baseEnd_3697520 : Nat := 632868329870826223231807

theorem tailTrace_3697520 : CollatzResearch.WordTrace tailWord_3697520 prefixEnd_3697520 632868329870826223231807 := by
  unfold tailWord_3697520
  simp only [CollatzResearch.WordTrace]
  refine ⟨67429816782262000492965007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89906422376349333990620009 67429816782262000492965007)
  ·
    refine ⟨101144725173393000739447511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67429816782262000492965007 101144725173393000739447511)
    ·
      refine ⟨151717087760089501109171267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101144725173393000739447511 151717087760089501109171267)
      ·
        refine ⟨227575631640134251663756901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151717087760089501109171267 227575631640134251663756901)
        ·
          refine ⟨42670430932525172186954419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 227575631640134251663756901 42670430932525172186954419)
          ·
            refine ⟨64005646398787758280431629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42670430932525172186954419 64005646398787758280431629)
            ·
              refine ⟨24002117399545409355161861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 64005646398787758280431629 24002117399545409355161861)
              ·
                refine ⟨4500397012414764254092849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24002117399545409355161861 4500397012414764254092849)
                ·
                  refine ⟨3375297759311073190569637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4500397012414764254092849 3375297759311073190569637)
                  ·
                    refine ⟨632868329870826223231807, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3375297759311073190569637 632868329870826223231807)
                    ·
                      rfl

theorem cell23_3697520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 3, 4, 2, 4].length) (baseStart_3697520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3697520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3697520 prefixEnd_3697520 := by exact prefixLift 3697520
  have htrace : WordTrace (prefixWord ++ tailWord_3697520) baseStart_3697520 baseEnd_3697520 := by
    simpa [prefixWord, tailWord_3697520, baseEnd_3697520] using wordTrace_append hprefix tailTrace_3697520
  have hstable : (prefixWord ++ tailWord_3697520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3697520).length < 2 ^ (prefixWord ++ tailWord_3697520).sum := by decide
  have hdescent : baseEnd_3697520 < baseStart_3697520 := by decide
  rcases family_descends (prefixWord ++ tailWord_3697520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3697521 : List Nat := [1, 2, 2, 2, 1, 6, 2, 2, 1, 1, 3]
def baseStart_3697521 : Nat := 118140960795 + 3697521 * 2 ^ 59
def prefixEnd_3697521 : Nat := 4983230072969 + 3 ^ 40 * 3697521 * 2
def baseEnd_3697521 : Nat := 1898605503093133165782917

theorem tailTrace_3697521 : CollatzResearch.WordTrace tailWord_3697521 prefixEnd_3697521 1898605503093133165782917 := by
  unfold tailWord_3697521
  simp only [CollatzResearch.WordTrace]
  refine ⟨134859670037520378156716417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89906446691680252104477611 134859670037520378156716417)
  ·
    refine ⟨101144752528140283617537313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134859670037520378156716417 101144752528140283617537313)
    ·
      refine ⟨75858564396105212713152985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101144752528140283617537313 75858564396105212713152985)
      ·
        refine ⟨56893923297078909534864739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75858564396105212713152985 56893923297078909534864739)
        ·
          refine ⟨85340884945618364302297109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56893923297078909534864739 85340884945618364302297109)
          ·
            refine ⟨4000353981825860826670177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 85340884945618364302297109 4000353981825860826670177)
            ·
              refine ⟨3000265486369395620002633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4000353981825860826670177 3000265486369395620002633)
              ·
                refine ⟨2250199114777046715001975, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3000265486369395620002633 2250199114777046715001975)
                ·
                  refine ⟨3375298672165570072502963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2250199114777046715001975 3375298672165570072502963)
                  ·
                    refine ⟨5062948008248355108754445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3375298672165570072502963 5062948008248355108754445)
                    ·
                      refine ⟨1898605503093133165782917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5062948008248355108754445 1898605503093133165782917)
                      ·
                        rfl

theorem cell23_3697521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 6, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 6, 2, 2, 1, 1, 3].length) (baseStart_3697521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3697521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3697521 prefixEnd_3697521 := by exact prefixLift 3697521
  have htrace : WordTrace (prefixWord ++ tailWord_3697521) baseStart_3697521 baseEnd_3697521 := by
    simpa [prefixWord, tailWord_3697521, baseEnd_3697521] using wordTrace_append hprefix tailTrace_3697521
  have hstable : (prefixWord ++ tailWord_3697521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3697521).length < 2 ^ (prefixWord ++ tailWord_3697521).sum := by decide
  have hdescent : baseEnd_3697521 < baseStart_3697521 := by decide
  rcases family_descends (prefixWord ++ tailWord_3697521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3697533 : List Nat := [1, 4, 1, 1, 2, 1, 5, 8]
def baseStart_3697533 : Nat := 118140960795 + 3697533 * 2 ^ 59
def prefixEnd_3697533 : Nat := 4983230072969 + 3 ^ 40 * 3697533 * 2
def baseEnd_3697533 : Nat := 70318950550406930327143

theorem tailTrace_3697533 : CollatzResearch.WordTrace tailWord_3697533 prefixEnd_3697533 70318950550406930327143 := by
  unfold tailWord_3697533
  simp only [CollatzResearch.WordTrace]
  refine ⟨134860107713476904206153253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89906738475651269470768835 134860107713476904206153253)
  ·
    refine ⟨25286270196276919538653735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 134860107713476904206153253 25286270196276919538653735)
    ·
      refine ⟨37929405294415379307980603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25286270196276919538653735 37929405294415379307980603)
      ·
        refine ⟨56894107941623068961970905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37929405294415379307980603 56894107941623068961970905)
        ·
          refine ⟨42670580956217301721478179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56894107941623068961970905 42670580956217301721478179)
          ·
            refine ⟨64005871434325952582217269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42670580956217301721478179 64005871434325952582217269)
            ·
              refine ⟨6000550446968058054582869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 64005871434325952582217269 6000550446968058054582869)
              ·
                refine ⟨70318950550406930327143, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6000550446968058054582869 70318950550406930327143)
                ·
                  rfl

theorem cell23_3697533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 5, 8].length) (baseStart_3697533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3697533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3697533 prefixEnd_3697533 := by exact prefixLift 3697533
  have htrace : WordTrace (prefixWord ++ tailWord_3697533) baseStart_3697533 baseEnd_3697533 := by
    simpa [prefixWord, tailWord_3697533, baseEnd_3697533] using wordTrace_append hprefix tailTrace_3697533
  have hstable : (prefixWord ++ tailWord_3697533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3697533).length < 2 ^ (prefixWord ++ tailWord_3697533).sum := by decide
  have hdescent : baseEnd_3697533 < baseStart_3697533 := by decide
  rcases family_descends (prefixWord ++ tailWord_3697533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3697544 : List Nat := [2, 1, 3, 3, 2, 2, 1, 2, 3, 2, 2]
def baseStart_3697544 : Nat := 118140960795 + 3697544 * 2 ^ 59
def prefixEnd_3697544 : Nat := 4983230072969 + 3 ^ 40 * 3697544 * 2
def baseEnd_3697544 : Nat := 1898617313148186575795311

theorem tailTrace_3697544 : CollatzResearch.WordTrace tailWord_3697544 prefixEnd_3697544 1898617313148186575795311 := by
  unfold tailWord_3697544
  simp only [CollatzResearch.WordTrace]
  refine ⟨67430254458218526542401843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89907005944291368723202457 67430254458218526542401843)
  ·
    refine ⟨101145381687327789813602765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67430254458218526542401843 101145381687327789813602765)
    ·
      refine ⟨37929518132747921180101037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 101145381687327789813602765 37929518132747921180101037)
      ·
        refine ⟨14223569299780470442537889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37929518132747921180101037 14223569299780470442537889)
        ·
          refine ⟨10667676974835352831903417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14223569299780470442537889 10667676974835352831903417)
          ·
            refine ⟨8000757731126514623927563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10667676974835352831903417 8000757731126514623927563)
            ·
              refine ⟨12001136596689771935891345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8000757731126514623927563 12001136596689771935891345)
              ·
                refine ⟨9000852447517328951918509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12001136596689771935891345 9000852447517328951918509)
                ·
                  refine ⟨3375319667818998356969441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9000852447517328951918509 3375319667818998356969441)
                  ·
                    refine ⟨2531489750864248767727081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3375319667818998356969441 2531489750864248767727081)
                    ·
                      refine ⟨1898617313148186575795311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2531489750864248767727081 1898617313148186575795311)
                      ·
                        rfl

theorem cell23_3697544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 2, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 2, 1, 2, 3, 2, 2].length) (baseStart_3697544 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3697544 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3697544 prefixEnd_3697544 := by exact prefixLift 3697544
  have htrace : WordTrace (prefixWord ++ tailWord_3697544) baseStart_3697544 baseEnd_3697544 := by
    simpa [prefixWord, tailWord_3697544, baseEnd_3697544] using wordTrace_append hprefix tailTrace_3697544
  have hstable : (prefixWord ++ tailWord_3697544).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3697544).length < 2 ^ (prefixWord ++ tailWord_3697544).sum := by decide
  have hdescent : baseEnd_3697544 < baseStart_3697544 := by decide
  rcases family_descends (prefixWord ++ tailWord_3697544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3697558 : List Nat := [5, 3, 1, 1, 1, 3, 2, 1, 1, 5]
def baseStart_3697558 : Nat := 118140960795 + 3697558 * 2 ^ 59
def prefixEnd_3697558 : Nat := 4983230072969 + 3 ^ 40 * 3697558 * 2
def baseEnd_3697558 : Nat := 632874833959116507006749

theorem tailTrace_3697558 : CollatzResearch.WordTrace tailWord_3697558 prefixEnd_3697558 632874833959116507006749 := by
  unfold tailWord_3697558
  simp only [CollatzResearch.WordTrace]
  refine ⟨8428813721149145842238333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 89907346358924222317208885 8428813721149145842238333)
  ·
    refine ⟨3160805145430929690839375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8428813721149145842238333 3160805145430929690839375)
    ·
      refine ⟨4741207718146394536259063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3160805145430929690839375 4741207718146394536259063)
      ·
        refine ⟨7111811577219591804388595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4741207718146394536259063 7111811577219591804388595)
        ·
          refine ⟨10667717365829387706582893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7111811577219591804388595 10667717365829387706582893)
          ·
            refine ⟨4000394012186020389968585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10667717365829387706582893 4000394012186020389968585)
            ·
              refine ⟨3000295509139515292476439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4000394012186020389968585 3000295509139515292476439)
              ·
                refine ⟨4500443263709272938714659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3000295509139515292476439 4500443263709272938714659)
                ·
                  refine ⟨6750664895563909408071989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4500443263709272938714659 6750664895563909408071989)
                  ·
                    refine ⟨632874833959116507006749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6750664895563909408071989 632874833959116507006749)
                    ·
                      rfl

theorem cell23_3697558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 3, 2, 1, 1, 5].length) (baseStart_3697558 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3697558 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3697558 prefixEnd_3697558 := by exact prefixLift 3697558
  have htrace : WordTrace (prefixWord ++ tailWord_3697558) baseStart_3697558 baseEnd_3697558 := by
    simpa [prefixWord, tailWord_3697558, baseEnd_3697558] using wordTrace_append hprefix tailTrace_3697558
  have hstable : (prefixWord ++ tailWord_3697558).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3697558).length < 2 ^ (prefixWord ++ tailWord_3697558).sum := by decide
  have hdescent : baseEnd_3697558 < baseStart_3697558 := by decide
  rcases family_descends (prefixWord ++ tailWord_3697558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3697564 : List Nat := [2, 2, 3, 3, 2, 1, 1, 3, 1, 2, 3]
def baseStart_3697564 : Nat := 118140960795 + 3697564 * 2 ^ 59
def prefixEnd_3697564 : Nat := 4983230072969 + 3 ^ 40 * 3697564 * 2
def baseEnd_3697564 : Nat := 1898627582761276497545219

theorem tailTrace_3697564 : CollatzResearch.WordTrace tailWord_3697564 prefixEnd_3697564 1898627582761276497545219 := by
  unfold tailWord_3697564
  simp only [CollatzResearch.WordTrace]
  refine ⟨67430619188182298250265873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89907492250909731000354497 67430619188182298250265873)
  ·
    refine ⟨50572964391136723687699405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67430619188182298250265873 50572964391136723687699405)
    ·
      refine ⟨18964861646676271382887277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50572964391136723687699405 18964861646676271382887277)
      ·
        refine ⟨7111823117503601768582729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18964861646676271382887277 7111823117503601768582729)
        ·
          refine ⟨5333867338127701326437047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7111823117503601768582729 5333867338127701326437047)
          ·
            refine ⟨8000801007191551989655571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5333867338127701326437047 8000801007191551989655571)
            ·
              refine ⟨12001201510787327984483357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8000801007191551989655571 12001201510787327984483357)
              ·
                refine ⟨4500450566545247994181259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12001201510787327984483357 4500450566545247994181259)
                ·
                  refine ⟨6750675849817871991271889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4500450566545247994181259 6750675849817871991271889)
                  ·
                    refine ⟨5063006887363403993453917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6750675849817871991271889 5063006887363403993453917)
                    ·
                      refine ⟨1898627582761276497545219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5063006887363403993453917 1898627582761276497545219)
                      ·
                        rfl

theorem cell23_3697564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 1, 1, 3, 1, 2, 3].length) (baseStart_3697564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3697564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3697564 prefixEnd_3697564 := by exact prefixLift 3697564
  have htrace : WordTrace (prefixWord ++ tailWord_3697564) baseStart_3697564 baseEnd_3697564 := by
    simpa [prefixWord, tailWord_3697564, baseEnd_3697564] using wordTrace_append hprefix tailTrace_3697564
  have hstable : (prefixWord ++ tailWord_3697564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3697564).length < 2 ^ (prefixWord ++ tailWord_3697564).sum := by decide
  have hdescent : baseEnd_3697564 < baseStart_3697564 := by decide
  rcases family_descends (prefixWord ++ tailWord_3697564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3697583 : List Nat := [1, 1, 2, 1, 2, 2, 2, 3, 2, 3, 4]
def baseStart_3697583 : Nat := 118140960795 + 3697583 * 2 ^ 59
def prefixEnd_3697583 : Nat := 4983230072969 + 3 ^ 40 * 3697583 * 2
def baseEnd_3697583 : Nat := 1898637338893711923207631

theorem tailTrace_3697583 : CollatzResearch.WordTrace tailWord_3697583 prefixEnd_3697583 1898637338893711923207631 := by
  unfold tailWord_3697583
  simp only [CollatzResearch.WordTrace]
  refine ⟨134861931363295762745473403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89907954242197175163648935 134861931363295762745473403)
  ·
    refine ⟨202292897044943644118210105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134861931363295762745473403 202292897044943644118210105)
    ·
      refine ⟨151719672783707733088657579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 202292897044943644118210105 151719672783707733088657579)
      ·
        refine ⟨227579509175561599632986369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151719672783707733088657579 227579509175561599632986369)
        ·
          refine ⟨170684631881671199724739777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 227579509175561599632986369 170684631881671199724739777)
          ·
            refine ⟨128013473911253399793554833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 170684631881671199724739777 128013473911253399793554833)
            ·
              refine ⟨96010105433440049845166125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 128013473911253399793554833 96010105433440049845166125)
              ·
                refine ⟨36003789537540018691937297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 96010105433440049845166125 36003789537540018691937297)
                ·
                  refine ⟨27002842153155014018952973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36003789537540018691937297 27002842153155014018952973)
                  ·
                    refine ⟨10126065807433130257107365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27002842153155014018952973 10126065807433130257107365)
                    ·
                      refine ⟨1898637338893711923207631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10126065807433130257107365 1898637338893711923207631)
                      ·
                        rfl

theorem cell23_3697583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 3, 2, 3, 4].length) (baseStart_3697583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3697583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3697583 prefixEnd_3697583 := by exact prefixLift 3697583
  have htrace : WordTrace (prefixWord ++ tailWord_3697583) baseStart_3697583 baseEnd_3697583 := by
    simpa [prefixWord, tailWord_3697583, baseEnd_3697583] using wordTrace_append hprefix tailTrace_3697583
  have hstable : (prefixWord ++ tailWord_3697583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3697583).length < 2 ^ (prefixWord ++ tailWord_3697583).sum := by decide
  have hdescent : baseEnd_3697583 < baseStart_3697583 := by decide
  rcases family_descends (prefixWord ++ tailWord_3697583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3697594 : List Nat := [3, 1, 1, 1, 2, 1, 7, 1, 2, 1, 3]
def baseStart_3697594 : Nat := 118140960795 + 3697594 * 2 ^ 59
def prefixEnd_3697594 : Nat := 4983230072969 + 3 ^ 40 * 3697594 * 2
def baseEnd_3697594 : Nat := 1898642987180911380170081

theorem tailTrace_3697594 : CollatzResearch.WordTrace tailWord_3697594 prefixEnd_3697594 1898642987180911380170081 := by
  unfold tailWord_3697594
  simp only [CollatzResearch.WordTrace]
  refine ⟨33715583141563977906030959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89908221710837274416082557 33715583141563977906030959)
  ·
    refine ⟨50573374712345966859046439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33715583141563977906030959 50573374712345966859046439)
    ·
      refine ⟨75860062068518950288569659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50573374712345966859046439 75860062068518950288569659)
      ·
        refine ⟨113790093102778425432854489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75860062068518950288569659 113790093102778425432854489)
        ·
          refine ⟨85342569827083819074640867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 113790093102778425432854489 85342569827083819074640867)
          ·
            refine ⟨128013854740625728611961301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85342569827083819074640867 128013854740625728611961301)
            ·
              refine ⟨3000324720483415514342843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 128013854740625728611961301 3000324720483415514342843)
              ·
                refine ⟨4500487080725123271514265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3000324720483415514342843 4500487080725123271514265)
                ·
                  refine ⟨3375365310543842453635699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4500487080725123271514265 3375365310543842453635699)
                  ·
                    refine ⟨5063047965815763680453549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3375365310543842453635699 5063047965815763680453549)
                    ·
                      refine ⟨1898642987180911380170081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5063047965815763680453549 1898642987180911380170081)
                      ·
                        rfl

theorem cell23_3697594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 7, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 7, 1, 2, 1, 3].length) (baseStart_3697594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3697594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3697594 prefixEnd_3697594 := by exact prefixLift 3697594
  have htrace : WordTrace (prefixWord ++ tailWord_3697594) baseStart_3697594 baseEnd_3697594 := by
    simpa [prefixWord, tailWord_3697594, baseEnd_3697594] using wordTrace_append hprefix tailTrace_3697594
  have hstable : (prefixWord ++ tailWord_3697594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3697594).length < 2 ^ (prefixWord ++ tailWord_3697594).sum := by decide
  have hdescent : baseEnd_3697594 < baseStart_3697594 := by decide
  rcases family_descends (prefixWord ++ tailWord_3697594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3697603 : List Nat := [1, 1, 1, 3, 1, 1, 2, 3, 4, 1, 5]
def baseStart_3697603 : Nat := 118140960795 + 3697603 * 2 ^ 59
def prefixEnd_3697603 : Nat := 4983230072969 + 3 ^ 40 * 3697603 * 2
def baseEnd_3697603 : Nat := 1898647608506801844957539

theorem tailTrace_3697603 : CollatzResearch.WordTrace tailWord_3697603 prefixEnd_3697603 1898647608506801844957539 := by
  unfold tailWord_3697603
  simp only [CollatzResearch.WordTrace]
  refine ⟨134862660823223306161201463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89908440548815537440800975 134862660823223306161201463)
  ·
    refine ⟨202293991234834959241802195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134862660823223306161201463 202293991234834959241802195)
    ·
      refine ⟨303440986852252438862703293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 202293991234834959241802195 303440986852252438862703293)
      ·
        refine ⟨113790370069594664573513735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 303440986852252438862703293 113790370069594664573513735)
        ·
          refine ⟨170685555104391996860270603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113790370069594664573513735 170685555104391996860270603)
          ·
            refine ⟨256028332656587995290405905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 170685555104391996860270603 256028332656587995290405905)
            ·
              refine ⟨192021249492440996467804429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 256028332656587995290405905 192021249492440996467804429)
              ·
                refine ⟨72007968559665373675426661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 192021249492440996467804429 72007968559665373675426661)
                ·
                  refine ⟨13501494104937257564142499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 72007968559665373675426661 13501494104937257564142499)
                  ·
                    refine ⟨20252241157405886346213749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13501494104937257564142499 20252241157405886346213749)
                    ·
                      refine ⟨1898647608506801844957539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20252241157405886346213749 1898647608506801844957539)
                      ·
                        rfl

theorem cell23_3697603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 3, 4, 1, 5].length) (baseStart_3697603 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3697603 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3697603 prefixEnd_3697603 := by exact prefixLift 3697603
  have htrace : WordTrace (prefixWord ++ tailWord_3697603) baseStart_3697603 baseEnd_3697603 := by
    simpa [prefixWord, tailWord_3697603, baseEnd_3697603] using wordTrace_append hprefix tailTrace_3697603
  have hstable : (prefixWord ++ tailWord_3697603).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3697603).length < 2 ^ (prefixWord ++ tailWord_3697603).sum := by decide
  have hdescent : baseEnd_3697603 < baseStart_3697603 := by decide
  rcases family_descends (prefixWord ++ tailWord_3697603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3697617 : List Nat := [1, 2, 2, 1, 2, 1, 3, 1, 6, 2, 2]
def baseStart_3697617 : Nat := 118140960795 + 3697617 * 2 ^ 59
def prefixEnd_3697617 : Nat := 4983230072969 + 3 ^ 40 * 3697617 * 2
def baseEnd_3697617 : Nat := 1898654797235964790182475

theorem tailTrace_3697617 : CollatzResearch.WordTrace tailWord_3697617 prefixEnd_3697617 1898654797235964790182475 := by
  unfold tailWord_3697617
  simp only [CollatzResearch.WordTrace]
  refine ⟨134863171445172586552211105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89908780963448391034807403 134863171445172586552211105)
  ·
    refine ⟨101147378583879439914158329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134863171445172586552211105 101147378583879439914158329)
    ·
      refine ⟨75860533937909579935618747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101147378583879439914158329 75860533937909579935618747)
      ·
        refine ⟨113790800906864369903428121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75860533937909579935618747 113790800906864369903428121)
        ·
          refine ⟨85343100680148277427571091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 113790800906864369903428121 85343100680148277427571091)
          ·
            refine ⟨128014651020222416141356637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85343100680148277427571091 128014651020222416141356637)
            ·
              refine ⟨48005494132583406053008739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 128014651020222416141356637 48005494132583406053008739)
              ·
                refine ⟨72008241198875109079513109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48005494132583406053008739 72008241198875109079513109)
                ·
                  refine ⟨3375386306197270738102177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 72008241198875109079513109 3375386306197270738102177)
                  ·
                    refine ⟨2531539729647953053576633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3375386306197270738102177 2531539729647953053576633)
                    ·
                      refine ⟨1898654797235964790182475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2531539729647953053576633 1898654797235964790182475)
                      ·
                        rfl

theorem cell23_3697617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 3, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 3, 1, 6, 2, 2].length) (baseStart_3697617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3697617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3697617 prefixEnd_3697617 := by exact prefixLift 3697617
  have htrace : WordTrace (prefixWord ++ tailWord_3697617) baseStart_3697617 baseEnd_3697617 := by
    simpa [prefixWord, tailWord_3697617, baseEnd_3697617] using wordTrace_append hprefix tailTrace_3697617
  have hstable : (prefixWord ++ tailWord_3697617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3697617).length < 2 ^ (prefixWord ++ tailWord_3697617).sum := by decide
  have hdescent : baseEnd_3697617 < baseStart_3697617 := by decide
  rcases family_descends (prefixWord ++ tailWord_3697617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3697620 : List Nat := [2, 4, 1, 2, 1, 2, 1, 1, 1, 3, 5]
def baseStart_3697620 : Nat := 118140960795 + 3697620 * 2 ^ 59
def prefixEnd_3697620 : Nat := 4983230072969 + 3 ^ 40 * 3697620 * 2
def baseEnd_3697620 : Nat := 1898656337677928278444961

theorem tailTrace_3697620 : CollatzResearch.WordTrace tailWord_3697620 prefixEnd_3697620 1898656337677928278444961 := by
  unfold tailWord_3697620
  simp only [CollatzResearch.WordTrace]
  refine ⟨67431640432080859032285157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89908853909441145376380209 67431640432080859032285157)
  ·
    refine ⟨12643432581015161068553467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 67431640432080859032285157 12643432581015161068553467)
    ·
      refine ⟨18965148871522741602830201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12643432581015161068553467 18965148871522741602830201)
      ·
        refine ⟨14223861653642056202122651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18965148871522741602830201 14223861653642056202122651)
        ·
          refine ⟨21335792480463084303183977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14223861653642056202122651 21335792480463084303183977)
          ·
            refine ⟨16001844360347313227387983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21335792480463084303183977 16001844360347313227387983)
            ·
              refine ⟨24002766540520969841081975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16001844360347313227387983 24002766540520969841081975)
              ·
                refine ⟨36004149810781454761622963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24002766540520969841081975 36004149810781454761622963)
                ·
                  refine ⟨54006224716172182142434445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36004149810781454761622963 54006224716172182142434445)
                  ·
                    refine ⟨20252334268564568303412917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 54006224716172182142434445 20252334268564568303412917)
                    ·
                      refine ⟨1898656337677928278444961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20252334268564568303412917 1898656337677928278444961)
                      ·
                        rfl

theorem cell23_3697620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 1, 1, 1, 3, 5].length) (baseStart_3697620 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3697620 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3697620 prefixEnd_3697620 := by exact prefixLift 3697620
  have htrace : WordTrace (prefixWord ++ tailWord_3697620) baseStart_3697620 baseEnd_3697620 := by
    simpa [prefixWord, tailWord_3697620, baseEnd_3697620] using wordTrace_append hprefix tailTrace_3697620
  have hstable : (prefixWord ++ tailWord_3697620).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3697620).length < 2 ^ (prefixWord ++ tailWord_3697620).sum := by decide
  have hdescent : baseEnd_3697620 < baseStart_3697620 := by decide
  rcases family_descends (prefixWord ++ tailWord_3697620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3697633 : List Nat := [1, 2, 3, 1, 2, 1, 1, 1, 1, 1, 9]
def baseStart_3697633 : Nat := 118140960795 + 3697633 * 2 ^ 59
def prefixEnd_3697633 : Nat := 4983230072969 + 3 ^ 40 * 3697633 * 2
def baseEnd_3697633 : Nat := 1898663012926436727582401

theorem tailTrace_3697633 : CollatzResearch.WordTrace tailWord_3697633 prefixEnd_3697633 1898663012926436727582401 := by
  unfold tailWord_3697633
  simp only [CollatzResearch.WordTrace]
  refine ⟨134863755013114621284793553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89909170008743080856529035 134863755013114621284793553)
  ·
    refine ⟨101147816259835965963595165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134863755013114621284793553 101147816259835965963595165)
    ·
      refine ⟨37930431097438487236348187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 101147816259835965963595165 37930431097438487236348187)
      ·
        refine ⟨56895646646157730854522281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37930431097438487236348187 56895646646157730854522281)
        ·
          refine ⟨42671734984618298140891711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56895646646157730854522281 42671734984618298140891711)
          ·
            refine ⟨64007602476927447211337567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42671734984618298140891711 64007602476927447211337567)
            ·
              refine ⟨96011403715391170817006351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64007602476927447211337567 96011403715391170817006351)
              ·
                refine ⟨144017105573086756225509527, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 96011403715391170817006351 144017105573086756225509527)
                ·
                  refine ⟨216025658359630134338264291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 144017105573086756225509527 216025658359630134338264291)
                  ·
                    refine ⟨324038487539445201507396437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 216025658359630134338264291 324038487539445201507396437)
                    ·
                      refine ⟨1898663012926436727582401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 324038487539445201507396437 1898663012926436727582401)
                      ·
                        rfl

theorem cell23_3697633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 1, 1, 1, 9].length) (baseStart_3697633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3697633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3697633 prefixEnd_3697633 := by exact prefixLift 3697633
  have htrace : WordTrace (prefixWord ++ tailWord_3697633) baseStart_3697633 baseEnd_3697633 := by
    simpa [prefixWord, tailWord_3697633, baseEnd_3697633] using wordTrace_append hprefix tailTrace_3697633
  have hstable : (prefixWord ++ tailWord_3697633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3697633).length < 2 ^ (prefixWord ++ tailWord_3697633).sum := by decide
  have hdescent : baseEnd_3697633 < baseStart_3697633 := by decide
  rcases family_descends (prefixWord ++ tailWord_3697633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3697640 : List Nat := [2, 1, 4, 1, 1, 1, 5, 1, 7]
def baseStart_3697640 : Nat := 118140960795 + 3697640 * 2 ^ 59
def prefixEnd_3697640 : Nat := 4983230072969 + 3 ^ 40 * 3697640 * 2
def baseEnd_3697640 : Nat := 210962956365668688910541

theorem tailTrace_3697640 : CollatzResearch.WordTrace tailWord_3697640 prefixEnd_3697640 210962956365668688910541 := by
  unfold tailWord_3697640
  simp only [CollatzResearch.WordTrace]
  refine ⟨67432005162044630740149187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89909340216059507653532249 67432005162044630740149187)
  ·
    refine ⟨101148007743066946110223781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67432005162044630740149187 101148007743066946110223781)
    ·
      refine ⟨18965251451825052395666959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 101148007743066946110223781 18965251451825052395666959)
      ·
        refine ⟨28447877177737578593500439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18965251451825052395666959 28447877177737578593500439)
        ·
          refine ⟨42671815766606367890250659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28447877177737578593500439 42671815766606367890250659)
          ·
            refine ⟨64007723649909551835375989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42671815766606367890250659 64007723649909551835375989)
            ·
              refine ⟨6000724092179020484566499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 64007723649909551835375989 6000724092179020484566499)
              ·
                refine ⟨9001086138268530726849749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6000724092179020484566499 9001086138268530726849749)
                ·
                  refine ⟨210962956365668688910541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9001086138268530726849749 210962956365668688910541)
                  ·
                    rfl

theorem cell23_3697640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 5, 1, 7].length) (baseStart_3697640 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3697640 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3697640 prefixEnd_3697640 := by exact prefixLift 3697640
  have htrace : WordTrace (prefixWord ++ tailWord_3697640) baseStart_3697640 baseEnd_3697640 := by
    simpa [prefixWord, tailWord_3697640, baseEnd_3697640] using wordTrace_append hprefix tailTrace_3697640
  have hstable : (prefixWord ++ tailWord_3697640).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3697640).length < 2 ^ (prefixWord ++ tailWord_3697640).sum := by decide
  have hdescent : baseEnd_3697640 < baseStart_3697640 := by decide
  rcases family_descends (prefixWord ++ tailWord_3697640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3697687 : List Nat := [1, 1, 3, 5, 1, 1, 2, 2, 2, 5]
def baseStart_3697687 : Nat := 118140960795 + 3697687 * 2 ^ 59
def prefixEnd_3697687 : Nat := 4983230072969 + 3 ^ 40 * 3697687 * 2
def baseEnd_3697687 : Nat := 632896913627259838769051

theorem tailTrace_3697687 : CollatzResearch.WordTrace tailWord_3697687 prefixEnd_3697687 632896913627259838769051 := by
  unfold tailWord_3697687
  simp only [CollatzResearch.WordTrace]
  refine ⟨134865724554918988507259315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89910483036612659004839543 134865724554918988507259315)
  ·
    refine ⟨202298586832378482760888973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134865724554918988507259315 202298586832378482760888973)
    ·
      refine ⟨75861970062141931035333365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 202298586832378482760888973 75861970062141931035333365)
      ·
        refine ⟨7112059693325806034562503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 75861970062141931035333365 7112059693325806034562503)
        ·
          refine ⟨10668089539988709051843755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7112059693325806034562503 10668089539988709051843755)
          ·
            refine ⟨16002134309983063577765633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10668089539988709051843755 16002134309983063577765633)
            ·
              refine ⟨12001600732487297683324225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16002134309983063577765633 12001600732487297683324225)
              ·
                refine ⟨9001200549365473262493169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12001600732487297683324225 9001200549365473262493169)
                ·
                  refine ⟨6750900412024104946869877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9001200549365473262493169 6750900412024104946869877)
                  ·
                    refine ⟨632896913627259838769051, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6750900412024104946869877 632896913627259838769051)
                    ·
                      rfl

theorem cell23_3697687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 2, 2, 2, 5].length) (baseStart_3697687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3697687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3697687 prefixEnd_3697687 := by exact prefixLift 3697687
  have htrace : WordTrace (prefixWord ++ tailWord_3697687) baseStart_3697687 baseEnd_3697687 := by
    simpa [prefixWord, tailWord_3697687, baseEnd_3697687] using wordTrace_append hprefix tailTrace_3697687
  have hstable : (prefixWord ++ tailWord_3697687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3697687).length < 2 ^ (prefixWord ++ tailWord_3697687).sum := by decide
  have hdescent : baseEnd_3697687 < baseStart_3697687 := by decide
  rcases family_descends (prefixWord ++ tailWord_3697687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3697707 : List Nat := [1, 1, 1, 1, 2, 1, 7, 1, 2, 4, 2]
def baseStart_3697707 : Nat := 118140960795 + 3697707 * 2 ^ 59
def prefixEnd_3697707 : Nat := 4983230072969 + 3 ^ 40 * 3697707 * 2
def baseEnd_3697707 : Nat := 1898701010494869438057061

theorem tailTrace_3697707 : CollatzResearch.WordTrace tailWord_3697707 prefixEnd_3697707 1898701010494869438057061 := by
  unfold tailWord_3697707
  simp only [CollatzResearch.WordTrace]
  refine ⟨134866454014846531922987375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89910969343231021281991583 134866454014846531922987375)
  ·
    refine ⟨202299681022269797884481063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134866454014846531922987375 202299681022269797884481063)
    ·
      refine ⟨303449521533404696826721595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 202299681022269797884481063 303449521533404696826721595)
      ·
        refine ⟨455174282300107045240082393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 303449521533404696826721595 455174282300107045240082393)
        ·
          refine ⟨341380711725080283930061795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 455174282300107045240082393 341380711725080283930061795)
          ·
            refine ⟨512071067587620425895092693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 341380711725080283930061795 512071067587620425895092693)
            ·
              refine ⟨12001665646584853731916235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 512071067587620425895092693 12001665646584853731916235)
              ·
                refine ⟨18002498469877280597874353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12001665646584853731916235 18002498469877280597874353)
                ·
                  refine ⟨13501873852407960448405765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18002498469877280597874353 13501873852407960448405765)
                  ·
                    refine ⟨2531601347326492584076081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13501873852407960448405765 2531601347326492584076081)
                    ·
                      refine ⟨1898701010494869438057061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2531601347326492584076081 1898701010494869438057061)
                      ·
                        rfl

theorem cell23_3697707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 7, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 7, 1, 2, 4, 2].length) (baseStart_3697707 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3697707 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3697707 prefixEnd_3697707 := by exact prefixLift 3697707
  have htrace : WordTrace (prefixWord ++ tailWord_3697707) baseStart_3697707 baseEnd_3697707 := by
    simpa [prefixWord, tailWord_3697707, baseEnd_3697707] using wordTrace_append hprefix tailTrace_3697707
  have hstable : (prefixWord ++ tailWord_3697707).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3697707).length < 2 ^ (prefixWord ++ tailWord_3697707).sum := by decide
  have hdescent : baseEnd_3697707 < baseStart_3697707 := by decide
  rcases family_descends (prefixWord ++ tailWord_3697707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3697724 : List Nat := [2, 2, 2, 2, 2, 4, 1, 1, 2, 1, 4]
def baseStart_3697724 : Nat := 118140960795 + 3697724 * 2 ^ 59
def prefixEnd_3697724 : Nat := 4983230072969 + 3 ^ 40 * 3697724 * 2
def baseEnd_3697724 : Nat := 1898709739665995871544483

theorem tailTrace_3697724 : CollatzResearch.WordTrace tailWord_3697724 prefixEnd_3697724 1898709739665995871544483 := by
  unfold tailWord_3697724
  simp only [CollatzResearch.WordTrace]
  refine ⟨67433537027892471913178113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89911382703856629217570817 67433537027892471913178113)
  ·
    refine ⟨50575152770919353934883585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67433537027892471913178113 50575152770919353934883585)
    ·
      refine ⟨37931364578189515451162689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50575152770919353934883585 37931364578189515451162689)
      ·
        refine ⟨28448523433642136588372017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37931364578189515451162689 28448523433642136588372017)
        ·
          refine ⟨21336392575231602441279013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28448523433642136588372017 21336392575231602441279013)
          ·
            refine ⟨4000573607855925457739815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21336392575231602441279013 4000573607855925457739815)
            ·
              refine ⟨6000860411783888186609723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4000573607855925457739815 6000860411783888186609723)
              ·
                refine ⟨9001290617675832279914585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6000860411783888186609723 9001290617675832279914585)
                ·
                  refine ⟨6750967963256874209935939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9001290617675832279914585 6750967963256874209935939)
                  ·
                    refine ⟨10126451944885311314903909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6750967963256874209935939 10126451944885311314903909)
                    ·
                      refine ⟨1898709739665995871544483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10126451944885311314903909 1898709739665995871544483)
                      ·
                        rfl

theorem cell23_3697724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 4, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 4, 1, 1, 2, 1, 4].length) (baseStart_3697724 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3697724 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3697724 prefixEnd_3697724 := by exact prefixLift 3697724
  have htrace : WordTrace (prefixWord ++ tailWord_3697724) baseStart_3697724 baseEnd_3697724 := by
    simpa [prefixWord, tailWord_3697724, baseEnd_3697724] using wordTrace_append hprefix tailTrace_3697724
  have hstable : (prefixWord ++ tailWord_3697724).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3697724).length < 2 ^ (prefixWord ++ tailWord_3697724).sum := by decide
  have hdescent : baseEnd_3697724 < baseStart_3697724 := by decide
  rcases family_descends (prefixWord ++ tailWord_3697724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3697758 : List Nat := [4, 4, 1, 1, 1, 1, 2, 1, 2, 4, 2]
def baseStart_3697758 : Nat := 118140960795 + 3697758 * 2 ^ 59
def prefixEnd_3697758 : Nat := 4983230072969 + 3 ^ 40 * 3697758 * 2
def baseEnd_3697758 : Nat := 1898727198008248738519327

theorem tailTrace_3697758 : CollatzResearch.WordTrace tailWord_3697758 prefixEnd_3697758 1898727198008248738519327 := by
  unfold tailWord_3697758
  simp only [CollatzResearch.WordTrace]
  refine ⟨16858539267207720954136741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 89912209425107845088729285 16858539267207720954136741)
  ·
    refine ⟨3160976112601447678900639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16858539267207720954136741 3160976112601447678900639)
    ·
      refine ⟨4741464168902171518350959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3160976112601447678900639 4741464168902171518350959)
      ·
        refine ⟨7112196253353257277526439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4741464168902171518350959 7112196253353257277526439)
        ·
          refine ⟨10668294380029885916289659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7112196253353257277526439 10668294380029885916289659)
          ·
            refine ⟨16002441570044828874434489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10668294380029885916289659 16002441570044828874434489)
            ·
              refine ⟨12001831177533621655825867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16002441570044828874434489 12001831177533621655825867)
              ·
                refine ⟨18002746766300432483738801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12001831177533621655825867 18002746766300432483738801)
                ·
                  refine ⟨13502060074725324362804101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18002746766300432483738801 13502060074725324362804101)
                  ·
                    refine ⟨2531636264010998318025769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13502060074725324362804101 2531636264010998318025769)
                    ·
                      refine ⟨1898727198008248738519327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2531636264010998318025769 1898727198008248738519327)
                      ·
                        rfl

theorem cell23_3697758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 2, 1, 2, 4, 2].length) (baseStart_3697758 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3697758 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3697758 prefixEnd_3697758 := by exact prefixLift 3697758
  have htrace : WordTrace (prefixWord ++ tailWord_3697758) baseStart_3697758 baseEnd_3697758 := by
    simpa [prefixWord, tailWord_3697758, baseEnd_3697758] using wordTrace_append hprefix tailTrace_3697758
  have hstable : (prefixWord ++ tailWord_3697758).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3697758).length < 2 ^ (prefixWord ++ tailWord_3697758).sum := by decide
  have hdescent : baseEnd_3697758 < baseStart_3697758 := by decide
  rcases family_descends (prefixWord ++ tailWord_3697758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3697824 : List Nat := [2, 1, 1, 4, 2, 1, 3, 3, 2, 4]
def baseStart_3697824 : Nat := 118140960795 + 3697824 * 2 ^ 59
def prefixEnd_3697824 : Nat := 4983230072969 + 3 ^ 40 * 3697824 * 2
def baseEnd_3697824 : Nat := 632920362577148493431341

theorem tailTrace_3697824 : CollatzResearch.WordTrace tailWord_3697824 prefixEnd_3697824 632920362577148493431341 := by
  unfold tailWord_3697824
  simp only [CollatzResearch.WordTrace]
  refine ⟨67435360677711330452498263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89913814236948440603331017 67435360677711330452498263)
  ·
    refine ⟨101153041016566995678747395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67435360677711330452498263 101153041016566995678747395)
    ·
      refine ⟨151729561524850493518121093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101153041016566995678747395 151729561524850493518121093)
      ·
        refine ⟨28449292785909467534647705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 151729561524850493518121093 28449292785909467534647705)
        ·
          refine ⟨21336969589432100650985779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28449292785909467534647705 21336969589432100650985779)
          ·
            refine ⟨32005454384148150976478669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21336969589432100650985779 32005454384148150976478669)
            ·
              refine ⟨12002045394055556616179501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32005454384148150976478669 12002045394055556616179501)
              ·
                refine ⟨4500767022770833731067313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12002045394055556616179501 4500767022770833731067313)
                ·
                  refine ⟨3375575267078125298300485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4500767022770833731067313 3375575267078125298300485)
                  ·
                    refine ⟨632920362577148493431341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3375575267078125298300485 632920362577148493431341)
                    ·
                      rfl

theorem cell23_3697824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 3, 3, 2, 4].length) (baseStart_3697824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3697824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3697824 prefixEnd_3697824 := by exact prefixLift 3697824
  have htrace : WordTrace (prefixWord ++ tailWord_3697824) baseStart_3697824 baseEnd_3697824 := by
    simpa [prefixWord, tailWord_3697824, baseEnd_3697824] using wordTrace_append hprefix tailTrace_3697824
  have hstable : (prefixWord ++ tailWord_3697824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3697824).length < 2 ^ (prefixWord ++ tailWord_3697824).sum := by decide
  have hdescent : baseEnd_3697824 < baseStart_3697824 := by decide
  rcases family_descends (prefixWord ++ tailWord_3697824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3697831 : List Nat := [1, 1, 6, 2, 1, 1, 3, 2, 1, 1, 4]
def baseStart_3697831 : Nat := 118140960795 + 3697831 * 2 ^ 59
def prefixEnd_3697831 : Nat := 4983230072969 + 3 ^ 40 * 3697831 * 2
def baseEnd_3697831 : Nat := 1898764682096026952906491

theorem tailTrace_3697831 : CollatzResearch.WordTrace tailWord_3697831 prefixEnd_3697831 1898764682096026952906491 := by
  unfold tailWord_3697831
  simp only [CollatzResearch.WordTrace]
  refine ⟨134870976666397301100501347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89913984444264867400334231 134870976666397301100501347)
  ·
    refine ⟨202306464999595951650752021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134870976666397301100501347 202306464999595951650752021)
    ·
      refine ⟨9483115546856060233629001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 202306464999595951650752021 9483115546856060233629001)
      ·
        refine ⟨7112336660142045175221751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9483115546856060233629001 7112336660142045175221751)
        ·
          refine ⟨10668504990213067762832627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7112336660142045175221751 10668504990213067762832627)
          ·
            refine ⟨16002757485319601644248941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10668504990213067762832627 16002757485319601644248941)
            ·
              refine ⟨6001034056994850616593353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16002757485319601644248941 6001034056994850616593353)
              ·
                refine ⟨4500775542746137962445015, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6001034056994850616593353 4500775542746137962445015)
                ·
                  refine ⟨6751163314119206943667523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4500775542746137962445015 6751163314119206943667523)
                  ·
                    refine ⟨10126744971178810415501285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6751163314119206943667523 10126744971178810415501285)
                    ·
                      refine ⟨1898764682096026952906491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10126744971178810415501285 1898764682096026952906491)
                      ·
                        rfl

theorem cell23_3697831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 3, 2, 1, 1, 4].length) (baseStart_3697831 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3697831 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3697831 prefixEnd_3697831 := by exact prefixLift 3697831
  have htrace : WordTrace (prefixWord ++ tailWord_3697831) baseStart_3697831 baseEnd_3697831 := by
    simpa [prefixWord, tailWord_3697831, baseEnd_3697831] using wordTrace_append hprefix tailTrace_3697831
  have hstable : (prefixWord ++ tailWord_3697831).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3697831).length < 2 ^ (prefixWord ++ tailWord_3697831).sum := by decide
  have hdescent : baseEnd_3697831 < baseStart_3697831 := by decide
  rcases family_descends (prefixWord ++ tailWord_3697831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3697840 : List Nat := [2, 1, 1, 1, 2, 1, 2, 2, 1, 4, 6]
def baseStart_3697840 : Nat := 118140960795 + 3697840 * 2 ^ 59
def prefixEnd_3697840 : Nat := 4983230072969 + 3 ^ 40 * 3697840 * 2
def baseEnd_3697840 : Nat := 1898769303421917417693949

theorem tailTrace_3697840 : CollatzResearch.WordTrace tailWord_3697840 prefixEnd_3697840 1898769303421917417693949 := by
  unfold tailWord_3697840
  simp only [CollatzResearch.WordTrace]
  refine ⟨67435652461682347818789487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89914203282243130425052649 67435652461682347818789487)
  ·
    refine ⟨101153478692523521728184231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67435652461682347818789487 101153478692523521728184231)
    ·
      refine ⟨151730218038785282592276347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101153478692523521728184231 151730218038785282592276347)
      ·
        refine ⟨227595327058177923888414521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151730218038785282592276347 227595327058177923888414521)
        ·
          refine ⟨170696495293633442916310891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 227595327058177923888414521 170696495293633442916310891)
          ·
            refine ⟨256044742940450164374466337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 170696495293633442916310891 256044742940450164374466337)
            ·
              refine ⟨192033557205337623280849753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 256044742940450164374466337 192033557205337623280849753)
              ·
                refine ⟨144025167904003217460637315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 192033557205337623280849753 144025167904003217460637315)
                ·
                  refine ⟨216037751856004826190955973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 144025167904003217460637315 216037751856004826190955973)
                  ·
                    refine ⟨40507078473000904910804245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 216037751856004826190955973 40507078473000904910804245)
                    ·
                      refine ⟨1898769303421917417693949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 40507078473000904910804245 1898769303421917417693949)
                      ·
                        rfl

theorem cell23_3697840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 2, 1, 4, 6].length) (baseStart_3697840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3697840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3697840 prefixEnd_3697840 := by exact prefixLift 3697840
  have htrace : WordTrace (prefixWord ++ tailWord_3697840) baseStart_3697840 baseEnd_3697840 := by
    simpa [prefixWord, tailWord_3697840, baseEnd_3697840] using wordTrace_append hprefix tailTrace_3697840
  have hstable : (prefixWord ++ tailWord_3697840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3697840).length < 2 ^ (prefixWord ++ tailWord_3697840).sum := by decide
  have hdescent : baseEnd_3697840 < baseStart_3697840 := by decide
  rcases family_descends (prefixWord ++ tailWord_3697840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3697864 : List Nat := [2, 1, 3, 1, 2, 1, 2, 3, 4, 1, 3]
def baseStart_3697864 : Nat := 118140960795 + 3697864 * 2 ^ 59
def prefixEnd_3697864 : Nat := 4983230072969 + 3 ^ 40 * 3697864 * 2
def baseEnd_3697864 : Nat := 1898781626957625323793839

theorem tailTrace_3697864 : CollatzResearch.WordTrace tailWord_3697864 prefixEnd_3697864 1898781626957625323793839 := by
  unfold tailWord_3697864
  simp only [CollatzResearch.WordTrace]
  refine ⟨67436090137638873868226323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89914786850185165157635097 67436090137638873868226323)
  ·
    refine ⟨101154135206458310802339485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67436090137638873868226323 101154135206458310802339485)
    ·
      refine ⟨37932800702421866550877307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 101154135206458310802339485 37932800702421866550877307)
      ·
        refine ⟨56899201053632799826315961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37932800702421866550877307 56899201053632799826315961)
        ·
          refine ⟨42674400790224599869736971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56899201053632799826315961 42674400790224599869736971)
          ·
            refine ⟨64011601185336899804605457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42674400790224599869736971 64011601185336899804605457)
            ·
              refine ⟨48008700889002674853454093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64011601185336899804605457 48008700889002674853454093)
              ·
                refine ⟨18003262833376003070045285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48008700889002674853454093 18003262833376003070045285)
                ·
                  refine ⟨3375611781258000575633491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18003262833376003070045285 3375611781258000575633491)
                  ·
                    refine ⟨5063417671887000863450237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3375611781258000575633491 5063417671887000863450237)
                    ·
                      refine ⟨1898781626957625323793839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5063417671887000863450237 1898781626957625323793839)
                      ·
                        rfl

theorem cell23_3697864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 2, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 2, 3, 4, 1, 3].length) (baseStart_3697864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3697864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3697864 prefixEnd_3697864 := by exact prefixLift 3697864
  have htrace : WordTrace (prefixWord ++ tailWord_3697864) baseStart_3697864 baseEnd_3697864 := by
    simpa [prefixWord, tailWord_3697864, baseEnd_3697864] using wordTrace_append hprefix tailTrace_3697864
  have hstable : (prefixWord ++ tailWord_3697864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3697864).length < 2 ^ (prefixWord ++ tailWord_3697864).sum := by decide
  have hdescent : baseEnd_3697864 < baseStart_3697864 := by decide
  rcases family_descends (prefixWord ++ tailWord_3697864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3697878 : List Nat := [5, 2, 1, 2, 2, 1, 2, 1, 1, 2, 4]
def baseStart_3697878 : Nat := 118140960795 + 3697878 * 2 ^ 59
def prefixEnd_3697878 : Nat := 4983230072969 + 3 ^ 40 * 3697878 * 2
def baseEnd_3697878 : Nat := 1898788815686788269018775

theorem tailTrace_3697878 : CollatzResearch.WordTrace tailWord_3697878 prefixEnd_3697878 1898788815686788269018775 := by
  unfold tailWord_3697878
  simp only [CollatzResearch.WordTrace]
  refine ⟨8429543181076689257966393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 89915127264818018751641525 8429543181076689257966393)
  ·
    refine ⟨6322157385807516943474795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8429543181076689257966393 6322157385807516943474795)
    ·
      refine ⟨9483236078711275415212193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6322157385807516943474795 9483236078711275415212193)
      ·
        refine ⟨7112427059033456561409145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9483236078711275415212193 7112427059033456561409145)
        ·
          refine ⟨5334320294275092421056859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7112427059033456561409145 5334320294275092421056859)
          ·
            refine ⟨8001480441412638631585289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5334320294275092421056859 8001480441412638631585289)
            ·
              refine ⟨6001110331059478973688967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8001480441412638631585289 6001110331059478973688967)
              ·
                refine ⟨9001665496589218460533451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6001110331059478973688967 9001665496589218460533451)
                ·
                  refine ⟨13502498244883827690800177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9001665496589218460533451 13502498244883827690800177)
                  ·
                    refine ⟨10126873683662870768100133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13502498244883827690800177 10126873683662870768100133)
                    ·
                      refine ⟨1898788815686788269018775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10126873683662870768100133 1898788815686788269018775)
                      ·
                        rfl

theorem cell23_3697878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 1, 2, 1, 1, 2, 4].length) (baseStart_3697878 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3697878 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3697878 prefixEnd_3697878 := by exact prefixLift 3697878
  have htrace : WordTrace (prefixWord ++ tailWord_3697878) baseStart_3697878 baseEnd_3697878 := by
    simpa [prefixWord, tailWord_3697878, baseEnd_3697878] using wordTrace_append hprefix tailTrace_3697878
  have hstable : (prefixWord ++ tailWord_3697878).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3697878).length < 2 ^ (prefixWord ++ tailWord_3697878).sum := by decide
  have hdescent : baseEnd_3697878 < baseStart_3697878 := by decide
  rcases family_descends (prefixWord ++ tailWord_3697878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3697934 : List Nat := [4, 1, 1, 2, 1, 3, 2, 1, 2, 2, 4]
def baseStart_3697934 : Nat := 118140960795 + 3697934 * 2 ^ 59
def prefixEnd_3697934 : Nat := 4983230072969 + 3 ^ 40 * 3697934 * 2
def baseEnd_3697934 : Nat := 1898817570603440049918517

theorem tailTrace_3697934 : CollatzResearch.WordTrace tailWord_3697934 prefixEnd_3697934 1898817570603440049918517 := by
  unfold tailWord_3697934
  simp only [CollatzResearch.WordTrace]
  refine ⟨16859341673128018711437607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 89916488923349433127667237 16859341673128018711437607)
  ·
    refine ⟨25289012509692028067156411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16859341673128018711437607 25289012509692028067156411)
    ·
      refine ⟨37933518764538042100734617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25289012509692028067156411 37933518764538042100734617)
      ·
        refine ⟨28450139073403531575550963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37933518764538042100734617 28450139073403531575550963)
        ·
          refine ⟨42675208610105297363326445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28450139073403531575550963 42675208610105297363326445)
          ·
            refine ⟨16003203228789486511247417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42675208610105297363326445 16003203228789486511247417)
            ·
              refine ⟨12002402421592114883435563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16003203228789486511247417 12002402421592114883435563)
              ·
                refine ⟨18003603632388172325153345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12002402421592114883435563 18003603632388172325153345)
                ·
                  refine ⟨13502702724291129243865009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18003603632388172325153345 13502702724291129243865009)
                  ·
                    refine ⟨10127027043218346932898757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13502702724291129243865009 10127027043218346932898757)
                    ·
                      refine ⟨1898817570603440049918517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10127027043218346932898757 1898817570603440049918517)
                      ·
                        rfl

theorem cell23_3697934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 2, 1, 2, 2, 4].length) (baseStart_3697934 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3697934 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3697934 prefixEnd_3697934 := by exact prefixLift 3697934
  have htrace : WordTrace (prefixWord ++ tailWord_3697934) baseStart_3697934 baseEnd_3697934 := by
    simpa [prefixWord, tailWord_3697934, baseEnd_3697934] using wordTrace_append hprefix tailTrace_3697934
  have hstable : (prefixWord ++ tailWord_3697934).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3697934).length < 2 ^ (prefixWord ++ tailWord_3697934).sum := by decide
  have hdescent : baseEnd_3697934 < baseStart_3697934 := by decide
  rcases family_descends (prefixWord ++ tailWord_3697934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3697964 : List Nat := [2, 2, 1, 1, 1, 3, 1, 2, 1, 7, 2]
def baseStart_3697964 : Nat := 118140960795 + 3697964 * 2 ^ 59
def prefixEnd_3697964 : Nat := 4983230072969 + 3 ^ 40 * 3697964 * 2
def baseEnd_3697964 : Nat := 1898832975023074932543379

theorem tailTrace_3697964 : CollatzResearch.WordTrace tailWord_3697964 prefixEnd_3697964 1898832975023074932543379 := by
  unfold tailWord_3697964
  simp only [CollatzResearch.WordTrace]
  refine ⟨67437913787457732407546473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89917218383276976543395297 67437913787457732407546473)
  ·
    refine ⟨50578435340593299305659855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67437913787457732407546473 50578435340593299305659855)
    ·
      refine ⟨75867653010889948958489783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50578435340593299305659855 75867653010889948958489783)
      ·
        refine ⟨113801479516334923437734675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75867653010889948958489783 113801479516334923437734675)
        ·
          refine ⟨170702219274502385156602013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113801479516334923437734675 170702219274502385156602013)
          ·
            refine ⟨64013332227938394433725755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 170702219274502385156602013 64013332227938394433725755)
            ·
              refine ⟨96019998341907591650588633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64013332227938394433725755 96019998341907591650588633)
              ·
                refine ⟨72014998756430693737941475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 96019998341907591650588633 72014998756430693737941475)
                ·
                  refine ⟨108022498134646040606912213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 72014998756430693737941475 108022498134646040606912213)
                  ·
                    refine ⟨2531777300030766576724505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 108022498134646040606912213 2531777300030766576724505)
                    ·
                      refine ⟨1898832975023074932543379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2531777300030766576724505 1898832975023074932543379)
                      ·
                        rfl

theorem cell23_3697964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 7, 2].length) (baseStart_3697964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3697964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3697964 prefixEnd_3697964 := by exact prefixLift 3697964
  have htrace : WordTrace (prefixWord ++ tailWord_3697964) baseStart_3697964 baseEnd_3697964 := by
    simpa [prefixWord, tailWord_3697964, baseEnd_3697964] using wordTrace_append hprefix tailTrace_3697964
  have hstable : (prefixWord ++ tailWord_3697964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3697964).length < 2 ^ (prefixWord ++ tailWord_3697964).sum := by decide
  have hdescent : baseEnd_3697964 < baseStart_3697964 := by decide
  rcases family_descends (prefixWord ++ tailWord_3697964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3697967 : List Nat := [1, 1, 2, 1, 2, 1, 3, 4, 1, 2, 5]
def baseStart_3697967 : Nat := 118140960795 + 3697967 * 2 ^ 59
def prefixEnd_3697967 : Nat := 4983230072969 + 3 ^ 40 * 3697967 * 2
def baseEnd_3697967 : Nat := 1898834515465038420805865

theorem tailTrace_3697967 : CollatzResearch.WordTrace tailWord_3697967 prefixEnd_3697967 1898834515465038420805865 := by
  unfold tailWord_3697967
  simp only [CollatzResearch.WordTrace]
  refine ⟨134875936993904596327452155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89917291329269730884968103 134875936993904596327452155)
  ·
    refine ⟨202313905490856894491178233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134875936993904596327452155 202313905490856894491178233)
    ·
      refine ⟨151735429118142670868383675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 202313905490856894491178233 151735429118142670868383675)
      ·
        refine ⟨227603143677214006302575513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151735429118142670868383675 227603143677214006302575513)
        ·
          refine ⟨170702357757910504726931635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 227603143677214006302575513 170702357757910504726931635)
          ·
            refine ⟨256053536636865757090397453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 170702357757910504726931635 256053536636865757090397453)
            ·
              refine ⟨96020076238824658908899045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 256053536636865757090397453 96020076238824658908899045)
              ·
                refine ⟨18003764294779623545418571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 96020076238824658908899045 18003764294779623545418571)
                ·
                  refine ⟨27005646442169435318127857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18003764294779623545418571 27005646442169435318127857)
                  ·
                    refine ⟨20254234831627076488595893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27005646442169435318127857 20254234831627076488595893)
                    ·
                      refine ⟨1898834515465038420805865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20254234831627076488595893 1898834515465038420805865)
                      ·
                        rfl

theorem cell23_3697967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 4, 1, 2, 5].length) (baseStart_3697967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3697967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3697967 prefixEnd_3697967 := by exact prefixLift 3697967
  have htrace : WordTrace (prefixWord ++ tailWord_3697967) baseStart_3697967 baseEnd_3697967 := by
    simpa [prefixWord, tailWord_3697967, baseEnd_3697967] using wordTrace_append hprefix tailTrace_3697967
  have hstable : (prefixWord ++ tailWord_3697967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3697967).length < 2 ^ (prefixWord ++ tailWord_3697967).sum := by decide
  have hdescent : baseEnd_3697967 < baseStart_3697967 := by decide
  rcases family_descends (prefixWord ++ tailWord_3697967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3698017 : List Nat := [1, 2, 3, 1, 1, 1, 1, 3, 10]
def baseStart_3698017 : Nat := 118140960795 + 3698017 * 2 ^ 59
def prefixEnd_3698017 : Nat := 4983230072969 + 3 ^ 40 * 3698017 * 2
def baseEnd_3698017 : Nat := 210984465499751469464515

theorem tailTrace_3698017 : CollatzResearch.WordTrace tailWord_3698017 prefixEnd_3698017 210984465499751469464515 := by
  unfold tailWord_3698017
  simp only [CollatzResearch.WordTrace]
  refine ⟨134877760643723454866772305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89918507095815636577848203 134877760643723454866772305)
  ·
    refine ⟨101158320482792591150079229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134877760643723454866772305 101158320482792591150079229)
    ·
      refine ⟨37934370181047221681279711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 101158320482792591150079229 37934370181047221681279711)
      ·
        refine ⟨56901555271570832521919567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37934370181047221681279711 56901555271570832521919567)
        ·
          refine ⟨85352332907356248782879351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56901555271570832521919567 85352332907356248782879351)
          ·
            refine ⟨128028499361034373174319027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85352332907356248782879351 128028499361034373174319027)
            ·
              refine ⟨192042749041551559761478541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 128028499361034373174319027 192042749041551559761478541)
              ·
                refine ⟨72016030890581834910554453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 192042749041551559761478541 72016030890581834910554453)
                ·
                  refine ⟨210984465499751469464515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 72016030890581834910554453 210984465499751469464515)
                  ·
                    rfl

theorem cell23_3698017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 3, 10].length) (baseStart_3698017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3698017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3698017 prefixEnd_3698017 := by exact prefixLift 3698017
  have htrace : WordTrace (prefixWord ++ tailWord_3698017) baseStart_3698017 baseEnd_3698017 := by
    simpa [prefixWord, tailWord_3698017, baseEnd_3698017] using wordTrace_append hprefix tailTrace_3698017
  have hstable : (prefixWord ++ tailWord_3698017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3698017).length < 2 ^ (prefixWord ++ tailWord_3698017).sum := by decide
  have hdescent : baseEnd_3698017 < baseStart_3698017 := by decide
  rcases family_descends (prefixWord ++ tailWord_3698017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3698047 : List Nat := [1, 1, 2, 2, 1, 1, 2, 1, 1, 11]
def baseStart_3698047 : Nat := 118140960795 + 3698047 * 2 ^ 59
def prefixEnd_3698047 : Nat := 4983230072969 + 3 ^ 40 * 3698047 * 2
def baseEnd_3698047 : Nat := 632958531305799369268499

theorem tailTrace_3698047 : CollatzResearch.WordTrace tailWord_3698047 prefixEnd_3698047 632958531305799369268499 := by
  unfold tailWord_3698047
  simp only [CollatzResearch.WordTrace]
  refine ⟨134878854833614769990364395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89919236555743179993576263 134878854833614769990364395)
  ·
    refine ⟨202318282250422154985546593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134878854833614769990364395 202318282250422154985546593)
    ·
      refine ⟨151738711687816616239159945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 202318282250422154985546593 151738711687816616239159945)
      ·
        refine ⟨113804033765862462179369959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 151738711687816616239159945 113804033765862462179369959)
        ·
          refine ⟨170706050648793693269054939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113804033765862462179369959 170706050648793693269054939)
          ·
            refine ⟨256059075973190539903582409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 170706050648793693269054939 256059075973190539903582409)
            ·
              refine ⟨192044306979892904927686807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 256059075973190539903582409 192044306979892904927686807)
              ·
                refine ⟨288066460469839357391530211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 192044306979892904927686807 288066460469839357391530211)
                ·
                  refine ⟨432099690704759036087295317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 288066460469839357391530211 432099690704759036087295317)
                  ·
                    refine ⟨632958531305799369268499, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 11 432099690704759036087295317 632958531305799369268499)
                    ·
                      rfl

theorem cell23_3698047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 1, 1, 11].length) (baseStart_3698047 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3698047 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3698047 prefixEnd_3698047 := by exact prefixLift 3698047
  have htrace : WordTrace (prefixWord ++ tailWord_3698047) baseStart_3698047 baseEnd_3698047 := by
    simpa [prefixWord, tailWord_3698047, baseEnd_3698047] using wordTrace_append hprefix tailTrace_3698047
  have hstable : (prefixWord ++ tailWord_3698047).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3698047).length < 2 ^ (prefixWord ++ tailWord_3698047).sum := by decide
  have hdescent : baseEnd_3698047 < baseStart_3698047 := by decide
  rcases family_descends (prefixWord ++ tailWord_3698047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3698104 : List Nat := [2, 1, 2, 1, 2, 2, 3, 1, 3, 1, 5]
def baseStart_3698104 : Nat := 118140960795 + 3698104 * 2 ^ 59
def prefixEnd_3698104 : Nat := 4983230072969 + 3 ^ 40 * 3698104 * 2
def baseEnd_3698104 : Nat := 1898904862314704384792735

theorem tailTrace_3698104 : CollatzResearch.WordTrace tailWord_3698104 prefixEnd_3698104 1898904862314704384792735 := by
  unfold tailWord_3698104
  simp only [CollatzResearch.WordTrace]
  refine ⟨67440466897204134362594683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89920622529605512483459577 67440466897204134362594683)
  ·
    refine ⟨101160700345806201543892025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67440466897204134362594683 101160700345806201543892025)
    ·
      refine ⟨75870525259354651157919019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101160700345806201543892025 75870525259354651157919019)
      ·
        refine ⟨113805787889031976736878529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75870525259354651157919019 113805787889031976736878529)
        ·
          refine ⟨85354340916773982552658897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 113805787889031976736878529 85354340916773982552658897)
          ·
            refine ⟨64015755687580486914494173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85354340916773982552658897 64015755687580486914494173)
            ·
              refine ⟨24005908382842682592935315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 64015755687580486914494173 24005908382842682592935315)
              ·
                refine ⟨36008862574264023889402973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24005908382842682592935315 36008862574264023889402973)
                ·
                  refine ⟨13503323465349008958526115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36008862574264023889402973 13503323465349008958526115)
                  ·
                    refine ⟨20254985198023513437789173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13503323465349008958526115 20254985198023513437789173)
                    ·
                      refine ⟨1898904862314704384792735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20254985198023513437789173 1898904862314704384792735)
                      ·
                        rfl

theorem cell23_3698104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 3, 1, 3, 1, 5].length) (baseStart_3698104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3698104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3698104 prefixEnd_3698104 := by exact prefixLift 3698104
  have htrace : WordTrace (prefixWord ++ tailWord_3698104) baseStart_3698104 baseEnd_3698104 := by
    simpa [prefixWord, tailWord_3698104, baseEnd_3698104] using wordTrace_append hprefix tailTrace_3698104
  have hstable : (prefixWord ++ tailWord_3698104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3698104).length < 2 ^ (prefixWord ++ tailWord_3698104).sum := by decide
  have hdescent : baseEnd_3698104 < baseStart_3698104 := by decide
  rcases family_descends (prefixWord ++ tailWord_3698104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3698111 : List Nat := [1, 1, 2, 2, 2, 1, 1, 7, 2, 4]
def baseStart_3698111 : Nat := 118140960795 + 3698111 * 2 ^ 59
def prefixEnd_3698111 : Nat := 4983230072969 + 3 ^ 40 * 3698111 * 2
def baseEnd_3698111 : Nat := 632969485559761952468401

theorem tailTrace_3698111 : CollatzResearch.WordTrace tailWord_3698111 prefixEnd_3698111 632969485559761952468401 := by
  unfold tailWord_3698111
  simp only [CollatzResearch.WordTrace]
  refine ⟨134881189105382908920694187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89920792736921939280462791 134881189105382908920694187)
  ·
    refine ⟨202321783658074363381041281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134881189105382908920694187 202321783658074363381041281)
    ·
      refine ⟨151741337743555772535780961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 202321783658074363381041281 151741337743555772535780961)
      ·
        refine ⟨113806003307666829401835721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 151741337743555772535780961 113806003307666829401835721)
        ·
          refine ⟨85354502480750122051376791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 113806003307666829401835721 85354502480750122051376791)
          ·
            refine ⟨128031753721125183077065187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85354502480750122051376791 128031753721125183077065187)
            ·
              refine ⟨192047630581687774615597781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 128031753721125183077065187 192047630581687774615597781)
              ·
                refine ⟨4501116341758307217553073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 192047630581687774615597781 4501116341758307217553073)
                ·
                  refine ⟨3375837256318730413164805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4501116341758307217553073 3375837256318730413164805)
                  ·
                    refine ⟨632969485559761952468401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3375837256318730413164805 632969485559761952468401)
                    ·
                      rfl

theorem cell23_3698111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 7, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 7, 2, 4].length) (baseStart_3698111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3698111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3698111 prefixEnd_3698111 := by exact prefixLift 3698111
  have htrace : WordTrace (prefixWord ++ tailWord_3698111) baseStart_3698111 baseEnd_3698111 := by
    simpa [prefixWord, tailWord_3698111, baseEnd_3698111] using wordTrace_append hprefix tailTrace_3698111
  have hstable : (prefixWord ++ tailWord_3698111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3698111).length < 2 ^ (prefixWord ++ tailWord_3698111).sum := by decide
  have hdescent : baseEnd_3698111 < baseStart_3698111 := by decide
  rcases family_descends (prefixWord ++ tailWord_3698111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3698138 : List Nat := [3, 1, 1, 2, 3, 2, 2, 3, 1, 2, 3]
def baseStart_3698138 : Nat := 118140960795 + 3698138 * 2 ^ 59
def prefixEnd_3698138 : Nat := 4983230072969 + 3 ^ 40 * 3698138 * 2
def baseEnd_3698138 : Nat := 1898922320656957251767579

theorem tailTrace_3698138 : CollatzResearch.WordTrace tailWord_3698138 prefixEnd_3698138 1898922320656957251767579 := by
  unfold tailWord_3698138
  simp only [CollatzResearch.WordTrace]
  refine ⟨33720543469071273132981767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89921449250856728354618045 33720543469071273132981767)
  ·
    refine ⟨50580815203606909699472651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33720543469071273132981767 50580815203606909699472651)
    ·
      refine ⟨75871222805410364549208977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50580815203606909699472651 75871222805410364549208977)
      ·
        refine ⟨56903417104057773411906733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75871222805410364549208977 56903417104057773411906733)
        ·
          refine ⟨21338781414021665029465025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56903417104057773411906733 21338781414021665029465025)
          ·
            refine ⟨16004086060516248772098769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21338781414021665029465025 16004086060516248772098769)
            ·
              refine ⟨12003064545387186579074077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16004086060516248772098769 12003064545387186579074077)
              ·
                refine ⟨4501149204520194967152779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12003064545387186579074077 4501149204520194967152779)
                ·
                  refine ⟨6751723806780292450729169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4501149204520194967152779 6751723806780292450729169)
                  ·
                    refine ⟨5063792855085219338046877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6751723806780292450729169 5063792855085219338046877)
                    ·
                      refine ⟨1898922320656957251767579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5063792855085219338046877 1898922320656957251767579)
                      ·
                        rfl

theorem cell23_3698138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 2, 3, 1, 2, 3].length) (baseStart_3698138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3698138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3698138 prefixEnd_3698138 := by exact prefixLift 3698138
  have htrace : WordTrace (prefixWord ++ tailWord_3698138) baseStart_3698138 baseEnd_3698138 := by
    simpa [prefixWord, tailWord_3698138, baseEnd_3698138] using wordTrace_append hprefix tailTrace_3698138
  have hstable : (prefixWord ++ tailWord_3698138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3698138).length < 2 ^ (prefixWord ++ tailWord_3698138).sum := by decide
  have hdescent : baseEnd_3698138 < baseStart_3698138 := by decide
  rcases family_descends (prefixWord ++ tailWord_3698138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3698141 : List Nat := [1, 4, 3, 1, 1, 4, 9]
def baseStart_3698141 : Nat := 118140960795 + 3698141 * 2 ^ 59
def prefixEnd_3698141 : Nat := 4983230072969 + 3 ^ 40 * 3698141 * 2
def baseEnd_3698141 : Nat := 23443504458011367160865

theorem tailTrace_3698141 : CollatzResearch.WordTrace tailWord_3698141 prefixEnd_3698141 23443504458011367160865 := by
  unfold tailWord_3698141
  simp only [CollatzResearch.WordTrace]
  refine ⟨134882283295274224044286277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89921522196849482696190851 134882283295274224044286277)
  ·
    refine ⟨25290428117863917008303677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 134882283295274224044286277 25290428117863917008303677)
    ·
      refine ⟨9483910544198968878113879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25290428117863917008303677 9483910544198968878113879)
      ·
        refine ⟨14225865816298453317170819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9483910544198968878113879 14225865816298453317170819)
        ·
          refine ⟨21338798724447679975756229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14225865816298453317170819 21338798724447679975756229)
          ·
            refine ⟨4001024760833939995454293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21338798724447679975756229 4001024760833939995454293)
            ·
              refine ⟨23443504458011367160865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 4001024760833939995454293 23443504458011367160865)
              ·
                rfl

theorem cell23_3698141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 4, 9].length) (baseStart_3698141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3698141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3698141 prefixEnd_3698141 := by exact prefixLift 3698141
  have htrace : WordTrace (prefixWord ++ tailWord_3698141) baseStart_3698141 baseEnd_3698141 := by
    simpa [prefixWord, tailWord_3698141, baseEnd_3698141] using wordTrace_append hprefix tailTrace_3698141
  have hstable : (prefixWord ++ tailWord_3698141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3698141).length < 2 ^ (prefixWord ++ tailWord_3698141).sum := by decide
  have hdescent : baseEnd_3698141 < baseStart_3698141 := by decide
  rcases family_descends (prefixWord ++ tailWord_3698141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3698162 : List Nat := [3, 2, 1, 4, 1, 3, 2, 1, 2, 4]
def baseStart_3698162 : Nat := 118140960795 + 3698162 * 2 ^ 59
def prefixEnd_3698162 : Nat := 4983230072969 + 3 ^ 40 * 3698162 * 2
def baseEnd_3698162 : Nat := 632978214730888385955823

theorem tailTrace_3698162 : CollatzResearch.WordTrace tailWord_3698162 prefixEnd_3698162 632978214730888385955823 := by
  unfold tailWord_3698162
  simp only [CollatzResearch.WordTrace]
  refine ⟨33720762307049536157700185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89922032818798763087200493 33720762307049536157700185)
  ·
    refine ⟨25290571730287152118275139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33720762307049536157700185 25290571730287152118275139)
    ·
      refine ⟨37935857595430728177412709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25290571730287152118275139 37935857595430728177412709)
      ·
        refine ⟨7112973299143261533264883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 37935857595430728177412709 7112973299143261533264883)
        ·
          refine ⟨10669459948714892299897325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7112973299143261533264883 10669459948714892299897325)
          ·
            refine ⟨4001047480768084612461497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10669459948714892299897325 4001047480768084612461497)
            ·
              refine ⟨3000785610576063459346123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4001047480768084612461497 3000785610576063459346123)
              ·
                refine ⟨4501178415864095189019185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3000785610576063459346123 4501178415864095189019185)
                ·
                  refine ⟨3375883811898071391764389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4501178415864095189019185 3375883811898071391764389)
                  ·
                    refine ⟨632978214730888385955823, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3375883811898071391764389 632978214730888385955823)
                    ·
                      rfl

theorem cell23_3698162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 3, 2, 1, 2, 4].length) (baseStart_3698162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3698162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3698162 prefixEnd_3698162 := by exact prefixLift 3698162
  have htrace : WordTrace (prefixWord ++ tailWord_3698162) baseStart_3698162 baseEnd_3698162 := by
    simpa [prefixWord, tailWord_3698162, baseEnd_3698162] using wordTrace_append hprefix tailTrace_3698162
  have hstable : (prefixWord ++ tailWord_3698162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3698162).length < 2 ^ (prefixWord ++ tailWord_3698162).sum := by decide
  have hdescent : baseEnd_3698162 < baseStart_3698162 := by decide
  rcases family_descends (prefixWord ++ tailWord_3698162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3698189 : List Nat := [1, 7, 1, 1, 3, 1, 1, 1, 1, 1, 5]
def baseStart_3698189 : Nat := 118140960795 + 3698189 * 2 ^ 59
def prefixEnd_3698189 : Nat := 4983230072969 + 3 ^ 40 * 3698189 * 2
def baseEnd_3698189 : Nat := 1898948508170336552229845

theorem tailTrace_3698189 : CollatzResearch.WordTrace tailWord_3698189 prefixEnd_3698189 1898948508170336552229845 := by
  unfold tailWord_3698189
  simp only [CollatzResearch.WordTrace]
  refine ⟨134884033999100328242033621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89922689332733552161355747 134884033999100328242033621)
  ·
    refine ⟨3161344546853913943172663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 134884033999100328242033621 3161344546853913943172663)
    ·
      refine ⟨4742016820280870914758995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3161344546853913943172663 4742016820280870914758995)
      ·
        refine ⟨7113025230421306372138493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4742016820280870914758995 7113025230421306372138493)
        ·
          refine ⟨2667384461407989889551935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7113025230421306372138493 2667384461407989889551935)
          ·
            refine ⟨4001076692111984834327903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2667384461407989889551935 4001076692111984834327903)
            ·
              refine ⟨6001615038167977251491855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4001076692111984834327903 6001615038167977251491855)
              ·
                refine ⟨9002422557251965877237783, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6001615038167977251491855 9002422557251965877237783)
                ·
                  refine ⟨13503633835877948815856675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9002422557251965877237783 13503633835877948815856675)
                  ·
                    refine ⟨20255450753816923223785013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13503633835877948815856675 20255450753816923223785013)
                    ·
                      refine ⟨1898948508170336552229845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20255450753816923223785013 1898948508170336552229845)
                      ·
                        rfl

theorem cell23_3698189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 3, 1, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 3, 1, 1, 1, 1, 1, 5].length) (baseStart_3698189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3698189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3698189 prefixEnd_3698189 := by exact prefixLift 3698189
  have htrace : WordTrace (prefixWord ++ tailWord_3698189) baseStart_3698189 baseEnd_3698189 := by
    simpa [prefixWord, tailWord_3698189, baseEnd_3698189] using wordTrace_append hprefix tailTrace_3698189
  have hstable : (prefixWord ++ tailWord_3698189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3698189).length < 2 ^ (prefixWord ++ tailWord_3698189).sum := by decide
  have hdescent : baseEnd_3698189 < baseStart_3698189 := by decide
  rcases family_descends (prefixWord ++ tailWord_3698189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3698191 : List Nat := [1, 1, 2, 1, 1, 1, 2, 2, 2, 8, 2]
def baseStart_3698191 : Nat := 118140960795 + 3698191 * 2 ^ 59
def prefixEnd_3698191 : Nat := 4983230072969 + 3 ^ 40 * 3698191 * 2
def baseEnd_3698191 : Nat := 1898949535131645544404835

theorem tailTrace_3698191 : CollatzResearch.WordTrace tailWord_3698191 prefixEnd_3698191 1898949535131645544404835 := by
  unfold tailWord_3698191
  simp only [CollatzResearch.WordTrace]
  refine ⟨134884106945093082583606427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89922737963395388389070951 134884106945093082583606427)
  ·
    refine ⟨202326160417639623875409641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134884106945093082583606427 202326160417639623875409641)
    ·
      refine ⟨151744620313229717906557231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 202326160417639623875409641 151744620313229717906557231)
      ·
        refine ⟨227616930469844576859835847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151744620313229717906557231 227616930469844576859835847)
        ·
          refine ⟨341425395704766865289753771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 227616930469844576859835847 341425395704766865289753771)
          ·
            refine ⟨512138093557150297934630657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 341425395704766865289753771 512138093557150297934630657)
            ·
              refine ⟨384103570167862723450972993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 512138093557150297934630657 384103570167862723450972993)
              ·
                refine ⟨288077677625897042588229745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 384103570167862723450972993 288077677625897042588229745)
                ·
                  refine ⟨216058258219422781941172309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 288077677625897042588229745 216058258219422781941172309)
                  ·
                    refine ⟨2531932713508860725873113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 216058258219422781941172309 2531932713508860725873113)
                    ·
                      refine ⟨1898949535131645544404835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2531932713508860725873113 1898949535131645544404835)
                      ·
                        rfl

theorem cell23_3698191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 2, 2, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 2, 2, 8, 2].length) (baseStart_3698191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3698191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3698191 prefixEnd_3698191 := by exact prefixLift 3698191
  have htrace : WordTrace (prefixWord ++ tailWord_3698191) baseStart_3698191 baseEnd_3698191 := by
    simpa [prefixWord, tailWord_3698191, baseEnd_3698191] using wordTrace_append hprefix tailTrace_3698191
  have hstable : (prefixWord ++ tailWord_3698191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3698191).length < 2 ^ (prefixWord ++ tailWord_3698191).sum := by decide
  have hdescent : baseEnd_3698191 < baseStart_3698191 := by decide
  rcases family_descends (prefixWord ++ tailWord_3698191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3698231 : List Nat := [1, 1, 3, 1, 2, 5, 1, 2, 7]
def baseStart_3698231 : Nat := 118140960795 + 3698231 * 2 ^ 59
def prefixEnd_3698231 : Nat := 4983230072969 + 3 ^ 40 * 3698231 * 2
def baseEnd_3698231 : Nat := 210996674928647265322739

theorem tailTrace_3698231 : CollatzResearch.WordTrace tailWord_3698231 prefixEnd_3698231 210996674928647265322739 := by
  unfold tailWord_3698231
  simp only [CollatzResearch.WordTrace]
  refine ⟨134885565864948169415062547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89923710576632112943375031 134885565864948169415062547)
  ·
    refine ⟨202328348797422254122593821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134885565864948169415062547 202328348797422254122593821)
    ·
      refine ⟨75873130799033345295972683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 202328348797422254122593821 75873130799033345295972683)
      ·
        refine ⟨113809696198550017943959025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75873130799033345295972683 113809696198550017943959025)
        ·
          refine ⟨85357272148912513457969269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 113809696198550017943959025 85357272148912513457969269)
          ·
            refine ⟨8002244263960548136684619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 85357272148912513457969269 8002244263960548136684619)
            ·
              refine ⟨12003366395940822205026929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8002244263960548136684619 12003366395940822205026929)
              ·
                refine ⟨9002524796955616653770197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12003366395940822205026929 9002524796955616653770197)
                ·
                  refine ⟨210996674928647265322739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9002524796955616653770197 210996674928647265322739)
                  ·
                    rfl

theorem cell23_3698231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 5, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 5, 1, 2, 7].length) (baseStart_3698231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3698231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3698231 prefixEnd_3698231 := by exact prefixLift 3698231
  have htrace : WordTrace (prefixWord ++ tailWord_3698231) baseStart_3698231 baseEnd_3698231 := by
    simpa [prefixWord, tailWord_3698231, baseEnd_3698231] using wordTrace_append hprefix tailTrace_3698231
  have hstable : (prefixWord ++ tailWord_3698231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3698231).length < 2 ^ (prefixWord ++ tailWord_3698231).sum := by decide
  have hdescent : baseEnd_3698231 < baseStart_3698231 := by decide
  rcases family_descends (prefixWord ++ tailWord_3698231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3698258 : List Nat := [3, 2, 2, 1, 2, 2, 1, 2, 2, 3, 3]
def baseStart_3698258 : Nat := 118140960795 + 3698258 * 2 ^ 59
def prefixEnd_3698258 : Nat := 4983230072969 + 3 ^ 40 * 3698258 * 2
def baseEnd_3698258 : Nat := 1898983938335496782267027

theorem tailTrace_3698258 : CollatzResearch.WordTrace tailWord_3698258 prefixEnd_3698258 1898983938335496782267027 := by
  unfold tailWord_3698258
  simp only [CollatzResearch.WordTrace]
  refine ⟨33721637658962588256573857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89924367090566902017530285 33721637658962588256573857)
  ·
    refine ⟨25291228244221941192430393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33721637658962588256573857 25291228244221941192430393)
    ·
      refine ⟨18968421183166455894322795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25291228244221941192430393 18968421183166455894322795)
      ·
        refine ⟨28452631774749683841484193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18968421183166455894322795 28452631774749683841484193)
        ·
          refine ⟨21339473831062262881113145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28452631774749683841484193 21339473831062262881113145)
          ·
            refine ⟨16004605373296697160834859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21339473831062262881113145 16004605373296697160834859)
            ·
              refine ⟨24006908059945045741252289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16004605373296697160834859 24006908059945045741252289)
              ·
                refine ⟨18005181044958784305939217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24006908059945045741252289 18005181044958784305939217)
                ·
                  refine ⟨13503885783719088229454413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18005181044958784305939217 13503885783719088229454413)
                  ·
                    refine ⟨5063957168894658086045405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13503885783719088229454413 5063957168894658086045405)
                    ·
                      refine ⟨1898983938335496782267027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5063957168894658086045405 1898983938335496782267027)
                      ·
                        rfl

theorem cell23_3698258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 1, 2, 2, 3, 3].length) (baseStart_3698258 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3698258 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3698258 prefixEnd_3698258 := by exact prefixLift 3698258
  have htrace : WordTrace (prefixWord ++ tailWord_3698258) baseStart_3698258 baseEnd_3698258 := by
    simpa [prefixWord, tailWord_3698258, baseEnd_3698258] using wordTrace_append hprefix tailTrace_3698258
  have hstable : (prefixWord ++ tailWord_3698258).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3698258).length < 2 ^ (prefixWord ++ tailWord_3698258).sum := by decide
  have hdescent : baseEnd_3698258 < baseStart_3698258 := by decide
  rcases family_descends (prefixWord ++ tailWord_3698258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3698261 : List Nat := [1, 3, 2, 2, 1, 1, 1, 3, 4, 5]
def baseStart_3698261 : Nat := 118140960795 + 3698261 * 2 ^ 59
def prefixEnd_3698261 : Nat := 4983230072969 + 3 ^ 40 * 3698261 * 2
def baseEnd_3698261 : Nat := 632995159592486756843171

theorem tailTrace_3698261 : CollatzResearch.WordTrace tailWord_3698261 prefixEnd_3698261 632995159592486756843171 := by
  unfold tailWord_3698261
  simp only [CollatzResearch.WordTrace]
  refine ⟨134886660054839484538654637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89924440036559656359103091 134886660054839484538654637)
  ·
    refine ⟨50582497520564806701995489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 134886660054839484538654637 50582497520564806701995489)
    ·
      refine ⟨37936873140423605026496617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50582497520564806701995489 37936873140423605026496617)
      ·
        refine ⟨28452654855317703769872463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37936873140423605026496617 28452654855317703769872463)
        ·
          refine ⟨42678982282976555654808695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28452654855317703769872463 42678982282976555654808695)
          ·
            refine ⟨64018473424464833482213043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42678982282976555654808695 64018473424464833482213043)
            ·
              refine ⟨96027710136697250223319565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64018473424464833482213043 96027710136697250223319565)
              ·
                refine ⟨36010391301261468833744837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 96027710136697250223319565 36010391301261468833744837)
                ·
                  refine ⟨6751948368986525406327157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36010391301261468833744837 6751948368986525406327157)
                  ·
                    refine ⟨632995159592486756843171, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6751948368986525406327157 632995159592486756843171)
                    ·
                      rfl

theorem cell23_3698261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 3, 4, 5].length) (baseStart_3698261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3698261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3698261 prefixEnd_3698261 := by exact prefixLift 3698261
  have htrace : WordTrace (prefixWord ++ tailWord_3698261) baseStart_3698261 baseEnd_3698261 := by
    simpa [prefixWord, tailWord_3698261, baseEnd_3698261] using wordTrace_append hprefix tailTrace_3698261
  have hstable : (prefixWord ++ tailWord_3698261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3698261).length < 2 ^ (prefixWord ++ tailWord_3698261).sum := by decide
  have hdescent : baseEnd_3698261 < baseStart_3698261 := by decide
  rcases family_descends (prefixWord ++ tailWord_3698261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3698281 : List Nat := [1, 2, 1, 1, 1, 4, 3, 2, 1, 3, 4]
def baseStart_3698281 : Nat := 118140960795 + 3698281 * 2 ^ 59
def prefixEnd_3698281 : Nat := 4983230072969 + 3 ^ 40 * 3698281 * 2
def baseEnd_3698281 : Nat := 1898995748390550192279421

theorem tailTrace_3698281 : CollatzResearch.WordTrace tailWord_3698281 prefixEnd_3698281 1898995748390550192279421 := by
  unfold tailWord_3698281
  simp only [CollatzResearch.WordTrace]
  refine ⟨134887389514767027954382697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89924926343178018636255131 134887389514767027954382697)
  ·
    refine ⟨101165542136075270965787023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134887389514767027954382697 101165542136075270965787023)
    ·
      refine ⟨151748313204112906448680535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101165542136075270965787023 151748313204112906448680535)
      ·
        refine ⟨227622469806169359673020803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151748313204112906448680535 227622469806169359673020803)
        ·
          refine ⟨341433704709254039509531205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 227622469806169359673020803 341433704709254039509531205)
          ·
            refine ⟨64018819632985132408037101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 341433704709254039509531205 64018819632985132408037101)
            ·
              refine ⟨24007057362369424653013913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 64018819632985132408037101 24007057362369424653013913)
              ·
                refine ⟨18005293021777068489760435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24007057362369424653013913 18005293021777068489760435)
                ·
                  refine ⟨27007939532665602734640653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18005293021777068489760435 27007939532665602734640653)
                  ·
                    refine ⟨10127977324749601025490245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27007939532665602734640653 10127977324749601025490245)
                    ·
                      refine ⟨1898995748390550192279421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10127977324749601025490245 1898995748390550192279421)
                      ·
                        rfl

theorem cell23_3698281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 3, 2, 1, 3, 4].length) (baseStart_3698281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3698281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3698281 prefixEnd_3698281 := by exact prefixLift 3698281
  have htrace : WordTrace (prefixWord ++ tailWord_3698281) baseStart_3698281 baseEnd_3698281 := by
    simpa [prefixWord, tailWord_3698281, baseEnd_3698281] using wordTrace_append hprefix tailTrace_3698281
  have hstable : (prefixWord ++ tailWord_3698281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3698281).length < 2 ^ (prefixWord ++ tailWord_3698281).sum := by decide
  have hdescent : baseEnd_3698281 < baseStart_3698281 := by decide
  rcases family_descends (prefixWord ++ tailWord_3698281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3698298 : List Nat := [3, 1, 1, 1, 1, 1, 1, 4, 4, 4, 2]
def baseStart_3698298 : Nat := 118140960795 + 3698298 * 2 ^ 59
def prefixEnd_3698298 : Nat := 4983230072969 + 3 ^ 40 * 3698298 * 2
def baseEnd_3698298 : Nat := 1899004477561676625766843

theorem tailTrace_3698298 : CollatzResearch.WordTrace tailWord_3698298 prefixEnd_3698298 1899004477561676625766843 := by
  unfold tailWord_3698298
  simp only [CollatzResearch.WordTrace]
  refine ⟨33722002388926359964437887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89925339703803626571834365 33722002388926359964437887)
  ·
    refine ⟨50583003583389539946656831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33722002388926359964437887 50583003583389539946656831)
    ·
      refine ⟨75874505375084309919985247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50583003583389539946656831 75874505375084309919985247)
      ·
        refine ⟨113811758062626464879977871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75874505375084309919985247 113811758062626464879977871)
        ·
          refine ⟨170717637093939697319966807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113811758062626464879977871 170717637093939697319966807)
          ·
            refine ⟨256076455640909545979950211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 170717637093939697319966807 256076455640909545979950211)
            ·
              refine ⟨384114683461364318969925317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 256076455640909545979950211 384114683461364318969925317)
              ·
                refine ⟨72021503149005809806860997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 384114683461364318969925317 72021503149005809806860997)
                ·
                  refine ⟨13504031840438589338786437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 72021503149005809806860997 13504031840438589338786437)
                  ·
                    refine ⟨2532005970082235501022457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13504031840438589338786437 2532005970082235501022457)
                    ·
                      refine ⟨1899004477561676625766843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2532005970082235501022457 1899004477561676625766843)
                      ·
                        rfl

theorem cell23_3698298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 4, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 4, 4, 4, 2].length) (baseStart_3698298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3698298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3698298 prefixEnd_3698298 := by exact prefixLift 3698298
  have htrace : WordTrace (prefixWord ++ tailWord_3698298) baseStart_3698298 baseEnd_3698298 := by
    simpa [prefixWord, tailWord_3698298, baseEnd_3698298] using wordTrace_append hprefix tailTrace_3698298
  have hstable : (prefixWord ++ tailWord_3698298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3698298).length < 2 ^ (prefixWord ++ tailWord_3698298).sum := by decide
  have hdescent : baseEnd_3698298 < baseStart_3698298 := by decide
  rcases family_descends (prefixWord ++ tailWord_3698298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3698325 : List Nat := [1, 3, 2, 1, 1, 1, 1, 8, 1, 4]
def baseStart_3698325 : Nat := 118140960795 + 3698325 * 2 ^ 59
def prefixEnd_3698325 : Nat := 4983230072969 + 3 ^ 40 * 3698325 * 2
def baseEnd_3698325 : Nat := 633006113846449340043073

theorem tailTrace_3698325 : CollatzResearch.WordTrace tailWord_3698325 prefixEnd_3698325 633006113846449340043073 := by
  unfold tailWord_3698325
  simp only [CollatzResearch.WordTrace]
  refine ⟨134888994326607623468984429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89925996217738415645989619 134888994326607623468984429)
  ·
    refine ⟨50583372872477858800869161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 134888994326607623468984429 50583372872477858800869161)
    ·
      refine ⟨37937529654358394100651871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50583372872477858800869161 37937529654358394100651871)
      ·
        refine ⟨56906294481537591150977807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37937529654358394100651871 56906294481537591150977807)
        ·
          refine ⟨85359441722306386726466711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56906294481537591150977807 85359441722306386726466711)
          ·
            refine ⟨128039162583459580089700067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85359441722306386726466711 128039162583459580089700067)
            ·
              refine ⟨192058743875189370134550101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 128039162583459580089700067 192058743875189370134550101)
              ·
                refine ⟨2250688404787375431264259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 192058743875189370134550101 2250688404787375431264259)
                ·
                  refine ⟨3376032607181063146896389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2250688404787375431264259 3376032607181063146896389)
                  ·
                    refine ⟨633006113846449340043073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3376032607181063146896389 633006113846449340043073)
                    ·
                      rfl

theorem cell23_3698325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 8, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 8, 1, 4].length) (baseStart_3698325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3698325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3698325 prefixEnd_3698325 := by exact prefixLift 3698325
  have htrace : WordTrace (prefixWord ++ tailWord_3698325) baseStart_3698325 baseEnd_3698325 := by
    simpa [prefixWord, tailWord_3698325, baseEnd_3698325] using wordTrace_append hprefix tailTrace_3698325
  have hstable : (prefixWord ++ tailWord_3698325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3698325).length < 2 ^ (prefixWord ++ tailWord_3698325).sum := by decide
  have hdescent : baseEnd_3698325 < baseStart_3698325 := by decide
  rcases family_descends (prefixWord ++ tailWord_3698325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3698341 : List Nat := [1, 3, 1, 2, 1, 2, 2, 2, 1, 2, 6]
def baseStart_3698341 : Nat := 118140960795 + 3698341 * 2 ^ 59
def prefixEnd_3698341 : Nat := 4983230072969 + 3 ^ 40 * 3698341 * 2
def baseEnd_3698341 : Nat := 1899026557229819957529145

theorem tailTrace_3698341 : CollatzResearch.WordTrace tailWord_3698341 prefixEnd_3698341 1899026557229819957529145 := by
  unfold tailWord_3698341
  simp only [CollatzResearch.WordTrace]
  refine ⟨134889577894549658201566877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89926385263033105467711251 134889577894549658201566877)
  ·
    refine ⟨50583591710456121825587579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 134889577894549658201566877 50583591710456121825587579)
    ·
      refine ⟨75875387565684182738381369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50583591710456121825587579 75875387565684182738381369)
      ·
        refine ⟨56906540674263137053786027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75875387565684182738381369 56906540674263137053786027)
        ·
          refine ⟨85359811011394705580679041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56906540674263137053786027 85359811011394705580679041)
          ·
            refine ⟨64019858258546029185509281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85359811011394705580679041 64019858258546029185509281)
            ·
              refine ⟨48014893693909521889131961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64019858258546029185509281 48014893693909521889131961)
              ·
                refine ⟨36011170270432141416848971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48014893693909521889131961 36011170270432141416848971)
                ·
                  refine ⟨54016755405648212125273457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36011170270432141416848971 54016755405648212125273457)
                  ·
                    refine ⟨40512566554236159093955093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 54016755405648212125273457 40512566554236159093955093)
                    ·
                      refine ⟨1899026557229819957529145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 40512566554236159093955093 1899026557229819957529145)
                      ·
                        rfl

theorem cell23_3698341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 2, 2, 1, 2, 6].length) (baseStart_3698341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3698341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3698341 prefixEnd_3698341 := by exact prefixLift 3698341
  have htrace : WordTrace (prefixWord ++ tailWord_3698341) baseStart_3698341 baseEnd_3698341 := by
    simpa [prefixWord, tailWord_3698341, baseEnd_3698341] using wordTrace_append hprefix tailTrace_3698341
  have hstable : (prefixWord ++ tailWord_3698341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3698341).length < 2 ^ (prefixWord ++ tailWord_3698341).sum := by decide
  have hdescent : baseEnd_3698341 < baseStart_3698341 := by decide
  rcases family_descends (prefixWord ++ tailWord_3698341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3698375 : List Nat := [1, 1, 4, 1, 1, 1, 3, 4, 2, 3, 2]
def baseStart_3698375 : Nat := 118140960795 + 3698375 * 2 ^ 59
def prefixEnd_3698375 : Nat := 4983230072969 + 3 ^ 40 * 3698375 * 2
def baseEnd_3698375 : Nat := 1899044015572072824503989

theorem tailTrace_3698375 : CollatzResearch.WordTrace tailWord_3698375 prefixEnd_3698375 1899044015572072824503989 := by
  unfold tailWord_3698375
  simp only [CollatzResearch.WordTrace]
  refine ⟨134890817976426482008304579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89927211984284321338869719 134890817976426482008304579)
  ·
    refine ⟨202336226964639723012456869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134890817976426482008304579 202336226964639723012456869)
    ·
      refine ⟨37938042555869948064835663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 202336226964639723012456869 37938042555869948064835663)
      ·
        refine ⟨56907063833804922097253495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37938042555869948064835663 56907063833804922097253495)
        ·
          refine ⟨85360595750707383145880243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56907063833804922097253495 85360595750707383145880243)
          ·
            refine ⟨128040893626061074718820365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85360595750707383145880243 128040893626061074718820365)
            ·
              refine ⟨48015335109772903019557637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 128040893626061074718820365 48015335109772903019557637)
              ·
                refine ⟨9002875333082419316167057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 48015335109772903019557637 9002875333082419316167057)
                ·
                  refine ⟨6752156499811814487125293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9002875333082419316167057 6752156499811814487125293)
                  ·
                    refine ⟨2532058687429430432671985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6752156499811814487125293 2532058687429430432671985)
                    ·
                      refine ⟨1899044015572072824503989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2532058687429430432671985 1899044015572072824503989)
                      ·
                        rfl

theorem cell23_3698375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 3, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 3, 4, 2, 3, 2].length) (baseStart_3698375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3698375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3698375 prefixEnd_3698375 := by exact prefixLift 3698375
  have htrace : WordTrace (prefixWord ++ tailWord_3698375) baseStart_3698375 baseEnd_3698375 := by
    simpa [prefixWord, tailWord_3698375, baseEnd_3698375] using wordTrace_append hprefix tailTrace_3698375
  have hstable : (prefixWord ++ tailWord_3698375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3698375).length < 2 ^ (prefixWord ++ tailWord_3698375).sum := by decide
  have hdescent : baseEnd_3698375 < baseStart_3698375 := by decide
  rcases family_descends (prefixWord ++ tailWord_3698375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3698405 : List Nat := [1, 3, 1, 4, 1, 1, 2, 4, 1, 1, 4]
def baseStart_3698405 : Nat := 118140960795 + 3698405 * 2 ^ 59
def prefixEnd_3698405 : Nat := 4983230072969 + 3 ^ 40 * 3698405 * 2
def baseEnd_3698405 : Nat := 1899059419991707707128851

theorem tailTrace_3698405 : CollatzResearch.WordTrace tailWord_3698405 prefixEnd_3698405 1899059419991707707128851 := by
  unfold tailWord_3698405
  simp only [CollatzResearch.WordTrace]
  refine ⟨134891912166317797131896669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89927941444211864754597779 134891912166317797131896669)
  ·
    refine ⟨50584467062369173924461251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 134891912166317797131896669 50584467062369173924461251)
    ·
      refine ⟨75876700593553760886691877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50584467062369173924461251 75876700593553760886691877)
      ·
        refine ⟨14226881361291330166254727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 75876700593553760886691877 14226881361291330166254727)
        ·
          refine ⟨21340322041936995249382091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14226881361291330166254727 21340322041936995249382091)
          ·
            refine ⟨32010483062905492874073137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21340322041936995249382091 32010483062905492874073137)
            ·
              refine ⟨24007862297179119655554853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32010483062905492874073137 24007862297179119655554853)
              ·
                refine ⟨4501474180721084935416535, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24007862297179119655554853 4501474180721084935416535)
                ·
                  refine ⟨6752211271081627403124803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4501474180721084935416535 6752211271081627403124803)
                  ·
                    refine ⟨10128316906622441104687205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6752211271081627403124803 10128316906622441104687205)
                    ·
                      refine ⟨1899059419991707707128851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10128316906622441104687205 1899059419991707707128851)
                      ·
                        rfl

theorem cell23_3698405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 2, 4, 1, 1, 4].length) (baseStart_3698405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3698405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3698405 prefixEnd_3698405 := by exact prefixLift 3698405
  have htrace : WordTrace (prefixWord ++ tailWord_3698405) baseStart_3698405 baseEnd_3698405 := by
    simpa [prefixWord, tailWord_3698405, baseEnd_3698405] using wordTrace_append hprefix tailTrace_3698405
  have hstable : (prefixWord ++ tailWord_3698405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3698405).length < 2 ^ (prefixWord ++ tailWord_3698405).sum := by decide
  have hdescent : baseEnd_3698405 < baseStart_3698405 := by decide
  rcases family_descends (prefixWord ++ tailWord_3698405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3698411 : List Nat := [1, 1, 1, 1, 2, 4, 2, 11]
def baseStart_3698411 : Nat := 118140960795 + 3698411 * 2 ^ 59
def prefixEnd_3698411 : Nat := 4983230072969 + 3 ^ 40 * 3698411 * 2
def baseEnd_3698411 : Nat := 70335648180579062357549

theorem tailTrace_3698411 : CollatzResearch.WordTrace tailWord_3698411 prefixEnd_3698411 70335648180579062357549 := by
  unfold tailWord_3698411
  simp only [CollatzResearch.WordTrace]
  refine ⟨134892131004296060156615087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89928087336197373437743391 134892131004296060156615087)
  ·
    refine ⟨202338196506444090234922631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134892131004296060156615087 202338196506444090234922631)
    ·
      refine ⟨303507294759666135352383947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 202338196506444090234922631 303507294759666135352383947)
      ·
        refine ⟨455260942139499203028575921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 303507294759666135352383947 455260942139499203028575921)
        ·
          refine ⟨341445706604624402271431941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 455260942139499203028575921 341445706604624402271431941)
          ·
            refine ⟨64021069988367075425893489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 341445706604624402271431941 64021069988367075425893489)
            ·
              refine ⟨48015802491275306569420117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64021069988367075425893489 48015802491275306569420117)
              ·
                refine ⟨70335648180579062357549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 48015802491275306569420117 70335648180579062357549)
                ·
                  rfl

theorem cell23_3698411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 2, 11].length) (baseStart_3698411 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3698411 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3698411 prefixEnd_3698411 := by exact prefixLift 3698411
  have htrace : WordTrace (prefixWord ++ tailWord_3698411) baseStart_3698411 baseEnd_3698411 := by
    simpa [prefixWord, tailWord_3698411, baseEnd_3698411] using wordTrace_append hprefix tailTrace_3698411
  have hstable : (prefixWord ++ tailWord_3698411).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3698411).length < 2 ^ (prefixWord ++ tailWord_3698411).sum := by decide
  have hdescent : baseEnd_3698411 < baseStart_3698411 := by decide
  rcases family_descends (prefixWord ++ tailWord_3698411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3698422 : List Nat := [5, 1, 1, 1, 1, 4, 1, 3, 1, 1, 4]
def baseStart_3698422 : Nat := 118140960795 + 3698422 * 2 ^ 59
def prefixEnd_3698422 : Nat := 4983230072969 + 3 ^ 40 * 3698422 * 2
def baseEnd_3698422 : Nat := 1899068149162834140616273

theorem tailTrace_3698422 : CollatzResearch.WordTrace tailWord_3698422 prefixEnd_3698422 1899068149162834140616273 := by
  unfold tailWord_3698422
  simp only [CollatzResearch.WordTrace]
  refine ⟨8430783262953513064704095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 89928354804837472690177013 8430783262953513064704095)
  ·
    refine ⟨12646174894430269597056143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8430783262953513064704095 12646174894430269597056143)
    ·
      refine ⟨18969262341645404395584215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12646174894430269597056143 18969262341645404395584215)
      ·
        refine ⟨28453893512468106593376323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18969262341645404395584215 28453893512468106593376323)
        ·
          refine ⟨42680840268702159890064485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28453893512468106593376323 42680840268702159890064485)
          ·
            refine ⟨8002657550381654979387091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 42680840268702159890064485 8002657550381654979387091)
            ·
              refine ⟨12003986325572482469080637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8002657550381654979387091 12003986325572482469080637)
              ·
                refine ⟨4501494872089680925905239, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12003986325572482469080637 4501494872089680925905239)
                ·
                  refine ⟨6752242308134521388857859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4501494872089680925905239 6752242308134521388857859)
                  ·
                    refine ⟨10128363462201782083286789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6752242308134521388857859 10128363462201782083286789)
                    ·
                      refine ⟨1899068149162834140616273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10128363462201782083286789 1899068149162834140616273)
                      ·
                        rfl

theorem cell23_3698422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 4, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 4, 1, 3, 1, 1, 4].length) (baseStart_3698422 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3698422 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3698422 prefixEnd_3698422 := by exact prefixLift 3698422
  have htrace : WordTrace (prefixWord ++ tailWord_3698422) baseStart_3698422 baseEnd_3698422 := by
    simpa [prefixWord, tailWord_3698422, baseEnd_3698422] using wordTrace_append hprefix tailTrace_3698422
  have hstable : (prefixWord ++ tailWord_3698422).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3698422).length < 2 ^ (prefixWord ++ tailWord_3698422).sum := by decide
  have hdescent : baseEnd_3698422 < baseStart_3698422 := by decide
  rcases family_descends (prefixWord ++ tailWord_3698422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3698472 : List Nat := [2, 1, 5, 1, 1, 2, 1, 2, 4, 1, 3]
def baseStart_3698472 : Nat := 118140960795 + 3698472 * 2 ^ 59
def prefixEnd_3698472 : Nat := 4983230072969 + 3 ^ 40 * 3698472 * 2
def baseEnd_3698472 : Nat := 1899093823195558944991043

theorem tailTrace_3698472 : CollatzResearch.WordTrace tailWord_3698472 prefixEnd_3698472 1899093823195558944991043 := by
  unfold tailWord_3698472
  simp only [CollatzResearch.WordTrace]
  refine ⟨67447177928537533787292835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89929570571383378383057113 67447177928537533787292835)
  ·
    refine ⟨101170766892806300680939253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67447177928537533787292835 101170766892806300680939253)
    ·
      refine ⟨9484759396200590688838055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 101170766892806300680939253 9484759396200590688838055)
      ·
        refine ⟨14227139094300886033257083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9484759396200590688838055 14227139094300886033257083)
        ·
          refine ⟨21340708641451329049885625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14227139094300886033257083 21340708641451329049885625)
          ·
            refine ⟨16005531481088496787414219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21340708641451329049885625 16005531481088496787414219)
            ·
              refine ⟨24008297221632745181121329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16005531481088496787414219 24008297221632745181121329)
              ·
                refine ⟨18006222916224558885840997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24008297221632745181121329 18006222916224558885840997)
                ·
                  refine ⟨3376166796792104791095187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18006222916224558885840997 3376166796792104791095187)
                  ·
                    refine ⟨5064250195188157186642781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3376166796792104791095187 5064250195188157186642781)
                    ·
                      refine ⟨1899093823195558944991043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5064250195188157186642781 1899093823195558944991043)
                      ·
                        rfl

theorem cell23_3698472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 1, 2, 4, 1, 3].length) (baseStart_3698472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3698472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3698472 prefixEnd_3698472 := by exact prefixLift 3698472
  have htrace : WordTrace (prefixWord ++ tailWord_3698472) baseStart_3698472 baseEnd_3698472 := by
    simpa [prefixWord, tailWord_3698472, baseEnd_3698472] using wordTrace_append hprefix tailTrace_3698472
  have hstable : (prefixWord ++ tailWord_3698472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3698472).length < 2 ^ (prefixWord ++ tailWord_3698472).sum := by decide
  have hdescent : baseEnd_3698472 < baseStart_3698472 := by decide
  rcases family_descends (prefixWord ++ tailWord_3698472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3698516 : List Nat := [2, 4, 1, 1, 3, 3, 1, 2, 1, 3, 2]
def baseStart_3698516 : Nat := 118140960795 + 3698516 * 2 ^ 59
def prefixEnd_3698516 : Nat := 4983230072969 + 3 ^ 40 * 3698516 * 2
def baseEnd_3698516 : Nat := 1899116416344356772840841

theorem tailTrace_3698516 : CollatzResearch.WordTrace tailWord_3698516 prefixEnd_3698516 1899116416344356772840841 := by
  unfold tailWord_3698516
  simp only [CollatzResearch.WordTrace]
  refine ⟨67447980334457831544593701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89930640445943775392791601 67447980334457831544593701)
  ·
    refine ⟨12646496312710843414611319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 67447980334457831544593701 12646496312710843414611319)
    ·
      refine ⟨18969744469066265121916979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12646496312710843414611319 18969744469066265121916979)
      ·
        refine ⟨28454616703599397682875469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18969744469066265121916979 28454616703599397682875469)
        ·
          refine ⟨10670481263849774131078301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28454616703599397682875469 10670481263849774131078301)
          ·
            refine ⟨4001430473943665299154363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10670481263849774131078301 4001430473943665299154363)
            ·
              refine ⟨6002145710915497948731545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4001430473943665299154363 6002145710915497948731545)
              ·
                refine ⟨4501609283186623461548659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6002145710915497948731545 4501609283186623461548659)
                ·
                  refine ⟨6752413924779935192322989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4501609283186623461548659 6752413924779935192322989)
                  ·
                    refine ⟨2532155221792475697121121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6752413924779935192322989 2532155221792475697121121)
                    ·
                      refine ⟨1899116416344356772840841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2532155221792475697121121 1899116416344356772840841)
                      ·
                        rfl

theorem cell23_3698516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 3, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 3, 1, 2, 1, 3, 2].length) (baseStart_3698516 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3698516 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3698516 prefixEnd_3698516 := by exact prefixLift 3698516
  have htrace : WordTrace (prefixWord ++ tailWord_3698516) baseStart_3698516 baseEnd_3698516 := by
    simpa [prefixWord, tailWord_3698516, baseEnd_3698516] using wordTrace_append hprefix tailTrace_3698516
  have hstable : (prefixWord ++ tailWord_3698516).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3698516).length < 2 ^ (prefixWord ++ tailWord_3698516).sum := by decide
  have hdescent : baseEnd_3698516 < baseStart_3698516 := by decide
  rcases family_descends (prefixWord ++ tailWord_3698516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3698545 : List Nat := [1, 2, 2, 2, 1, 3, 2, 2, 2, 3, 3]
def baseStart_3698545 : Nat := 118140960795 + 3698545 * 2 ^ 59
def prefixEnd_3698545 : Nat := 4983230072969 + 3 ^ 40 * 3698545 * 2
def baseEnd_3698545 : Nat := 1899131307283337159378207

theorem tailTrace_3698545 : CollatzResearch.WordTrace tailWord_3698545 prefixEnd_3698545 1899131307283337159378207 := by
  unfold tailWord_3698545
  simp only [CollatzResearch.WordTrace]
  refine ⟨134897018385810601041993089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89931345590540400694662059 134897018385810601041993089)
  ·
    refine ⟨101172763789357950781494817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134897018385810601041993089 101172763789357950781494817)
    ·
      refine ⟨75879572842018463086121113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101172763789357950781494817 75879572842018463086121113)
      ·
        refine ⟨56909679631513847314590835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75879572842018463086121113 56909679631513847314590835)
        ·
          refine ⟨85364519447270770971886253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56909679631513847314590835 85364519447270770971886253)
          ·
            refine ⟨32011694792726539114457345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 85364519447270770971886253 32011694792726539114457345)
            ·
              refine ⟨24008771094544904335843009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32011694792726539114457345 24008771094544904335843009)
              ·
                refine ⟨18006578320908678251882257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24008771094544904335843009 18006578320908678251882257)
                ·
                  refine ⟨13504933740681508688911693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18006578320908678251882257 13504933740681508688911693)
                  ·
                    refine ⟨5064350152755565758341885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13504933740681508688911693 5064350152755565758341885)
                    ·
                      refine ⟨1899131307283337159378207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5064350152755565758341885 1899131307283337159378207)
                      ·
                        rfl

theorem cell23_3698545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 2, 2, 2, 3, 3].length) (baseStart_3698545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3698545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3698545 prefixEnd_3698545 := by exact prefixLift 3698545
  have htrace : WordTrace (prefixWord ++ tailWord_3698545) baseStart_3698545 baseEnd_3698545 := by
    simpa [prefixWord, tailWord_3698545, baseEnd_3698545] using wordTrace_append hprefix tailTrace_3698545
  have hstable : (prefixWord ++ tailWord_3698545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3698545).length < 2 ^ (prefixWord ++ tailWord_3698545).sum := by decide
  have hdescent : baseEnd_3698545 < baseStart_3698545 := by decide
  rcases family_descends (prefixWord ++ tailWord_3698545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3698595 : List Nat := [1, 1, 1, 4, 1, 2, 1, 1, 7, 4]
def baseStart_3698595 : Nat := 118140960795 + 3698595 * 2 ^ 59
def prefixEnd_3698595 : Nat := 4983230072969 + 3 ^ 40 * 3698595 * 2
def baseEnd_3698595 : Nat := 633052327105353987917659

theorem tailTrace_3698595 : CollatzResearch.WordTrace tailWord_3698595 prefixEnd_3698595 633052327105353987917659 := by
  unfold tailWord_3698595
  simp only [CollatzResearch.WordTrace]
  refine ⟨134898842035629459581313239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89932561357086306387542159 134898842035629459581313239)
  ·
    refine ⟨202348263053444189371969859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134898842035629459581313239 202348263053444189371969859)
    ·
      refine ⟨303522394580166284057954789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 202348263053444189371969859 303522394580166284057954789)
      ·
        refine ⟨56910448983781178260866523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 303522394580166284057954789 56910448983781178260866523)
        ·
          refine ⟨85365673475671767391299785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56910448983781178260866523 85365673475671767391299785)
          ·
            refine ⟨64024255106753825543474839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85365673475671767391299785 64024255106753825543474839)
            ·
              refine ⟨96036382660130738315212259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64024255106753825543474839 96036382660130738315212259)
              ·
                refine ⟨144054573990196107472818389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 96036382660130738315212259 144054573990196107472818389)
                ·
                  refine ⟨3376279077895221268894181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 144054573990196107472818389 3376279077895221268894181)
                  ·
                    refine ⟨633052327105353987917659, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3376279077895221268894181 633052327105353987917659)
                    ·
                      rfl

theorem cell23_3698595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 1, 7, 4].length) (baseStart_3698595 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3698595 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3698595 prefixEnd_3698595 := by exact prefixLift 3698595
  have htrace : WordTrace (prefixWord ++ tailWord_3698595) baseStart_3698595 baseEnd_3698595 := by
    simpa [prefixWord, tailWord_3698595, baseEnd_3698595] using wordTrace_append hprefix tailTrace_3698595
  have hstable : (prefixWord ++ tailWord_3698595).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3698595).length < 2 ^ (prefixWord ++ tailWord_3698595).sum := by decide
  have hdescent : baseEnd_3698595 < baseStart_3698595 := by decide
  rcases family_descends (prefixWord ++ tailWord_3698595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3698622 : List Nat := [4, 2, 1, 1, 1, 3, 1, 2, 1, 4, 3]
def baseStart_3698622 : Nat := 118140960795 + 3698622 * 2 ^ 59
def prefixEnd_3698622 : Nat := 4983230072969 + 3 ^ 40 * 3698622 * 2
def baseEnd_3698622 : Nat := 1899170845293733358115353

theorem tailTrace_3698622 : CollatzResearch.WordTrace tailWord_3698622 prefixEnd_3698622 1899170845293733358115353 := by
  unfold tailWord_3698622
  simp only [CollatzResearch.WordTrace]
  refine ⟨16862478350816455399068265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 89933217871021095461697413 16862478350816455399068265)
  ·
    refine ⟨12646858763112341549301199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16862478350816455399068265 12646858763112341549301199)
    ·
      refine ⟨18970288144668512323951799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12646858763112341549301199 18970288144668512323951799)
      ·
        refine ⟨28455432217002768485927699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18970288144668512323951799 28455432217002768485927699)
        ·
          refine ⟨42683148325504152728891549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28455432217002768485927699 42683148325504152728891549)
          ·
            refine ⟨16006180622064057273334331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42683148325504152728891549 16006180622064057273334331)
            ·
              refine ⟨24009270933096085910001497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16006180622064057273334331 24009270933096085910001497)
              ·
                refine ⟨18006953199822064432501123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24009270933096085910001497 18006953199822064432501123)
                ·
                  refine ⟨27010429799733096648751685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18006953199822064432501123 27010429799733096648751685)
                  ·
                    refine ⟨5064455587449955621640941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27010429799733096648751685 5064455587449955621640941)
                    ·
                      refine ⟨1899170845293733358115353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5064455587449955621640941 1899170845293733358115353)
                      ·
                        rfl

theorem cell23_3698622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 1, 2, 1, 4, 3].length) (baseStart_3698622 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3698622 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3698622 prefixEnd_3698622 := by exact prefixLift 3698622
  have htrace : WordTrace (prefixWord ++ tailWord_3698622) baseStart_3698622 baseEnd_3698622 := by
    simpa [prefixWord, tailWord_3698622, baseEnd_3698622] using wordTrace_append hprefix tailTrace_3698622
  have hstable : (prefixWord ++ tailWord_3698622).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3698622).length < 2 ^ (prefixWord ++ tailWord_3698622).sum := by decide
  have hdescent : baseEnd_3698622 < baseStart_3698622 := by decide
  rcases family_descends (prefixWord ++ tailWord_3698622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3698635 : List Nat := [1, 1, 1, 1, 3, 4, 1, 1, 2, 5, 3]
def baseStart_3698635 : Nat := 118140960795 + 3698635 * 2 ^ 59
def prefixEnd_3698635 : Nat := 4983230072969 + 3 ^ 40 * 3698635 * 2
def baseEnd_3698635 : Nat := 1899177520542241807252793

theorem tailTrace_3698635 : CollatzResearch.WordTrace tailWord_3698635 prefixEnd_3698635 1899177520542241807252793 := by
  unfold tailWord_3698635
  simp only [CollatzResearch.WordTrace]
  refine ⟨134900300955484546412769359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89933533970323030941846239 134900300955484546412769359)
  ·
    refine ⟨202350451433226819619154039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134900300955484546412769359 202350451433226819619154039)
    ·
      refine ⟨303525677149840229428731059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 202350451433226819619154039 303525677149840229428731059)
      ·
        refine ⟨455288515724760344143096589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 303525677149840229428731059 455288515724760344143096589)
        ·
          refine ⟨170733193396785129053661221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 455288515724760344143096589 170733193396785129053661221)
          ·
            refine ⟨32012473761897211697561479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 170733193396785129053661221 32012473761897211697561479)
            ·
              refine ⟨48018710642845817546342219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32012473761897211697561479 48018710642845817546342219)
              ·
                refine ⟨72028065964268726319513329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48018710642845817546342219 72028065964268726319513329)
                ·
                  refine ⟨54021049473201544739634997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 72028065964268726319513329 54021049473201544739634997)
                  ·
                    refine ⟨5064473388112644819340781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 54021049473201544739634997 5064473388112644819340781)
                    ·
                      refine ⟨1899177520542241807252793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5064473388112644819340781 1899177520542241807252793)
                      ·
                        rfl

theorem cell23_3698635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 1, 1, 2, 5, 3].length) (baseStart_3698635 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3698635 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3698635 prefixEnd_3698635 := by exact prefixLift 3698635
  have htrace : WordTrace (prefixWord ++ tailWord_3698635) baseStart_3698635 baseEnd_3698635 := by
    simpa [prefixWord, tailWord_3698635, baseEnd_3698635] using wordTrace_append hprefix tailTrace_3698635
  have hstable : (prefixWord ++ tailWord_3698635).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3698635).length < 2 ^ (prefixWord ++ tailWord_3698635).sum := by decide
  have hdescent : baseEnd_3698635 < baseStart_3698635 := by decide
  rcases family_descends (prefixWord ++ tailWord_3698635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3698663 : List Nat := [1, 1, 5, 2, 3, 1, 3, 2, 1, 4]
def baseStart_3698663 : Nat := 118140960795 + 3698663 * 2 ^ 59
def prefixEnd_3698663 : Nat := 4983230072969 + 3 ^ 40 * 3698663 * 2
def baseEnd_3698663 : Nat := 633063966000189232567555

theorem tailTrace_3698663 : CollatzResearch.WordTrace tailWord_3698663 prefixEnd_3698663 633063966000189232567555 := by
  unfold tailWord_3698663
  simp only [CollatzResearch.WordTrace]
  refine ⟨134901322199383107194788643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89934214799588738129859095 134901322199383107194788643)
  ·
    refine ⟨202351983299074660792182965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134901322199383107194788643 202351983299074660792182965)
    ·
      refine ⟨18970498434288249449267153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 202351983299074660792182965 18970498434288249449267153)
      ·
        refine ⟨14227873825716187086950365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18970498434288249449267153 14227873825716187086950365)
        ·
          refine ⟨5335452684643570157606387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14227873825716187086950365 5335452684643570157606387)
          ·
            refine ⟨8003179026965355236409581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5335452684643570157606387 8003179026965355236409581)
            ·
              refine ⟨3001192135112008213653593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8003179026965355236409581 3001192135112008213653593)
              ·
                refine ⟨2250894101334006160240195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3001192135112008213653593 2250894101334006160240195)
                ·
                  refine ⟨3376341152001009240360293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2250894101334006160240195 3376341152001009240360293)
                  ·
                    refine ⟨633063966000189232567555, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3376341152001009240360293 633063966000189232567555)
                    ·
                      rfl

theorem cell23_3698663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 1, 3, 2, 1, 4].length) (baseStart_3698663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3698663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3698663 prefixEnd_3698663 := by exact prefixLift 3698663
  have htrace : WordTrace (prefixWord ++ tailWord_3698663) baseStart_3698663 baseEnd_3698663 := by
    simpa [prefixWord, tailWord_3698663, baseEnd_3698663] using wordTrace_append hprefix tailTrace_3698663
  have hstable : (prefixWord ++ tailWord_3698663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3698663).length < 2 ^ (prefixWord ++ tailWord_3698663).sum := by decide
  have hdescent : baseEnd_3698663 < baseStart_3698663 := by decide
  rcases family_descends (prefixWord ++ tailWord_3698663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3698702 : List Nat := [4, 1, 1, 2, 2, 1, 3, 2, 1, 6]
def baseStart_3698702 : Nat := 118140960795 + 3698702 * 2 ^ 59
def prefixEnd_3698702 : Nat := 4983230072969 + 3 ^ 40 * 3698702 * 2
def baseEnd_3698702 : Nat := 633070641248697681704995

theorem tailTrace_3698702 : CollatzResearch.WordTrace tailWord_3698702 prefixEnd_3698702 633070641248697681704995 := by
  unfold tailWord_3698702
  simp only [CollatzResearch.WordTrace]
  refine ⟨16862843080780227106932295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 89935163097494544570305573 16862843080780227106932295)
  ·
    refine ⟨25294264621170340660398443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16862843080780227106932295 25294264621170340660398443)
    ·
      refine ⟨37941396931755510990597665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25294264621170340660398443 37941396931755510990597665)
      ·
        refine ⟨28456047698816633242948249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37941396931755510990597665 28456047698816633242948249)
        ·
          refine ⟨21342035774112474932211187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28456047698816633242948249 21342035774112474932211187)
          ·
            refine ⟨32013053661168712398316781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21342035774112474932211187 32013053661168712398316781)
            ·
              refine ⟨12004895122938267149368793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32013053661168712398316781 12004895122938267149368793)
              ·
                refine ⟨9003671342203700362026595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12004895122938267149368793 9003671342203700362026595)
                ·
                  refine ⟨13505507013305550543039893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9003671342203700362026595 13505507013305550543039893)
                  ·
                    refine ⟨633070641248697681704995, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13505507013305550543039893 633070641248697681704995)
                    ·
                      rfl

theorem cell23_3698702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 3, 2, 1, 6].length) (baseStart_3698702 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3698702 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3698702 prefixEnd_3698702 := by exact prefixLift 3698702
  have htrace : WordTrace (prefixWord ++ tailWord_3698702) baseStart_3698702 baseEnd_3698702 := by
    simpa [prefixWord, tailWord_3698702, baseEnd_3698702] using wordTrace_append hprefix tailTrace_3698702
  have hstable : (prefixWord ++ tailWord_3698702).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3698702).length < 2 ^ (prefixWord ++ tailWord_3698702).sum := by decide
  have hdescent : baseEnd_3698702 < baseStart_3698702 := by decide
  rcases family_descends (prefixWord ++ tailWord_3698702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3698719 : List Nat := [1, 1, 2, 4, 1, 2, 4, 2, 2, 4]
def baseStart_3698719 : Nat := 118140960795 + 3698719 * 2 ^ 59
def prefixEnd_3698719 : Nat := 4983230072969 + 3 ^ 40 * 3698719 * 2
def baseEnd_3698719 : Nat := 633073550972406492867469

theorem tailTrace_3698719 : CollatzResearch.WordTrace tailWord_3698719 prefixEnd_3698719 633073550972406492867469 := by
  unfold tailWord_3698719
  simp only [CollatzResearch.WordTrace]
  refine ⟨134903364687180228758827211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89935576458120152505884807 134903364687180228758827211)
  ·
    refine ⟨202355047030770343138240817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134903364687180228758827211 202355047030770343138240817)
    ·
      refine ⟨151766285273077757353680613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 202355047030770343138240817 151766285273077757353680613)
      ·
        refine ⟨28456178488702079503815115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 151766285273077757353680613 28456178488702079503815115)
        ·
          refine ⟨42684267733053119255722673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28456178488702079503815115 42684267733053119255722673)
          ·
            refine ⟨32013200799789839441792005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42684267733053119255722673 32013200799789839441792005)
            ·
              refine ⟨6002475149960594895336001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32013200799789839441792005 6002475149960594895336001)
              ·
                refine ⟨4501856362470446171502001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6002475149960594895336001 4501856362470446171502001)
                ·
                  refine ⟨3376392271852834628626501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4501856362470446171502001 3376392271852834628626501)
                  ·
                    refine ⟨633073550972406492867469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3376392271852834628626501 633073550972406492867469)
                    ·
                      rfl

theorem cell23_3698719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 4, 2, 2, 4].length) (baseStart_3698719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3698719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3698719 prefixEnd_3698719 := by exact prefixLift 3698719
  have htrace : WordTrace (prefixWord ++ tailWord_3698719) baseStart_3698719 baseEnd_3698719 := by
    simpa [prefixWord, tailWord_3698719, baseEnd_3698719] using wordTrace_append hprefix tailTrace_3698719
  have hstable : (prefixWord ++ tailWord_3698719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3698719).length < 2 ^ (prefixWord ++ tailWord_3698719).sum := by decide
  have hdescent : baseEnd_3698719 < baseStart_3698719 := by decide
  rcases family_descends (prefixWord ++ tailWord_3698719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3698722 : List Nat := [3, 3, 1, 1, 1, 2, 1, 2, 3, 2, 4]
def baseStart_3698722 : Nat := 118140960795 + 3698722 * 2 ^ 59
def prefixEnd_3698722 : Nat := 4983230072969 + 3 ^ 40 * 3698722 * 2
def baseEnd_3698722 : Nat := 1899222193359182966864893

theorem tailTrace_3698722 : CollatzResearch.WordTrace tailWord_3698722 prefixEnd_3698722 1899222193359182966864893 := by
  unfold tailWord_3698722
  simp only [CollatzResearch.WordTrace]
  refine ⟨33725868526542340067796605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89935649404112906847457613 33725868526542340067796605)
  ·
    refine ⟨12647200697453377525423727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33725868526542340067796605 12647200697453377525423727)
    ·
      refine ⟨18970801046180066288135591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12647200697453377525423727 18970801046180066288135591)
      ·
        refine ⟨28456201569270099432203387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18970801046180066288135591 28456201569270099432203387)
        ·
          refine ⟨42684302353905149148305081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28456201569270099432203387 42684302353905149148305081)
          ·
            refine ⟨32013226765428861861228811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42684302353905149148305081 32013226765428861861228811)
            ·
              refine ⟨48019840148143292791843217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32013226765428861861228811 48019840148143292791843217)
              ·
                refine ⟨36014880111107469593882413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48019840148143292791843217 36014880111107469593882413)
                ·
                  refine ⟨13505580041665301097705905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36014880111107469593882413 13505580041665301097705905)
                  ·
                    refine ⟨10129185031248975823279429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13505580041665301097705905 10129185031248975823279429)
                    ·
                      refine ⟨1899222193359182966864893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10129185031248975823279429 1899222193359182966864893)
                      ·
                        rfl

theorem cell23_3698722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 1, 2, 3, 2, 4].length) (baseStart_3698722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3698722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3698722 prefixEnd_3698722 := by exact prefixLift 3698722
  have htrace : WordTrace (prefixWord ++ tailWord_3698722) baseStart_3698722 baseEnd_3698722 := by
    simpa [prefixWord, tailWord_3698722, baseEnd_3698722] using wordTrace_append hprefix tailTrace_3698722
  have hstable : (prefixWord ++ tailWord_3698722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3698722).length < 2 ^ (prefixWord ++ tailWord_3698722).sum := by decide
  have hdescent : baseEnd_3698722 < baseStart_3698722 := by decide
  rcases family_descends (prefixWord ++ tailWord_3698722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3698759 : List Nat := [1, 1, 4, 1, 3, 1, 2, 2, 4, 1, 3]
def baseStart_3698759 : Nat := 118140960795 + 3698759 * 2 ^ 59
def prefixEnd_3698759 : Nat := 4983230072969 + 3 ^ 40 * 3698759 * 2
def baseEnd_3698759 : Nat := 1899241192143399322102223

theorem tailTrace_3698759 : CollatzResearch.WordTrace tailWord_3698759 prefixEnd_3698759 1899241192143399322102223 := by
  unfold tailWord_3698759
  simp only [CollatzResearch.WordTrace]
  refine ⟨134904823607035315590283331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89936549071356877060188887 134904823607035315590283331)
  ·
    refine ⟨202357235410552973385424997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134904823607035315590283331 202357235410552973385424997)
    ·
      refine ⟨37941981639478682509767187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 202357235410552973385424997 37941981639478682509767187)
      ·
        refine ⟨56912972459218023764650781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37941981639478682509767187 56912972459218023764650781)
        ·
          refine ⟨21342364672206758911744043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56912972459218023764650781 21342364672206758911744043)
          ·
            refine ⟨32013547008310138367616065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21342364672206758911744043 32013547008310138367616065)
            ·
              refine ⟨24010160256232603775712049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32013547008310138367616065 24010160256232603775712049)
              ·
                refine ⟨18007620192174452831784037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24010160256232603775712049 18007620192174452831784037)
                ·
                  refine ⟨3376428786032709905959507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18007620192174452831784037 3376428786032709905959507)
                  ·
                    refine ⟨5064643179049064858939261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3376428786032709905959507 5064643179049064858939261)
                    ·
                      refine ⟨1899241192143399322102223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5064643179049064858939261 1899241192143399322102223)
                      ·
                        rfl

theorem cell23_3698759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 2, 2, 4, 1, 3].length) (baseStart_3698759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3698759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3698759 prefixEnd_3698759 := by exact prefixLift 3698759
  have htrace : WordTrace (prefixWord ++ tailWord_3698759) baseStart_3698759 baseEnd_3698759 := by
    simpa [prefixWord, tailWord_3698759, baseEnd_3698759] using wordTrace_append hprefix tailTrace_3698759
  have hstable : (prefixWord ++ tailWord_3698759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3698759).length < 2 ^ (prefixWord ++ tailWord_3698759).sum := by decide
  have hdescent : baseEnd_3698759 < baseStart_3698759 := by decide
  rcases family_descends (prefixWord ++ tailWord_3698759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3698776 : List Nat := [2, 1, 2, 2, 1, 4, 3, 2, 2, 1, 3]
def baseStart_3698776 : Nat := 118140960795 + 3698776 * 2 ^ 59
def prefixEnd_3698776 : Nat := 4983230072969 + 3 ^ 40 * 3698776 * 2
def baseEnd_3698776 : Nat := 1899249921314525755589645

theorem tailTrace_3698776 : CollatzResearch.WordTrace tailWord_3698776 prefixEnd_3698776 1899249921314525755589645 := by
  unfold tailWord_3698776
  simp only [CollatzResearch.WordTrace]
  refine ⟨67452721823986863746826091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89936962431982484995768121 67452721823986863746826091)
  ·
    refine ⟨101179082735980295620239137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67452721823986863746826091 101179082735980295620239137)
    ·
      refine ⟨75884312051985221715179353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101179082735980295620239137 75884312051985221715179353)
      ·
        refine ⟨56913234038988916286384515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75884312051985221715179353 56913234038988916286384515)
        ·
          refine ⟨85369851058483374429576773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56913234038988916286384515 85369851058483374429576773)
          ·
            refine ⟨16006847073465632705545645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 85369851058483374429576773 16006847073465632705545645)
            ·
              refine ⟨6002567652549612264579617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16006847073465632705545645 6002567652549612264579617)
              ·
                refine ⟨4501925739412209198434713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6002567652549612264579617 4501925739412209198434713)
                ·
                  refine ⟨3376444304559156898826035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4501925739412209198434713 3376444304559156898826035)
                  ·
                    refine ⟨5064666456838735348239053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3376444304559156898826035 5064666456838735348239053)
                    ·
                      refine ⟨1899249921314525755589645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5064666456838735348239053 1899249921314525755589645)
                      ·
                        rfl

theorem cell23_3698776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 3, 2, 2, 1, 3].length) (baseStart_3698776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3698776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3698776 prefixEnd_3698776 := by exact prefixLift 3698776
  have htrace : WordTrace (prefixWord ++ tailWord_3698776) baseStart_3698776 baseEnd_3698776 := by
    simpa [prefixWord, tailWord_3698776, baseEnd_3698776] using wordTrace_append hprefix tailTrace_3698776
  have hstable : (prefixWord ++ tailWord_3698776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3698776).length < 2 ^ (prefixWord ++ tailWord_3698776).sum := by decide
  have hdescent : baseEnd_3698776 < baseStart_3698776 := by decide
  rcases family_descends (prefixWord ++ tailWord_3698776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3698795 : List Nat := [1, 1, 1, 1, 2, 2, 1, 1, 1, 2, 10]
def baseStart_3698795 : Nat := 118140960795 + 3698795 * 2 ^ 59
def prefixEnd_3698795 : Nat := 4983230072969 + 3 ^ 40 * 3698795 * 2
def baseEnd_3698795 : Nat := 1899259677446961181252057

theorem tailTrace_3698795 : CollatzResearch.WordTrace tailWord_3698795 prefixEnd_3698795 1899259677446961181252057 := by
  unfold tailWord_3698795
  simp only [CollatzResearch.WordTrace]
  refine ⟨134906136634904893738593839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89937424423269929159062559 134906136634904893738593839)
  ·
    refine ⟨202359204952357340607890759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134906136634904893738593839 202359204952357340607890759)
    ·
      refine ⟨303538807428536010911836139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 202359204952357340607890759 303538807428536010911836139)
      ·
        refine ⟨455308211142804016367754209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 303538807428536010911836139 455308211142804016367754209)
        ·
          refine ⟨341481158357103012275815657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 455308211142804016367754209 341481158357103012275815657)
          ·
            refine ⟨256110868767827259206861743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 341481158357103012275815657 256110868767827259206861743)
            ·
              refine ⟨384166303151740888810292615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 256110868767827259206861743 384166303151740888810292615)
              ·
                refine ⟨576249454727611333215438923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 384166303151740888810292615 576249454727611333215438923)
                ·
                  refine ⟨864374182091416999823158385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 576249454727611333215438923 864374182091416999823158385)
                  ·
                    refine ⟨648280636568562749867368789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 864374182091416999823158385 648280636568562749867368789)
                    ·
                      refine ⟨1899259677446961181252057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 10 648280636568562749867368789 1899259677446961181252057)
                      ·
                        rfl

theorem cell23_3698795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 1, 1, 2, 10].length) (baseStart_3698795 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3698795 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3698795 prefixEnd_3698795 := by exact prefixLift 3698795
  have htrace : WordTrace (prefixWord ++ tailWord_3698795) baseStart_3698795 baseEnd_3698795 := by
    simpa [prefixWord, tailWord_3698795, baseEnd_3698795] using wordTrace_append hprefix tailTrace_3698795
  have hstable : (prefixWord ++ tailWord_3698795).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3698795).length < 2 ^ (prefixWord ++ tailWord_3698795).sum := by decide
  have hdescent : baseEnd_3698795 < baseStart_3698795 := by decide
  rcases family_descends (prefixWord ++ tailWord_3698795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3698850 : List Nat := [3, 3, 1, 3, 1, 2, 1, 3, 2, 2, 2]
def baseStart_3698850 : Nat := 118140960795 + 3698850 * 2 ^ 59
def prefixEnd_3698850 : Nat := 4983230072969 + 3 ^ 40 * 3698850 * 2
def baseEnd_3698850 : Nat := 1899287918882958466064305

theorem tailTrace_3698850 : CollatzResearch.WordTrace tailWord_3698850 prefixEnd_3698850 1899287918882958466064305 := by
  unfold tailWord_3698850
  simp only [CollatzResearch.WordTrace]
  refine ⟨33727035662426409532961501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89938761766470425421230669 33727035662426409532961501)
  ·
    refine ⟨12647638373409903574860563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33727035662426409532961501 12647638373409903574860563)
    ·
      refine ⟨18971457560114855362290845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12647638373409903574860563 18971457560114855362290845)
      ·
        refine ⟨7114296585043070760859067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18971457560114855362290845 7114296585043070760859067)
        ·
          refine ⟨10671444877564606141288601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7114296585043070760859067 10671444877564606141288601)
          ·
            refine ⟨8003583658173454605966451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10671444877564606141288601 8003583658173454605966451)
            ·
              refine ⟨12005375487260181908949677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8003583658173454605966451 12005375487260181908949677)
              ·
                refine ⟨4502015807722568215856129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12005375487260181908949677 4502015807722568215856129)
                ·
                  refine ⟨3376511855791926161892097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4502015807722568215856129 3376511855791926161892097)
                  ·
                    refine ⟨2532383891843944621419073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3376511855791926161892097 2532383891843944621419073)
                    ·
                      refine ⟨1899287918882958466064305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2532383891843944621419073 1899287918882958466064305)
                      ·
                        rfl

theorem cell23_3698850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 2, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 2, 1, 3, 2, 2, 2].length) (baseStart_3698850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3698850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3698850 prefixEnd_3698850 := by exact prefixLift 3698850
  have htrace : WordTrace (prefixWord ++ tailWord_3698850) baseStart_3698850 baseEnd_3698850 := by
    simpa [prefixWord, tailWord_3698850, baseEnd_3698850] using wordTrace_append hprefix tailTrace_3698850
  have hstable : (prefixWord ++ tailWord_3698850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3698850).length < 2 ^ (prefixWord ++ tailWord_3698850).sum := by decide
  have hdescent : baseEnd_3698850 < baseStart_3698850 := by decide
  rcases family_descends (prefixWord ++ tailWord_3698850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3698946 : List Nat := [3, 4, 1, 1, 2, 2, 1, 1, 8]
def baseStart_3698946 : Nat := 118140960795 + 3698946 * 2 ^ 59
def prefixEnd_3698946 : Nat := 4983230072969 + 3 ^ 40 * 3698946 * 2
def baseEnd_3698946 : Nat := 211037468113976676718207

theorem tailTrace_3698946 : CollatzResearch.WordTrace tailWord_3698946 prefixEnd_3698946 211037468113976676718207 := by
  unfold tailWord_3698946
  simp only [CollatzResearch.WordTrace]
  refine ⟨33727911014339461631835173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89941096038238564351560461 33727911014339461631835173)
  ·
    refine ⟨6323983315188649055969095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 33727911014339461631835173 6323983315188649055969095)
    ·
      refine ⟨9485974972782973583953643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6323983315188649055969095 9485974972782973583953643)
      ·
        refine ⟨14228962459174460375930465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9485974972782973583953643 14228962459174460375930465)
        ·
          refine ⟨10671721844380845281947849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14228962459174460375930465 10671721844380845281947849)
          ·
            refine ⟨8003791383285633961460887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10671721844380845281947849 8003791383285633961460887)
            ·
              refine ⟨12005687074928450942191331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8003791383285633961460887 12005687074928450942191331)
              ·
                refine ⟨18008530612392676413286997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12005687074928450942191331 18008530612392676413286997)
                ·
                  refine ⟨211037468113976676718207, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 18008530612392676413286997 211037468113976676718207)
                  ·
                    rfl

theorem cell23_3698946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 2, 1, 1, 8].length) (baseStart_3698946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3698946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3698946 prefixEnd_3698946 := by exact prefixLift 3698946
  have htrace : WordTrace (prefixWord ++ tailWord_3698946) baseStart_3698946 baseEnd_3698946 := by
    simpa [prefixWord, tailWord_3698946, baseEnd_3698946] using wordTrace_append hprefix tailTrace_3698946
  have hstable : (prefixWord ++ tailWord_3698946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3698946).length < 2 ^ (prefixWord ++ tailWord_3698946).sum := by decide
  have hdescent : baseEnd_3698946 < baseStart_3698946 := by decide
  rcases family_descends (prefixWord ++ tailWord_3698946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3698976 : List Nat := [2, 1, 1, 5, 2, 1, 1, 4, 1, 5]
def baseStart_3698976 : Nat := 118140960795 + 3698976 * 2 ^ 59
def prefixEnd_3698976 : Nat := 4983230072969 + 3 ^ 40 * 3698976 * 2
def baseEnd_3698976 : Nat := 633117539148474991029575

theorem tailTrace_3698976 : CollatzResearch.WordTrace tailWord_3698976 prefixEnd_3698976 633117539148474991029575 := by
  unfold tailWord_3698976
  simp only [CollatzResearch.WordTrace]
  refine ⟨67456369123624580825466391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89941825498166107767288521 67456369123624580825466391)
  ·
    refine ⟨101184553685436871238199587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67456369123624580825466391 101184553685436871238199587)
    ·
      refine ⟨151776830528155306857299381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101184553685436871238199587 151776830528155306857299381)
      ·
        refine ⟨14229077862014560017871817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 151776830528155306857299381 14229077862014560017871817)
        ·
          refine ⟨10671808396510920013403863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14229077862014560017871817 10671808396510920013403863)
          ·
            refine ⟨16007712594766380020105795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10671808396510920013403863 16007712594766380020105795)
            ·
              refine ⟨24011568892149570030158693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16007712594766380020105795 24011568892149570030158693)
              ·
                refine ⟨4502169167278044380654755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24011568892149570030158693 4502169167278044380654755)
                ·
                  refine ⟨6753253750917066570982133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4502169167278044380654755 6753253750917066570982133)
                  ·
                    refine ⟨633117539148474991029575, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6753253750917066570982133 633117539148474991029575)
                    ·
                      rfl

theorem cell23_3698976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 1, 4, 1, 5].length) (baseStart_3698976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3698976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3698976 prefixEnd_3698976 := by exact prefixLift 3698976
  have htrace : WordTrace (prefixWord ++ tailWord_3698976) baseStart_3698976 baseEnd_3698976 := by
    simpa [prefixWord, tailWord_3698976, baseEnd_3698976] using wordTrace_append hprefix tailTrace_3698976
  have hstable : (prefixWord ++ tailWord_3698976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3698976).length < 2 ^ (prefixWord ++ tailWord_3698976).sum := by decide
  have hdescent : baseEnd_3698976 < baseStart_3698976 := by decide
  rcases family_descends (prefixWord ++ tailWord_3698976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3699103 : List Nat := [1, 1, 2, 5, 1, 1, 1, 4, 1, 4, 2]
def baseStart_3699103 : Nat := 118140960795 + 3699103 * 2 ^ 59
def prefixEnd_3699103 : Nat := 4983230072969 + 3 ^ 40 * 3699103 * 2
def baseEnd_3699103 : Nat := 1899417829488545976200641

theorem tailTrace_3699103 : CollatzResearch.WordTrace tailWord_3699103 prefixEnd_3699103 1899417829488545976200641 := by
  unfold tailWord_3699103
  simp only [CollatzResearch.WordTrace]
  refine ⟨134917370317789062340805963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89944913545192708227203975 134917370317789062340805963)
  ·
    refine ⟨202376055476683593511208945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134917370317789062340805963 202376055476683593511208945)
    ·
      refine ⟨151782041607512695133406709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 202376055476683593511208945 151782041607512695133406709)
      ·
        refine ⟨14229566400704315168756879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 151782041607512695133406709 14229566400704315168756879)
        ·
          refine ⟨21344349601056472753135319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14229566400704315168756879 21344349601056472753135319)
          ·
            refine ⟨32016524401584709129702979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21344349601056472753135319 32016524401584709129702979)
            ·
              refine ⟨48024786602377063694554469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32016524401584709129702979 48024786602377063694554469)
              ·
                refine ⟨9004647487945699442728963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 48024786602377063694554469 9004647487945699442728963)
                ·
                  refine ⟨13506971231918549164093445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9004647487945699442728963 13506971231918549164093445)
                  ·
                    refine ⟨2532557105984727968267521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13506971231918549164093445 2532557105984727968267521)
                    ·
                      refine ⟨1899417829488545976200641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2532557105984727968267521 1899417829488545976200641)
                      ·
                        rfl

theorem cell23_3699103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 1, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 1, 4, 1, 4, 2].length) (baseStart_3699103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3699103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3699103 prefixEnd_3699103 := by exact prefixLift 3699103
  have htrace : WordTrace (prefixWord ++ tailWord_3699103) baseStart_3699103 baseEnd_3699103 := by
    simpa [prefixWord, tailWord_3699103, baseEnd_3699103] using wordTrace_append hprefix tailTrace_3699103
  have hstable : (prefixWord ++ tailWord_3699103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3699103).length < 2 ^ (prefixWord ++ tailWord_3699103).sum := by decide
  have hdescent : baseEnd_3699103 < baseStart_3699103 := by decide
  rcases family_descends (prefixWord ++ tailWord_3699103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3699106 : List Nat := [3, 3, 1, 2, 1, 1, 2, 1, 1, 3, 5]
def baseStart_3699106 : Nat := 118140960795 + 3699106 * 2 ^ 59
def prefixEnd_3699106 : Nat := 4983230072969 + 3 ^ 40 * 3699106 * 2
def baseEnd_3699106 : Nat := 1899419369930509464463127

theorem tailTrace_3699106 : CollatzResearch.WordTrace tailWord_3699106 prefixEnd_3699106 1899419369930509464463127 := by
  unfold tailWord_3699106
  simp only [CollatzResearch.WordTrace]
  refine ⟨33729369934194548463291293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89944986491185462568776781 33729369934194548463291293)
  ·
    refine ⟨12648513725322955673734235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33729369934194548463291293 12648513725322955673734235)
    ·
      refine ⟨18972770587984433510601353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12648513725322955673734235 18972770587984433510601353)
      ·
        refine ⟨14229577940988325132951015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18972770587984433510601353 14229577940988325132951015)
        ·
          refine ⟨21344366911482487699426523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14229577940988325132951015 21344366911482487699426523)
          ·
            refine ⟨32016550367223731549139785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21344366911482487699426523 32016550367223731549139785)
            ·
              refine ⟨24012412775417798661854839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32016550367223731549139785 24012412775417798661854839)
              ·
                refine ⟨36018619163126697992782259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24012412775417798661854839 36018619163126697992782259)
                ·
                  refine ⟨54027928744690046989173389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36018619163126697992782259 54027928744690046989173389)
                  ·
                    refine ⟨20260473279258767620940021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 54027928744690046989173389 20260473279258767620940021)
                    ·
                      refine ⟨1899419369930509464463127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20260473279258767620940021 1899419369930509464463127)
                      ·
                        rfl

theorem cell23_3699106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 2, 1, 1, 3, 5].length) (baseStart_3699106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3699106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3699106 prefixEnd_3699106 := by exact prefixLift 3699106
  have htrace : WordTrace (prefixWord ++ tailWord_3699106) baseStart_3699106 baseEnd_3699106 := by
    simpa [prefixWord, tailWord_3699106, baseEnd_3699106] using wordTrace_append hprefix tailTrace_3699106
  have hstable : (prefixWord ++ tailWord_3699106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3699106).length < 2 ^ (prefixWord ++ tailWord_3699106).sum := by decide
  have hdescent : baseEnd_3699106 < baseStart_3699106 := by decide
  rcases family_descends (prefixWord ++ tailWord_3699106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3699107 : List Nat := [1, 1, 1, 4, 1, 6, 2, 1, 1, 3, 2]
def baseStart_3699107 : Nat := 118140960795 + 3699107 * 2 ^ 59
def prefixEnd_3699107 : Nat := 4983230072969 + 3 ^ 40 * 3699107 * 2
def baseEnd_3699107 : Nat := 1899419883411163960550623

theorem tailTrace_3699107 : CollatzResearch.WordTrace tailWord_3699107 prefixEnd_3699107 1899419883411163960550623 := by
  unfold tailWord_3699107
  simp only [CollatzResearch.WordTrace]
  refine ⟨134917516209774571023951575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89945010806516380682634383 134917516209774571023951575)
  ·
    refine ⟨202376274314661856535927363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134917516209774571023951575 202376274314661856535927363)
    ·
      refine ⟨303564411471992784803891045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 202376274314661856535927363 303564411471992784803891045)
      ·
        refine ⟨56918327150998647150729571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 303564411471992784803891045 56918327150998647150729571)
        ·
          refine ⟨85377490726497970726094357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56918327150998647150729571 85377490726497970726094357)
          ·
            refine ⟨4002069877804592377785673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 85377490726497970726094357 4002069877804592377785673)
            ·
              refine ⟨3001552408353444283339255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4002069877804592377785673 3001552408353444283339255)
              ·
                refine ⟨4502328612530166425008883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3001552408353444283339255 4502328612530166425008883)
                ·
                  refine ⟨6753492918795249637513325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4502328612530166425008883 6753492918795249637513325)
                  ·
                    refine ⟨2532559844548218614067497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6753492918795249637513325 2532559844548218614067497)
                    ·
                      refine ⟨1899419883411163960550623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2532559844548218614067497 1899419883411163960550623)
                      ·
                        rfl

theorem cell23_3699107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 6, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 6, 2, 1, 1, 3, 2].length) (baseStart_3699107 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3699107 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3699107 prefixEnd_3699107 := by exact prefixLift 3699107
  have htrace : WordTrace (prefixWord ++ tailWord_3699107) baseStart_3699107 baseEnd_3699107 := by
    simpa [prefixWord, tailWord_3699107, baseEnd_3699107] using wordTrace_append hprefix tailTrace_3699107
  have hstable : (prefixWord ++ tailWord_3699107).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3699107).length < 2 ^ (prefixWord ++ tailWord_3699107).sum := by decide
  have hdescent : baseEnd_3699107 < baseStart_3699107 := by decide
  rcases family_descends (prefixWord ++ tailWord_3699107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3699109 : List Nat := [1, 3, 1, 2, 1, 1, 3, 2, 9]
def baseStart_3699109 : Nat := 118140960795 + 3699109 * 2 ^ 59
def prefixEnd_3699109 : Nat := 4983230072969 + 3 ^ 40 * 3699109 * 2
def baseEnd_3699109 : Nat := 211046767819163661413957

theorem tailTrace_3699109 : CollatzResearch.WordTrace tailWord_3699109 prefixEnd_3699109 211046767819163661413957 := by
  unfold tailWord_3699109
  simp only [CollatzResearch.WordTrace]
  refine ⟨134917589155767325365524381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89945059437178216910349587 134917589155767325365524381)
  ·
    refine ⟨50594095933412747012071643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 134917589155767325365524381 50594095933412747012071643)
    ·
      refine ⟨75891143900119120518107465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50594095933412747012071643 75891143900119120518107465)
      ·
        refine ⟨56918357925089340388580599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75891143900119120518107465 56918357925089340388580599)
        ·
          refine ⟨85377536887634010582870899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56918357925089340388580599 85377536887634010582870899)
          ·
            refine ⟨128066305331451015874306349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85377536887634010582870899 128066305331451015874306349)
            ·
              refine ⟨48024864499294130952864881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 128066305331451015874306349 48024864499294130952864881)
              ·
                refine ⟨36018648374470598214648661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48024864499294130952864881 36018648374470598214648661)
                ·
                  refine ⟨211046767819163661413957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 36018648374470598214648661 211046767819163661413957)
                  ·
                    rfl

theorem cell23_3699109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 3, 2, 9].length) (baseStart_3699109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3699109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3699109 prefixEnd_3699109 := by exact prefixLift 3699109
  have htrace : WordTrace (prefixWord ++ tailWord_3699109) baseStart_3699109 baseEnd_3699109 := by
    simpa [prefixWord, tailWord_3699109, baseEnd_3699109] using wordTrace_append hprefix tailTrace_3699109
  have hstable : (prefixWord ++ tailWord_3699109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3699109).length < 2 ^ (prefixWord ++ tailWord_3699109).sum := by decide
  have hdescent : baseEnd_3699109 < baseStart_3699109 := by decide
  rcases family_descends (prefixWord ++ tailWord_3699109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3699114 : List Nat := [3, 1, 6, 1, 1, 1, 1, 1, 4, 1, 3]
def baseStart_3699114 : Nat := 118140960795 + 3699114 * 2 ^ 59
def prefixEnd_3699114 : Nat := 4983230072969 + 3 ^ 40 * 3699114 * 2
def baseEnd_3699114 : Nat := 1899423477775745433163091

theorem tailTrace_3699114 : CollatzResearch.WordTrace tailWord_3699114 prefixEnd_3699114 1899423477775745433163091 := by
  unfold tailWord_3699114
  simp only [CollatzResearch.WordTrace]
  refine ⟨33729442880187302804864099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89945181013832807479637597 33729442880187302804864099)
  ·
    refine ⟨50594164320280954207296149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33729442880187302804864099 50594164320280954207296149)
    ·
      refine ⟨2371601452513169728467007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 50594164320280954207296149 2371601452513169728467007)
      ·
        refine ⟨3557402178769754592700511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2371601452513169728467007 3557402178769754592700511)
        ·
          refine ⟨5336103268154631889050767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3557402178769754592700511 5336103268154631889050767)
          ·
            refine ⟨8004154902231947833576151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5336103268154631889050767 8004154902231947833576151)
            ·
              refine ⟨12006232353347921750364227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8004154902231947833576151 12006232353347921750364227)
              ·
                refine ⟨18009348530021882625546341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12006232353347921750364227 18009348530021882625546341)
                ·
                  refine ⟨3376752849379102992289939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18009348530021882625546341 3376752849379102992289939)
                  ·
                    refine ⟨5065129274068654488434909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3376752849379102992289939 5065129274068654488434909)
                    ·
                      refine ⟨1899423477775745433163091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5065129274068654488434909 1899423477775745433163091)
                      ·
                        rfl

theorem cell23_3699114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 1, 1, 1, 4, 1, 3].length) (baseStart_3699114 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3699114 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3699114 prefixEnd_3699114 := by exact prefixLift 3699114
  have htrace : WordTrace (prefixWord ++ tailWord_3699114) baseStart_3699114 baseEnd_3699114 := by
    simpa [prefixWord, tailWord_3699114, baseEnd_3699114] using wordTrace_append hprefix tailTrace_3699114
  have hstable : (prefixWord ++ tailWord_3699114).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3699114).length < 2 ^ (prefixWord ++ tailWord_3699114).sum := by decide
  have hdescent : baseEnd_3699114 < baseStart_3699114 := by decide
  rcases family_descends (prefixWord ++ tailWord_3699114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3699193 : List Nat := [1, 2, 1, 3, 1, 2, 2, 3, 2, 4, 2]
def baseStart_3699193 : Nat := 118140960795 + 3699193 * 2 ^ 59
def prefixEnd_3699193 : Nat := 4983230072969 + 3 ^ 40 * 3699193 * 2
def baseEnd_3699193 : Nat := 1899464042747450624075227

theorem tailTrace_3699193 : CollatzResearch.WordTrace tailWord_3699193 prefixEnd_3699193 1899464042747450624075227 := by
  unfold tailWord_3699193
  simp only [CollatzResearch.WordTrace]
  refine ⟨134920652887463007711582233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89947101924975338474388155 134920652887463007711582233)
  ·
    refine ⟨101190489665597255783686675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134920652887463007711582233 101190489665597255783686675)
    ·
      refine ⟨151785734498395883675530013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101190489665597255783686675 151785734498395883675530013)
      ·
        refine ⟨56919650436898456378323755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 151785734498395883675530013 56919650436898456378323755)
        ·
          refine ⟨85379475655347684567485633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56919650436898456378323755 85379475655347684567485633)
          ·
            refine ⟨64034606741510763425614225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85379475655347684567485633 64034606741510763425614225)
            ·
              refine ⟨48025955056133072569210669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64034606741510763425614225 48025955056133072569210669)
              ·
                refine ⟨18009733146049902213454001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48025955056133072569210669 18009733146049902213454001)
                ·
                  refine ⟨13507299859537426660090501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18009733146049902213454001 13507299859537426660090501)
                  ·
                    refine ⟨2532618723663267498766969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13507299859537426660090501 2532618723663267498766969)
                    ·
                      refine ⟨1899464042747450624075227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2532618723663267498766969 1899464042747450624075227)
                      ·
                        rfl

theorem cell23_3699193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 2, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 2, 3, 2, 4, 2].length) (baseStart_3699193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3699193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3699193 prefixEnd_3699193 := by exact prefixLift 3699193
  have htrace : WordTrace (prefixWord ++ tailWord_3699193) baseStart_3699193 baseEnd_3699193 := by
    simpa [prefixWord, tailWord_3699193, baseEnd_3699193] using wordTrace_append hprefix tailTrace_3699193
  have hstable : (prefixWord ++ tailWord_3699193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3699193).length < 2 ^ (prefixWord ++ tailWord_3699193).sum := by decide
  have hdescent : baseEnd_3699193 < baseStart_3699193 := by decide
  rcases family_descends (prefixWord ++ tailWord_3699193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3699233 : List Nat := [1, 2, 3, 2, 2, 1, 4, 2, 6]
def baseStart_3699233 : Nat := 118140960795 + 3699233 * 2 ^ 59
def prefixEnd_3699233 : Nat := 4983230072969 + 3 ^ 40 * 3699233 * 2
def baseEnd_3699233 : Nat := 211053842441514496397227

theorem tailTrace_3699233 : CollatzResearch.WordTrace tailWord_3699233 prefixEnd_3699233 211053842441514496397227 := by
  unfold tailWord_3699233
  simp only [CollatzResearch.WordTrace]
  refine ⟨134922111807318094543038353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89948074538212063028692235 134922111807318094543038353)
  ·
    refine ⟨101191583855488570907278765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134922111807318094543038353 101191583855488570907278765)
    ·
      refine ⟨37946843945808214090229537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 101191583855488570907278765 37946843945808214090229537)
      ·
        refine ⟨28460132959356160567672153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37946843945808214090229537 28460132959356160567672153)
        ·
          refine ⟨21345099719517120425754115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28460132959356160567672153 21345099719517120425754115)
          ·
            refine ⟨32017649579275680638631173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21345099719517120425754115 32017649579275680638631173)
            ·
              refine ⟨6003309296114190119743345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32017649579275680638631173 6003309296114190119743345)
              ·
                refine ⟨4502481972085642589807509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6003309296114190119743345 4502481972085642589807509)
                ·
                  refine ⟨211053842441514496397227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4502481972085642589807509 211053842441514496397227)
                  ·
                    rfl

theorem cell23_3699233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 4, 2, 6].length) (baseStart_3699233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3699233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3699233 prefixEnd_3699233 := by exact prefixLift 3699233
  have htrace : WordTrace (prefixWord ++ tailWord_3699233) baseStart_3699233 baseEnd_3699233 := by
    simpa [prefixWord, tailWord_3699233, baseEnd_3699233] using wordTrace_append hprefix tailTrace_3699233
  have hstable : (prefixWord ++ tailWord_3699233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3699233).length < 2 ^ (prefixWord ++ tailWord_3699233).sum := by decide
  have hdescent : baseEnd_3699233 < baseStart_3699233 := by decide
  rcases family_descends (prefixWord ++ tailWord_3699233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3699237 : List Nat := [1, 3, 1, 2, 2, 1, 6, 2, 1, 4]
def baseStart_3699237 : Nat := 118140960795 + 3699237 * 2 ^ 59
def prefixEnd_3699237 : Nat := 4983230072969 + 3 ^ 40 * 3699237 * 2
def baseEnd_3699237 : Nat := 633162211965416150641675

theorem tailTrace_3699237 : CollatzResearch.WordTrace tailWord_3699237 prefixEnd_3699237 633162211965416150641675 := by
  unfold tailWord_3699237
  simp only [CollatzResearch.WordTrace]
  refine ⟨134922257699303603226183965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89948171799535735484122643 134922257699303603226183965)
  ·
    refine ⟨50595846637238851209818987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 134922257699303603226183965 50595846637238851209818987)
    ·
      refine ⟨75893769955858276814728481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50595846637238851209818987 75893769955858276814728481)
      ·
        refine ⟨56920327466893707611046361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75893769955858276814728481 56920327466893707611046361)
        ·
          refine ⟨42690245600170280708284771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56920327466893707611046361 42690245600170280708284771)
          ·
            refine ⟨64035368400255421062427157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42690245600170280708284771 64035368400255421062427157)
            ·
              refine ⟨3001657893761972862301273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 64035368400255421062427157 3001657893761972862301273)
              ·
                refine ⟨2251243420321479646725955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3001657893761972862301273 2251243420321479646725955)
                ·
                  refine ⟨3376865130482219470088933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2251243420321479646725955 3376865130482219470088933)
                  ·
                    refine ⟨633162211965416150641675, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3376865130482219470088933 633162211965416150641675)
                    ·
                      rfl

theorem cell23_3699237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 6, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 6, 2, 1, 4].length) (baseStart_3699237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3699237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3699237 prefixEnd_3699237 := by exact prefixLift 3699237
  have htrace : WordTrace (prefixWord ++ tailWord_3699237) baseStart_3699237 baseEnd_3699237 := by
    simpa [prefixWord, tailWord_3699237, baseEnd_3699237] using wordTrace_append hprefix tailTrace_3699237
  have hstable : (prefixWord ++ tailWord_3699237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3699237).length < 2 ^ (prefixWord ++ tailWord_3699237).sum := by decide
  have hdescent : baseEnd_3699237 < baseStart_3699237 := by decide
  rcases family_descends (prefixWord ++ tailWord_3699237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3699243 : List Nat := [1, 1, 1, 1, 2, 1, 3, 2, 7, 1, 3]
def baseStart_3699243 : Nat := 118140960795 + 3699243 * 2 ^ 59
def prefixEnd_3699243 : Nat := 4983230072969 + 3 ^ 40 * 3699243 * 2
def baseEnd_3699243 : Nat := 1899489716780175428449997

theorem tailTrace_3699243 : CollatzResearch.WordTrace tailWord_3699243 prefixEnd_3699243 1899489716780175428449997 := by
  unfold tailWord_3699243
  simp only [CollatzResearch.WordTrace]
  refine ⟨134922476537281866250902383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89948317691521244167268255 134922476537281866250902383)
  ·
    refine ⟨202383714805922799376353575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134922476537281866250902383 202383714805922799376353575)
    ·
      refine ⟨303575572208884199064530363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 202383714805922799376353575 303575572208884199064530363)
      ·
        refine ⟨455363358313326298596795545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 303575572208884199064530363 455363358313326298596795545)
        ·
          refine ⟨341522518734994723947596659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 455363358313326298596795545 341522518734994723947596659)
          ·
            refine ⟨512283778102492085921394989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 341522518734994723947596659 512283778102492085921394989)
            ·
              refine ⟨192106416788434532220523121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 512283778102492085921394989 192106416788434532220523121)
              ·
                refine ⟨144079812591325899165392341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 192106416788434532220523121 144079812591325899165392341)
                ·
                  refine ⟨3376870607609200761688883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 144079812591325899165392341 3376870607609200761688883)
                  ·
                    refine ⟨5065305911413801142533325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3376870607609200761688883 5065305911413801142533325)
                    ·
                      refine ⟨1899489716780175428449997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5065305911413801142533325 1899489716780175428449997)
                      ·
                        rfl

theorem cell23_3699243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 2, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 2, 7, 1, 3].length) (baseStart_3699243 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3699243 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3699243 prefixEnd_3699243 := by exact prefixLift 3699243
  have htrace : WordTrace (prefixWord ++ tailWord_3699243) baseStart_3699243 baseEnd_3699243 := by
    simpa [prefixWord, tailWord_3699243, baseEnd_3699243] using wordTrace_append hprefix tailTrace_3699243
  have hstable : (prefixWord ++ tailWord_3699243).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3699243).length < 2 ^ (prefixWord ++ tailWord_3699243).sum := by decide
  have hdescent : baseEnd_3699243 < baseStart_3699243 := by decide
  rcases family_descends (prefixWord ++ tailWord_3699243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3699256 : List Nat := [2, 1, 2, 1, 4, 1, 1, 1, 2, 1, 7]
def baseStart_3699256 : Nat := 118140960795 + 3699256 * 2 ^ 59
def prefixEnd_3699256 : Nat := 4983230072969 + 3 ^ 40 * 3699256 * 2
def baseEnd_3699256 : Nat := 1899496392028683877587437

theorem tailTrace_3699256 : CollatzResearch.WordTrace tailWord_3699256 prefixEnd_3699256 1899496392028683877587437 := by
  unfold tailWord_3699256
  simp only [CollatzResearch.WordTrace]
  refine ⟨67461475343117384735562811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89948633790823179647417081 67461475343117384735562811)
  ·
    refine ⟨101192213014676077103344217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67461475343117384735562811 101192213014676077103344217)
    ·
      refine ⟨75894159761007057827508163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101192213014676077103344217 75894159761007057827508163)
      ·
        refine ⟨113841239641510586741262245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75894159761007057827508163 113841239641510586741262245)
        ·
          refine ⟨21345232432783235013986671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 113841239641510586741262245 21345232432783235013986671)
          ·
            refine ⟨32017848649174852520980007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21345232432783235013986671 32017848649174852520980007)
            ·
              refine ⟨48026772973762278781470011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32017848649174852520980007 48026772973762278781470011)
              ·
                refine ⟨72040159460643418172205017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48026772973762278781470011 72040159460643418172205017)
                ·
                  refine ⟨54030119595482563629153763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 72040159460643418172205017 54030119595482563629153763)
                  ·
                    refine ⟨81045179393223845443730645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 54030119595482563629153763 81045179393223845443730645)
                    ·
                      refine ⟨1899496392028683877587437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 81045179393223845443730645 1899496392028683877587437)
                      ·
                        rfl

theorem cell23_3699256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 1, 1, 2, 1, 7].length) (baseStart_3699256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3699256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3699256 prefixEnd_3699256 := by exact prefixLift 3699256
  have htrace : WordTrace (prefixWord ++ tailWord_3699256) baseStart_3699256 baseEnd_3699256 := by
    simpa [prefixWord, tailWord_3699256, baseEnd_3699256] using wordTrace_append hprefix tailTrace_3699256
  have hstable : (prefixWord ++ tailWord_3699256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3699256).length < 2 ^ (prefixWord ++ tailWord_3699256).sum := by decide
  have hdescent : baseEnd_3699256 < baseStart_3699256 := by decide
  rcases family_descends (prefixWord ++ tailWord_3699256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3699260 : List Nat := [2, 2, 2, 2, 3, 1, 1, 1, 5, 1, 3]
def baseStart_3699260 : Nat := 118140960795 + 3699260 * 2 ^ 59
def prefixEnd_3699260 : Nat := 4983230072969 + 3 ^ 40 * 3699260 * 2
def baseEnd_3699260 : Nat := 1899498445951301861937419

theorem tailTrace_3699260 : CollatzResearch.WordTrace tailWord_3699260 prefixEnd_3699260 1899498445951301861937419 := by
  unfold tailWord_3699260
  simp only [CollatzResearch.WordTrace]
  refine ⟨67461548289110139077135617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89948731052146852102847489 67461548289110139077135617)
  ·
    refine ⟨50596161216832604307851713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67461548289110139077135617 50596161216832604307851713)
    ·
      refine ⟨37947120912624453230888785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50596161216832604307851713 37947120912624453230888785)
      ·
        refine ⟨28460340684468339923166589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37947120912624453230888785 28460340684468339923166589)
        ·
          refine ⟨10672627756675627471187471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28460340684468339923166589 10672627756675627471187471)
          ·
            refine ⟨16008941635013441206781207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10672627756675627471187471 16008941635013441206781207)
            ·
              refine ⟨24013412452520161810171811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16008941635013441206781207 24013412452520161810171811)
              ·
                refine ⟨36020118678780242715257717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24013412452520161810171811 36020118678780242715257717)
                ·
                  refine ⟨3376886126135647754555411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 36020118678780242715257717 3376886126135647754555411)
                  ·
                    refine ⟨5065329189203471631833117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3376886126135647754555411 5065329189203471631833117)
                    ·
                      refine ⟨1899498445951301861937419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5065329189203471631833117 1899498445951301861937419)
                      ·
                        rfl

theorem cell23_3699260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 1, 1, 5, 1, 3].length) (baseStart_3699260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3699260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3699260 prefixEnd_3699260 := by exact prefixLift 3699260
  have htrace : WordTrace (prefixWord ++ tailWord_3699260) baseStart_3699260 baseEnd_3699260 := by
    simpa [prefixWord, tailWord_3699260, baseEnd_3699260] using wordTrace_append hprefix tailTrace_3699260
  have hstable : (prefixWord ++ tailWord_3699260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3699260).length < 2 ^ (prefixWord ++ tailWord_3699260).sum := by decide
  have hdescent : baseEnd_3699260 < baseStart_3699260 := by decide
  rcases family_descends (prefixWord ++ tailWord_3699260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3699263 : List Nat := [1, 1, 2, 2, 3, 2, 2, 4, 1, 5]
def baseStart_3699263 : Nat := 118140960795 + 3699263 * 2 ^ 59
def prefixEnd_3699263 : Nat := 4983230072969 + 3 ^ 40 * 3699263 * 2
def baseEnd_3699263 : Nat := 633166662131088450066635

theorem tailTrace_3699263 : CollatzResearch.WordTrace tailWord_3699263 prefixEnd_3699263 633166662131088450066635 := by
  unfold tailWord_3699263
  simp only [CollatzResearch.WordTrace]
  refine ⟨134923205997209409666630443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89948803998139606444420295 134923205997209409666630443)
  ·
    refine ⟨202384808995814114499945665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134923205997209409666630443 202384808995814114499945665)
    ·
      refine ⟨151788606746860585874959249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 202384808995814114499945665 151788606746860585874959249)
      ·
        refine ⟨113841455060145439406219437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 151788606746860585874959249 113841455060145439406219437)
        ·
          refine ⟨42690545647554539777332289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 113841455060145439406219437 42690545647554539777332289)
          ·
            refine ⟨32017909235665904832999217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42690545647554539777332289 32017909235665904832999217)
            ·
              refine ⟨24013431926749428624749413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32017909235665904832999217 24013431926749428624749413)
              ·
                refine ⟨4502518486265517867140515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24013431926749428624749413 4502518486265517867140515)
                ·
                  refine ⟨6753777729398276800710773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4502518486265517867140515 6753777729398276800710773)
                  ·
                    refine ⟨633166662131088450066635, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6753777729398276800710773 633166662131088450066635)
                    ·
                      rfl

theorem cell23_3699263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 2, 4, 1, 5].length) (baseStart_3699263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3699263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3699263 prefixEnd_3699263 := by exact prefixLift 3699263
  have htrace : WordTrace (prefixWord ++ tailWord_3699263) baseStart_3699263 baseEnd_3699263 := by
    simpa [prefixWord, tailWord_3699263, baseEnd_3699263] using wordTrace_append hprefix tailTrace_3699263
  have hstable : (prefixWord ++ tailWord_3699263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3699263).length < 2 ^ (prefixWord ++ tailWord_3699263).sum := by decide
  have hdescent : baseEnd_3699263 < baseStart_3699263 := by decide
  rcases family_descends (prefixWord ++ tailWord_3699263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3699310 : List Nat := [4, 1, 2, 2, 2, 1, 3, 1, 1, 6]
def baseStart_3699310 : Nat := 118140960795 + 3699310 * 2 ^ 59
def prefixEnd_3699310 : Nat := 4983230072969 + 3 ^ 40 * 3699310 * 2
def baseEnd_3699310 : Nat := 633174706661342222104063

theorem tailTrace_3699310 : CollatzResearch.WordTrace tailWord_3699310 prefixEnd_3699310 633174706661342222104063 := by
  unfold tailWord_3699310
  simp only [CollatzResearch.WordTrace]
  refine ⟨16865615028504892086698923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 89949946818692757795727589 16865615028504892086698923)
  ·
    refine ⟨25298422542757338130048385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16865615028504892086698923 25298422542757338130048385)
    ·
      refine ⟨18973816907068003597536289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25298422542757338130048385 18973816907068003597536289)
      ·
        refine ⟨14230362680301002698152217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18973816907068003597536289 14230362680301002698152217)
        ·
          refine ⟨10672772010225752023614163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14230362680301002698152217 10672772010225752023614163)
          ·
            refine ⟨16009158015338628035421245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10672772010225752023614163 16009158015338628035421245)
            ·
              refine ⟨6003434255751985513282967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16009158015338628035421245 6003434255751985513282967)
              ·
                refine ⟨9005151383627978269924451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6003434255751985513282967 9005151383627978269924451)
                ·
                  refine ⟨13507727075441967404886677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9005151383627978269924451 13507727075441967404886677)
                  ·
                    refine ⟨633174706661342222104063, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13507727075441967404886677 633174706661342222104063)
                    ·
                      rfl

theorem cell23_3699310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 3, 1, 1, 6].length) (baseStart_3699310 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3699310 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3699310 prefixEnd_3699310 := by exact prefixLift 3699310
  have htrace : WordTrace (prefixWord ++ tailWord_3699310) baseStart_3699310 baseEnd_3699310 := by
    simpa [prefixWord, tailWord_3699310, baseEnd_3699310] using wordTrace_append hprefix tailTrace_3699310
  have hstable : (prefixWord ++ tailWord_3699310).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3699310).length < 2 ^ (prefixWord ++ tailWord_3699310).sum := by decide
  have hdescent : baseEnd_3699310 < baseStart_3699310 := by decide
  rcases family_descends (prefixWord ++ tailWord_3699310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3699351 : List Nat := [1, 1, 3, 3, 2, 1, 5, 2, 1, 2, 2]
def baseStart_3699351 : Nat := 118140960795 + 3699351 * 2 ^ 59
def prefixEnd_3699351 : Nat := 4983230072969 + 3 ^ 40 * 3699351 * 2
def baseEnd_3699351 : Nat := 1899545172690861005899501

theorem tailTrace_3699351 : CollatzResearch.WordTrace tailWord_3699351 prefixEnd_3699351 1899545172690861005899501 := by
  unfold tailWord_3699351
  simp only [CollatzResearch.WordTrace]
  refine ⟨134926415620890600695833907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89950943747260400463889271 134926415620890600695833907)
  ·
    refine ⟨202389623431335901043750861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134926415620890600695833907 202389623431335901043750861)
    ·
      refine ⟨75896108786750962891406573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 202389623431335901043750861 75896108786750962891406573)
      ·
        refine ⟨28461040795031611084277465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 75896108786750962891406573 28461040795031611084277465)
        ·
          refine ⟨21345780596273708313208099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28461040795031611084277465 21345780596273708313208099)
          ·
            refine ⟨32018670894410562469812149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21345780596273708313208099 32018670894410562469812149)
            ·
              refine ⟨3001750396350990231544889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 32018670894410562469812149 3001750396350990231544889)
              ·
                refine ⟨2251312797263242673658667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3001750396350990231544889 2251312797263242673658667)
                ·
                  refine ⟨3376969195894864010488001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2251312797263242673658667 3376969195894864010488001)
                  ·
                    refine ⟨2532726896921148007866001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3376969195894864010488001 2532726896921148007866001)
                    ·
                      refine ⟨1899545172690861005899501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2532726896921148007866001 1899545172690861005899501)
                      ·
                        rfl

theorem cell23_3699351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 5, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 5, 2, 1, 2, 2].length) (baseStart_3699351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3699351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3699351 prefixEnd_3699351 := by exact prefixLift 3699351
  have htrace : WordTrace (prefixWord ++ tailWord_3699351) baseStart_3699351 baseEnd_3699351 := by
    simpa [prefixWord, tailWord_3699351, baseEnd_3699351] using wordTrace_append hprefix tailTrace_3699351
  have hstable : (prefixWord ++ tailWord_3699351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3699351).length < 2 ^ (prefixWord ++ tailWord_3699351).sum := by decide
  have hdescent : baseEnd_3699351 < baseStart_3699351 := by decide
  rcases family_descends (prefixWord ++ tailWord_3699351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3699361 : List Nat := [1, 2, 3, 3, 4, 1, 2, 1, 2, 4]
def baseStart_3699361 : Nat := 118140960795 + 3699361 * 2 ^ 59
def prefixEnd_3699361 : Nat := 4983230072969 + 3 ^ 40 * 3699361 * 2
def baseEnd_3699361 : Nat := 633183435832468655591485

theorem tailTrace_3699361 : CollatzResearch.WordTrace tailWord_3699361 prefixEnd_3699361 633183435832468655591485 := by
  unfold tailWord_3699361
  simp only [CollatzResearch.WordTrace]
  refine ⟨134926780350854372403697937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89951186900569581602465291 134926780350854372403697937)
  ·
    refine ⟨101195085263140779302773453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134926780350854372403697937 101195085263140779302773453)
    ·
      refine ⟨37948156973677792238540045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 101195085263140779302773453 37948156973677792238540045)
      ·
        refine ⟨14230558865129172089452517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37948156973677792238540045 14230558865129172089452517)
        ·
          refine ⟨2668229787211719766772347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14230558865129172089452517 2668229787211719766772347)
          ·
            refine ⟨4002344680817579650158521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2668229787211719766772347 4002344680817579650158521)
            ·
              refine ⟨3001758510613184737618891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4002344680817579650158521 3001758510613184737618891)
              ·
                refine ⟨4502637765919777106428337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3001758510613184737618891 4502637765919777106428337)
                ·
                  refine ⟨3376978324439832829821253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4502637765919777106428337 3376978324439832829821253)
                  ·
                    refine ⟨633183435832468655591485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3376978324439832829821253 633183435832468655591485)
                    ·
                      rfl

theorem cell23_3699361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 4, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 4, 1, 2, 1, 2, 4].length) (baseStart_3699361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3699361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3699361 prefixEnd_3699361 := by exact prefixLift 3699361
  have htrace : WordTrace (prefixWord ++ tailWord_3699361) baseStart_3699361 baseEnd_3699361 := by
    simpa [prefixWord, tailWord_3699361, baseEnd_3699361] using wordTrace_append hprefix tailTrace_3699361
  have hstable : (prefixWord ++ tailWord_3699361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3699361).length < 2 ^ (prefixWord ++ tailWord_3699361).sum := by decide
  have hdescent : baseEnd_3699361 < baseStart_3699361 := by decide
  rcases family_descends (prefixWord ++ tailWord_3699361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3699458 : List Nat := [3, 4, 1, 1, 1, 4, 1, 2, 2, 2, 2]
def baseStart_3699458 : Nat := 118140960795 + 3699458 * 2 ^ 59
def prefixEnd_3699458 : Nat := 4983230072969 + 3 ^ 40 * 3699458 * 2
def baseEnd_3699458 : Nat := 1899600115120892087261509

theorem tailTrace_3699458 : CollatzResearch.WordTrace tailWord_3699458 prefixEnd_3699458 1899600115120892087261509 := by
  unfold tailWord_3699458
  simp only [CollatzResearch.WordTrace]
  refine ⟨33732579557875739492494757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89953545487668638646652685 33732579557875739492494757)
  ·
    refine ⟨6324858667101701154842767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 33732579557875739492494757 6324858667101701154842767)
    ·
      refine ⟨9487288000652551732264151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6324858667101701154842767 9487288000652551732264151)
      ·
        refine ⟨14230932000978827598396227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9487288000652551732264151 14230932000978827598396227)
        ·
          refine ⟨21346398001468241397594341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14230932000978827598396227 21346398001468241397594341)
          ·
            refine ⟨4002449625275295262048939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21346398001468241397594341 4002449625275295262048939)
            ·
              refine ⟨6003674437912942893073409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4002449625275295262048939 6003674437912942893073409)
              ·
                refine ⟨4502755828434707169805057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6003674437912942893073409 4502755828434707169805057)
                ·
                  refine ⟨3377066871326030377353793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4502755828434707169805057 3377066871326030377353793)
                  ·
                    refine ⟨2532800153494522783015345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3377066871326030377353793 2532800153494522783015345)
                    ·
                      refine ⟨1899600115120892087261509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2532800153494522783015345 1899600115120892087261509)
                      ·
                        rfl

theorem cell23_3699458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 4, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 4, 1, 2, 2, 2, 2].length) (baseStart_3699458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3699458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3699458 prefixEnd_3699458 := by exact prefixLift 3699458
  have htrace : WordTrace (prefixWord ++ tailWord_3699458) baseStart_3699458 baseEnd_3699458 := by
    simpa [prefixWord, tailWord_3699458, baseEnd_3699458] using wordTrace_append hprefix tailTrace_3699458
  have hstable : (prefixWord ++ tailWord_3699458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3699458).length < 2 ^ (prefixWord ++ tailWord_3699458).sum := by decide
  have hdescent : baseEnd_3699458 < baseStart_3699458 := by decide
  rcases family_descends (prefixWord ++ tailWord_3699458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3699460 : List Nat := [2, 3, 2, 2, 1, 1, 2, 1, 4, 5]
def baseStart_3699460 : Nat := 118140960795 + 3699460 * 2 ^ 59
def prefixEnd_3699460 : Nat := 4983230072969 + 3 ^ 40 * 3699460 * 2
def baseEnd_3699460 : Nat := 633200380694067026478833

theorem tailTrace_3699460 : CollatzResearch.WordTrace tailWord_3699460 prefixEnd_3699460 633200380694067026478833 := by
  unfold tailWord_3699460
  simp only [CollatzResearch.WordTrace]
  refine ⟨67465195588747856155775917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89953594118330474874367889 67465195588747856155775917)
  ·
    refine ⟨25299448345780446058415969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67465195588747856155775917 25299448345780446058415969)
    ·
      refine ⟨18974586259335334543811977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25299448345780446058415969 18974586259335334543811977)
      ·
        refine ⟨14230939694501500907858983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18974586259335334543811977 14230939694501500907858983)
        ·
          refine ⟨21346409541752251361788475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14230939694501500907858983 21346409541752251361788475)
          ·
            refine ⟨32019614312628377042682713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21346409541752251361788475 32019614312628377042682713)
            ·
              refine ⟨24014710734471282782012035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32019614312628377042682713 24014710734471282782012035)
              ·
                refine ⟨36022066101706924173018053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24014710734471282782012035 36022066101706924173018053)
                ·
                  refine ⟨6754137394070048282440885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36022066101706924173018053 6754137394070048282440885)
                  ·
                    refine ⟨633200380694067026478833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6754137394070048282440885 633200380694067026478833)
                    ·
                      rfl

theorem cell23_3699460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 2, 1, 4, 5].length) (baseStart_3699460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3699460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3699460 prefixEnd_3699460 := by exact prefixLift 3699460
  have htrace : WordTrace (prefixWord ++ tailWord_3699460) baseStart_3699460 baseEnd_3699460 := by
    simpa [prefixWord, tailWord_3699460, baseEnd_3699460] using wordTrace_append hprefix tailTrace_3699460
  have hstable : (prefixWord ++ tailWord_3699460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3699460).length < 2 ^ (prefixWord ++ tailWord_3699460).sum := by decide
  have hdescent : baseEnd_3699460 < baseStart_3699460 := by decide
  rcases family_descends (prefixWord ++ tailWord_3699460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3699498 : List Nat := [3, 1, 4, 3, 2, 1, 1, 3, 5]
def baseStart_3699498 : Nat := 118140960795 + 3699498 * 2 ^ 59
def prefixEnd_3699498 : Nat := 4983230072969 + 3 ^ 40 * 3699498 * 2
def baseEnd_3699498 : Nat := 211068961594119103417925

theorem tailTrace_3699498 : CollatzResearch.WordTrace tailWord_3699498 prefixEnd_3699498 211068961594119103417925 := by
  unfold tailWord_3699498
  simp only [CollatzResearch.WordTrace]
  refine ⟨33732944287839511200358787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89954518100905363200956765 33732944287839511200358787)
  ·
    refine ⟨50599416431759266800538181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33732944287839511200358787 50599416431759266800538181)
    ·
      refine ⟨9487390580954862525100909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 50599416431759266800538181 9487390580954862525100909)
      ·
        refine ⟨3557771467858073446912841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9487390580954862525100909 3557771467858073446912841)
        ·
          refine ⟨2668328600893555085184631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3557771467858073446912841 2668328600893555085184631)
          ·
            refine ⟨4002492901340332627776947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2668328600893555085184631 4002492901340332627776947)
            ·
              refine ⟨6003739352010498941665421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4002492901340332627776947 6003739352010498941665421)
              ·
                refine ⟨2251402257003937103124533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6003739352010498941665421 2251402257003937103124533)
                ·
                  refine ⟨211068961594119103417925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2251402257003937103124533 211068961594119103417925)
                  ·
                    rfl

theorem cell23_3699498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 2, 1, 1, 3, 5].length) (baseStart_3699498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3699498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3699498 prefixEnd_3699498 := by exact prefixLift 3699498
  have htrace : WordTrace (prefixWord ++ tailWord_3699498) baseStart_3699498 baseEnd_3699498 := by
    simpa [prefixWord, tailWord_3699498, baseEnd_3699498] using wordTrace_append hprefix tailTrace_3699498
  have hstable : (prefixWord ++ tailWord_3699498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3699498).length < 2 ^ (prefixWord ++ tailWord_3699498).sum := by decide
  have hdescent : baseEnd_3699498 < baseStart_3699498 := by decide
  rcases family_descends (prefixWord ++ tailWord_3699498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3699500 : List Nat := [2, 2, 1, 1, 1, 4, 1, 3, 1, 4, 3]
def baseStart_3699500 : Nat := 118140960795 + 3699500 * 2 ^ 59
def prefixEnd_3699500 : Nat := 4983230072969 + 3 ^ 40 * 3699500 * 2
def baseEnd_3699500 : Nat := 1899621681308380922936315

theorem tailTrace_3699500 : CollatzResearch.WordTrace tailWord_3699500 prefixEnd_3699500 1899621681308380922936315 := by
  unfold tailWord_3699500
  simp only [CollatzResearch.WordTrace]
  refine ⟨67465925048675399571503977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89954566731567199428671969 67465925048675399571503977)
  ·
    refine ⟨50599443786506549678627983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67465925048675399571503977 50599443786506549678627983)
    ·
      refine ⟨75899165679759824517941975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50599443786506549678627983 75899165679759824517941975)
      ·
        refine ⟨113848748519639736776912963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75899165679759824517941975 113848748519639736776912963)
        ·
          refine ⟨170773122779459605165369445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113848748519639736776912963 170773122779459605165369445)
          ·
            refine ⟨32019960521148675968506771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 170773122779459605165369445 32019960521148675968506771)
            ·
              refine ⟨48029940781723013952760157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32019960521148675968506771 48029940781723013952760157)
              ·
                refine ⟨18011227793146130232285059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48029940781723013952760157 18011227793146130232285059)
                ·
                  refine ⟨27016841689719195348427589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18011227793146130232285059 27016841689719195348427589)
                  ·
                    refine ⟨5065657816822349127830173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27016841689719195348427589 5065657816822349127830173)
                    ·
                      refine ⟨1899621681308380922936315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5065657816822349127830173 1899621681308380922936315)
                      ·
                        rfl

theorem cell23_3699500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 4, 3].length) (baseStart_3699500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3699500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3699500 prefixEnd_3699500 := by exact prefixLift 3699500
  have htrace : WordTrace (prefixWord ++ tailWord_3699500) baseStart_3699500 baseEnd_3699500 := by
    simpa [prefixWord, tailWord_3699500, baseEnd_3699500] using wordTrace_append hprefix tailTrace_3699500
  have hstable : (prefixWord ++ tailWord_3699500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3699500).length < 2 ^ (prefixWord ++ tailWord_3699500).sum := by decide
  have hdescent : baseEnd_3699500 < baseStart_3699500 := by decide
  rcases family_descends (prefixWord ++ tailWord_3699500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3699530 : List Nat := [3, 1, 2, 1, 1, 1, 2, 2, 2, 5, 3]
def baseStart_3699530 : Nat := 118140960795 + 3699530 * 2 ^ 59
def prefixEnd_3699530 : Nat := 4983230072969 + 3 ^ 40 * 3699530 * 2
def baseEnd_3699530 : Nat := 1899637085728015805561177

theorem tailTrace_3699530 : CollatzResearch.WordTrace tailWord_3699530 prefixEnd_3699530 1899637085728015805561177 := by
  unfold tailWord_3699530
  simp only [CollatzResearch.WordTrace]
  refine ⟨33733236071810528566650011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89955296191494742844400029 33733236071810528566650011)
  ·
    refine ⟨50599854107715792849975017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33733236071810528566650011 50599854107715792849975017)
    ·
      refine ⟨37949890580786844637481263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50599854107715792849975017 37949890580786844637481263)
      ·
        refine ⟨56924835871180266956221895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37949890580786844637481263 56924835871180266956221895)
        ·
          refine ⟨85387253806770400434332843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56924835871180266956221895 85387253806770400434332843)
          ·
            refine ⟨128080880710155600651499265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85387253806770400434332843 128080880710155600651499265)
            ·
              refine ⟨96060660532616700488624449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 128080880710155600651499265 96060660532616700488624449)
              ·
                refine ⟨72045495399462525366468337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 96060660532616700488624449 72045495399462525366468337)
                ·
                  refine ⟨54034121549596894024851253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 72045495399462525366468337 54034121549596894024851253)
                  ·
                    refine ⟨5065698895274708814829805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 54034121549596894024851253 5065698895274708814829805)
                    ·
                      refine ⟨1899637085728015805561177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5065698895274708814829805 1899637085728015805561177)
                      ·
                        rfl

theorem cell23_3699530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 2, 2, 5, 3].length) (baseStart_3699530 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3699530 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3699530 prefixEnd_3699530 := by exact prefixLift 3699530
  have htrace : WordTrace (prefixWord ++ tailWord_3699530) baseStart_3699530 baseEnd_3699530 := by
    simpa [prefixWord, tailWord_3699530, baseEnd_3699530] using wordTrace_append hprefix tailTrace_3699530
  have hstable : (prefixWord ++ tailWord_3699530).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3699530).length < 2 ^ (prefixWord ++ tailWord_3699530).sum := by decide
  have hdescent : baseEnd_3699530 < baseStart_3699530 := by decide
  rcases family_descends (prefixWord ++ tailWord_3699530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3699537 : List Nat := [1, 2, 2, 1, 6, 1, 1, 3, 6]
def baseStart_3699537 : Nat := 118140960795 + 3699537 * 2 ^ 59
def prefixEnd_3699537 : Nat := 4983230072969 + 3 ^ 40 * 3699537 * 2
def baseEnd_3699537 : Nat := 211071186676955253130405

theorem tailTrace_3699537 : CollatzResearch.WordTrace tailWord_3699537 prefixEnd_3699537 211071186676955253130405 := by
  unfold tailWord_3699537
  simp only [CollatzResearch.WordTrace]
  refine ⟨134933199598216754462104865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89955466398811169641403243 134933199598216754462104865)
  ·
    refine ⟨101199899698662565846578649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134933199598216754462104865 101199899698662565846578649)
    ·
      refine ⟨75899924773996924384933987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101199899698662565846578649 75899924773996924384933987)
      ·
        refine ⟨113849887160995386577400981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75899924773996924384933987 113849887160995386577400981)
        ·
          refine ⟨5336713460671658745815671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 113849887160995386577400981 5336713460671658745815671)
          ·
            refine ⟨8005070191007488118723507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5336713460671658745815671 8005070191007488118723507)
            ·
              refine ⟨12007605286511232178085261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8005070191007488118723507 12007605286511232178085261)
              ·
                refine ⟨4502851982441712066781973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12007605286511232178085261 4502851982441712066781973)
                ·
                  refine ⟨211071186676955253130405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4502851982441712066781973 211071186676955253130405)
                  ·
                    rfl

theorem cell23_3699537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 1, 1, 3, 6].length) (baseStart_3699537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3699537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3699537 prefixEnd_3699537 := by exact prefixLift 3699537
  have htrace : WordTrace (prefixWord ++ tailWord_3699537) baseStart_3699537 baseEnd_3699537 := by
    simpa [prefixWord, tailWord_3699537, baseEnd_3699537] using wordTrace_append hprefix tailTrace_3699537
  have hstable : (prefixWord ++ tailWord_3699537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3699537).length < 2 ^ (prefixWord ++ tailWord_3699537).sum := by decide
  have hdescent : baseEnd_3699537 < baseStart_3699537 := by decide
  rcases family_descends (prefixWord ++ tailWord_3699537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3699557 : List Nat := [1, 3, 1, 3, 1, 1, 2, 3, 1, 5, 2]
def baseStart_3699557 : Nat := 118140960795 + 3699557 * 2 ^ 59
def prefixEnd_3699557 : Nat := 4983230072969 + 3 ^ 40 * 3699557 * 2
def baseEnd_3699557 : Nat := 1899650949705687199923553

theorem tailTrace_3699557 : CollatzResearch.WordTrace tailWord_3699557 prefixEnd_3699557 1899650949705687199923553 := by
  unfold tailWord_3699557
  simp only [CollatzResearch.WordTrace]
  refine ⟨134933929058144297877832925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89955952705429531918555283 134933929058144297877832925)
  ·
    refine ⟨50600223396804111704187347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 134933929058144297877832925 50600223396804111704187347)
    ·
      refine ⟨75900335095206167556281021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50600223396804111704187347 75900335095206167556281021)
      ·
        refine ⟨28462625660702312833605383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 75900335095206167556281021 28462625660702312833605383)
        ·
          refine ⟨42693938491053469250408075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28462625660702312833605383 42693938491053469250408075)
          ·
            refine ⟨64040907736580203875612113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42693938491053469250408075 64040907736580203875612113)
            ·
              refine ⟨48030680802435152906709085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64040907736580203875612113 48030680802435152906709085)
              ·
                refine ⟨18011505300913182340015907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48030680802435152906709085 18011505300913182340015907)
                ·
                  refine ⟨27017257951369773510023861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18011505300913182340015907 27017257951369773510023861)
                  ·
                    refine ⟨2532867932940916266564737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 27017257951369773510023861 2532867932940916266564737)
                    ·
                      refine ⟨1899650949705687199923553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2532867932940916266564737 1899650949705687199923553)
                      ·
                        rfl

theorem cell23_3699557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 2, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 2, 3, 1, 5, 2].length) (baseStart_3699557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3699557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3699557 prefixEnd_3699557 := by exact prefixLift 3699557
  have htrace : WordTrace (prefixWord ++ tailWord_3699557) baseStart_3699557 baseEnd_3699557 := by
    simpa [prefixWord, tailWord_3699557, baseEnd_3699557] using wordTrace_append hprefix tailTrace_3699557
  have hstable : (prefixWord ++ tailWord_3699557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3699557).length < 2 ^ (prefixWord ++ tailWord_3699557).sum := by decide
  have hdescent : baseEnd_3699557 < baseStart_3699557 := by decide
  rcases family_descends (prefixWord ++ tailWord_3699557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3699604 : List Nat := [2, 4, 2, 1, 1, 1, 2, 4, 1, 1, 4]
def baseStart_3699604 : Nat := 118140960795 + 3699604 * 2 ^ 59
def prefixEnd_3699604 : Nat := 4983230072969 + 3 ^ 40 * 3699604 * 2
def baseEnd_3699604 : Nat := 1899675083296448516035837

theorem tailTrace_3699604 : CollatzResearch.WordTrace tailWord_3699604 prefixEnd_3699604 1899675083296448516035837 := by
  unfold tailWord_3699604
  simp only [CollatzResearch.WordTrace]
  refine ⟨67467821644487012452396933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89957095525982683269862577 67467821644487012452396933)
  ·
    refine ⟨12650216558341314834824425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 67467821644487012452396933 12650216558341314834824425)
    ·
      refine ⟨9487662418755986126118319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12650216558341314834824425 9487662418755986126118319)
      ·
        refine ⟨14231493628133979189177479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9487662418755986126118319 14231493628133979189177479)
        ·
          refine ⟨21347240442200968783766219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14231493628133979189177479 21347240442200968783766219)
          ·
            refine ⟨32020860663301453175649329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21347240442200968783766219 32020860663301453175649329)
            ·
              refine ⟨24015645497476089881736997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32020860663301453175649329 24015645497476089881736997)
              ·
                refine ⟨4502933530776766852825687, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24015645497476089881736997 4502933530776766852825687)
                ·
                  refine ⟨6754400296165150279238531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4502933530776766852825687 6754400296165150279238531)
                  ·
                    refine ⟨10131600444247725418857797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6754400296165150279238531 10131600444247725418857797)
                    ·
                      refine ⟨1899675083296448516035837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10131600444247725418857797 1899675083296448516035837)
                      ·
                        rfl

theorem cell23_3699604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 2, 4, 1, 1, 4].length) (baseStart_3699604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3699604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3699604 prefixEnd_3699604 := by exact prefixLift 3699604
  have htrace : WordTrace (prefixWord ++ tailWord_3699604) baseStart_3699604 baseEnd_3699604 := by
    simpa [prefixWord, tailWord_3699604, baseEnd_3699604] using wordTrace_append hprefix tailTrace_3699604
  have hstable : (prefixWord ++ tailWord_3699604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3699604).length < 2 ^ (prefixWord ++ tailWord_3699604).sum := by decide
  have hdescent : baseEnd_3699604 < baseStart_3699604 := by decide
  rcases family_descends (prefixWord ++ tailWord_3699604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3699607 : List Nat := [1, 1, 3, 3, 1, 2, 1, 3, 3, 2, 3]
def baseStart_3699607 : Nat := 118140960795 + 3699607 * 2 ^ 59
def prefixEnd_3699607 : Nat := 4983230072969 + 3 ^ 40 * 3699607 * 2
def baseEnd_3699607 : Nat := 1899676623738412004298323

theorem tailTrace_3699607 : CollatzResearch.WordTrace tailWord_3699607 prefixEnd_3699607 1899676623738412004298323 := by
  unfold tailWord_3699607
  simp only [CollatzResearch.WordTrace]
  refine ⟨134935752707963156417153075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89957168471975437611435383 134935752707963156417153075)
  ·
    refine ⟨202403629061944734625729613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134935752707963156417153075 202403629061944734625729613)
    ·
      refine ⟨75901360898229275484648605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 202403629061944734625729613 75901360898229275484648605)
      ·
        refine ⟨28463010336835978306743227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 75901360898229275484648605 28463010336835978306743227)
        ·
          refine ⟨42694515505253967460114841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28463010336835978306743227 42694515505253967460114841)
          ·
            refine ⟨32020886628940475595086131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42694515505253967460114841 32020886628940475595086131)
            ·
              refine ⟨48031329943410713392629197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32020886628940475595086131 48031329943410713392629197)
              ·
                refine ⟨18011748728779017522235949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48031329943410713392629197 18011748728779017522235949)
                ·
                  refine ⟨6754405773292131570838481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18011748728779017522235949 6754405773292131570838481)
                  ·
                    refine ⟨5065804329969098678128861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6754405773292131570838481 5065804329969098678128861)
                    ·
                      refine ⟨1899676623738412004298323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5065804329969098678128861 1899676623738412004298323)
                      ·
                        rfl

theorem cell23_3699607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 1, 3, 3, 2, 3].length) (baseStart_3699607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3699607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3699607 prefixEnd_3699607 := by exact prefixLift 3699607
  have htrace : WordTrace (prefixWord ++ tailWord_3699607) baseStart_3699607 baseEnd_3699607 := by
    simpa [prefixWord, tailWord_3699607, baseEnd_3699607] using wordTrace_append hprefix tailTrace_3699607
  have hstable : (prefixWord ++ tailWord_3699607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3699607).length < 2 ^ (prefixWord ++ tailWord_3699607).sum := by decide
  have hdescent : baseEnd_3699607 < baseStart_3699607 := by decide
  rcases family_descends (prefixWord ++ tailWord_3699607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3699647 : List Nat := [1, 1, 2, 2, 2, 1, 2, 1, 2, 7, 2]
def baseStart_3699647 : Nat := 118140960795 + 3699647 * 2 ^ 59
def prefixEnd_3699647 : Nat := 4983230072969 + 3 ^ 40 * 3699647 * 2
def baseEnd_3699647 : Nat := 1899697162964591847798139

theorem tailTrace_3699647 : CollatzResearch.WordTrace tailWord_3699647 prefixEnd_3699647 1899697162964591847798139 := by
  unfold tailWord_3699647
  simp only [CollatzResearch.WordTrace]
  refine ⟨134937211627818243248609195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89958141085212162165739463 134937211627818243248609195)
  ·
    refine ⟨202405817441727364872913793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134937211627818243248609195 202405817441727364872913793)
    ·
      refine ⟨151804363081295523654685345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 202405817441727364872913793 151804363081295523654685345)
      ·
        refine ⟨113853272310971642741014009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 151804363081295523654685345 113853272310971642741014009)
        ·
          refine ⟨85389954233228732055760507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 113853272310971642741014009 85389954233228732055760507)
          ·
            refine ⟨128084931349843098083640761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85389954233228732055760507 128084931349843098083640761)
            ·
              refine ⟨96063698512382323562730571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 128084931349843098083640761 96063698512382323562730571)
              ·
                refine ⟨144095547768573485344095857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 96063698512382323562730571 144095547768573485344095857)
                ·
                  refine ⟨108071660826430114008071893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 144095547768573485344095857 108071660826430114008071893)
                  ·
                    refine ⟨2532929550619455797064185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 108071660826430114008071893 2532929550619455797064185)
                    ·
                      refine ⟨1899697162964591847798139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2532929550619455797064185 1899697162964591847798139)
                      ·
                        rfl

theorem cell23_3699647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 1, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 1, 2, 7, 2].length) (baseStart_3699647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3699647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3699647 prefixEnd_3699647 := by exact prefixLift 3699647
  have htrace : WordTrace (prefixWord ++ tailWord_3699647) baseStart_3699647 baseEnd_3699647 := by
    simpa [prefixWord, tailWord_3699647, baseEnd_3699647] using wordTrace_append hprefix tailTrace_3699647
  have hstable : (prefixWord ++ tailWord_3699647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3699647).length < 2 ^ (prefixWord ++ tailWord_3699647).sum := by decide
  have hdescent : baseEnd_3699647 < baseStart_3699647 := by decide
  rcases family_descends (prefixWord ++ tailWord_3699647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3699767 : List Nat := [1, 1, 3, 1, 2, 2, 1, 4, 1, 3, 4]
def baseStart_3699767 : Nat := 118140960795 + 3699767 * 2 ^ 59
def prefixEnd_3699767 : Nat := 4983230072969 + 3 ^ 40 * 3699767 * 2
def baseEnd_3699767 : Nat := 1899758780643131378297587

theorem tailTrace_3699767 : CollatzResearch.WordTrace tailWord_3699767 prefixEnd_3699767 1899758780643131378297587 := by
  unfold tailWord_3699767
  simp only [CollatzResearch.WordTrace]
  refine ⟨134941588387383503742977555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89961058924922335828651703 134941588387383503742977555)
  ·
    refine ⟨202412382581075255614466333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134941588387383503742977555 202412382581075255614466333)
    ·
      refine ⟨75904643467903220855424875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 202412382581075255614466333 75904643467903220855424875)
      ·
        refine ⟨113856965201854831283137313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75904643467903220855424875 113856965201854831283137313)
        ·
          refine ⟨85392723901391123462352985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 113856965201854831283137313 85392723901391123462352985)
          ·
            refine ⟨64044542926043342596764739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85392723901391123462352985 64044542926043342596764739)
            ·
              refine ⟨96066814389065013895147109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64044542926043342596764739 96066814389065013895147109)
              ·
                refine ⟨18012527697949690105340083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 96066814389065013895147109 18012527697949690105340083)
                ·
                  refine ⟨27018791546924535158010125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18012527697949690105340083 27018791546924535158010125)
                  ·
                    refine ⟨10132046830096700684253797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27018791546924535158010125 10132046830096700684253797)
                    ·
                      refine ⟨1899758780643131378297587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10132046830096700684253797 1899758780643131378297587)
                      ·
                        rfl

theorem cell23_3699767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 4, 1, 3, 4].length) (baseStart_3699767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3699767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3699767 prefixEnd_3699767 := by exact prefixLift 3699767
  have htrace : WordTrace (prefixWord ++ tailWord_3699767) baseStart_3699767 baseEnd_3699767 := by
    simpa [prefixWord, tailWord_3699767, baseEnd_3699767] using wordTrace_append hprefix tailTrace_3699767
  have hstable : (prefixWord ++ tailWord_3699767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3699767).length < 2 ^ (prefixWord ++ tailWord_3699767).sum := by decide
  have hdescent : baseEnd_3699767 < baseStart_3699767 := by decide
  rcases family_descends (prefixWord ++ tailWord_3699767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3699784 : List Nat := [2, 1, 3, 1, 1, 1, 3, 2, 1, 6, 2]
def baseStart_3699784 : Nat := 118140960795 + 3699784 * 2 ^ 59
def prefixEnd_3699784 : Nat := 4983230072969 + 3 ^ 40 * 3699784 * 2
def baseEnd_3699784 : Nat := 1899767509814257811785009

theorem tailTrace_3699784 : CollatzResearch.WordTrace tailWord_3699784 prefixEnd_3699784 1899767509814257811785009 := by
  unfold tailWord_3699784
  simp only [CollatzResearch.WordTrace]
  refine ⟨67471104214160957823173203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89961472285547943764230937 67471104214160957823173203)
  ·
    refine ⟨101206656321241436734759805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67471104214160957823173203 101206656321241436734759805)
    ·
      refine ⟨37952496120465538775534927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 101206656321241436734759805 37952496120465538775534927)
      ·
        refine ⟨56928744180698308163302391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37952496120465538775534927 56928744180698308163302391)
        ·
          refine ⟨85393116271047462244953587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56928744180698308163302391 85393116271047462244953587)
          ·
            refine ⟨128089674406571193367430381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85393116271047462244953587 128089674406571193367430381)
            ·
              refine ⟨48033627902464197512786393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 128089674406571193367430381 48033627902464197512786393)
              ·
                refine ⟨36025220926848148134589795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48033627902464197512786393 36025220926848148134589795)
                ·
                  refine ⟨54037831390272222201884693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36025220926848148134589795 54037831390272222201884693)
                  ·
                    refine ⟨2533023346419010415713345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 54037831390272222201884693 2533023346419010415713345)
                    ·
                      refine ⟨1899767509814257811785009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2533023346419010415713345 1899767509814257811785009)
                      ·
                        rfl

theorem cell23_3699784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 3, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 3, 2, 1, 6, 2].length) (baseStart_3699784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3699784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3699784 prefixEnd_3699784 := by exact prefixLift 3699784
  have htrace : WordTrace (prefixWord ++ tailWord_3699784) baseStart_3699784 baseEnd_3699784 := by
    simpa [prefixWord, tailWord_3699784, baseEnd_3699784] using wordTrace_append hprefix tailTrace_3699784
  have hstable : (prefixWord ++ tailWord_3699784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3699784).length < 2 ^ (prefixWord ++ tailWord_3699784).sum := by decide
  have hdescent : baseEnd_3699784 < baseStart_3699784 := by decide
  rcases family_descends (prefixWord ++ tailWord_3699784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3699797 : List Nat := [1, 3, 2, 2, 1, 2, 1, 1, 1, 3, 6]
def baseStart_3699797 : Nat := 118140960795 + 3699797 * 2 ^ 59
def prefixEnd_3699797 : Nat := 4983230072969 + 3 ^ 40 * 3699797 * 2
def baseEnd_3699797 : Nat := 1899774185062766260922449

theorem tailTrace_3699797 : CollatzResearch.WordTrace tailWord_3699797 prefixEnd_3699797 1899774185062766260922449 := by
  unfold tailWord_3699797
  simp only [CollatzResearch.WordTrace]
  refine ⟨134942682577274818866569645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89961788384849879244379763 134942682577274818866569645)
  ·
    refine ⟨50603505966478057074963617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 134942682577274818866569645 50603505966478057074963617)
    ·
      refine ⟨37952629474858542806222713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50603505966478057074963617 37952629474858542806222713)
      ·
        refine ⟨28464472106143907104667035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37952629474858542806222713 28464472106143907104667035)
        ·
          refine ⟨42696708159215860657000553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28464472106143907104667035 42696708159215860657000553)
          ·
            refine ⟨32022531119411895492750415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42696708159215860657000553 32022531119411895492750415)
            ·
              refine ⟨48033796679117843239125623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32022531119411895492750415 48033796679117843239125623)
              ·
                refine ⟨72050695018676764858688435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48033796679117843239125623 72050695018676764858688435)
                ·
                  refine ⟨108076042528015147288032653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 72050695018676764858688435 108076042528015147288032653)
                  ·
                    refine ⟨40528515948005680233012245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 108076042528015147288032653 40528515948005680233012245)
                    ·
                      refine ⟨1899774185062766260922449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 40528515948005680233012245 1899774185062766260922449)
                      ·
                        rfl

theorem cell23_3699797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 1, 1, 1, 3, 6].length) (baseStart_3699797 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3699797 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3699797 prefixEnd_3699797 := by exact prefixLift 3699797
  have htrace : WordTrace (prefixWord ++ tailWord_3699797) baseStart_3699797 baseEnd_3699797 := by
    simpa [prefixWord, tailWord_3699797, baseEnd_3699797] using wordTrace_append hprefix tailTrace_3699797
  have hstable : (prefixWord ++ tailWord_3699797).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3699797).length < 2 ^ (prefixWord ++ tailWord_3699797).sum := by decide
  have hdescent : baseEnd_3699797 < baseStart_3699797 := by decide
  rcases family_descends (prefixWord ++ tailWord_3699797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3699807 : List Nat := [1, 1, 2, 3, 1, 1, 5, 1, 8]
def baseStart_3699807 : Nat := 118140960795 + 3699807 * 2 ^ 59
def prefixEnd_3699807 : Nat := 4983230072969 + 3 ^ 40 * 3699807 * 2
def baseEnd_3699807 : Nat := 211086591096590135755267

theorem tailTrace_3699807 : CollatzResearch.WordTrace tailWord_3699807 prefixEnd_3699807 211086591096590135755267 := by
  unfold tailWord_3699807
  simp only [CollatzResearch.WordTrace]
  refine ⟨134943047307238590574433675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89962031538159060382955783 134943047307238590574433675)
  ·
    refine ⟨202414570960857885861650513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134943047307238590574433675 202414570960857885861650513)
    ·
      refine ⟨151810928220643414396237885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 202414570960857885861650513 151810928220643414396237885)
      ·
        refine ⟨56929098082741280398589207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 151810928220643414396237885 56929098082741280398589207)
        ·
          refine ⟨85393647124111920597883811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56929098082741280398589207 85393647124111920597883811)
          ·
            refine ⟨128090470686167880896825717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85393647124111920597883811 128090470686167880896825717)
            ·
              refine ⟨12008481626828238834077411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 128090470686167880896825717 12008481626828238834077411)
              ·
                refine ⟨18012722440242358251116117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12008481626828238834077411 18012722440242358251116117)
                ·
                  refine ⟨211086591096590135755267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 18012722440242358251116117 211086591096590135755267)
                  ·
                    rfl

theorem cell23_3699807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 5, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 5, 1, 8].length) (baseStart_3699807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3699807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3699807 prefixEnd_3699807 := by exact prefixLift 3699807
  have htrace : WordTrace (prefixWord ++ tailWord_3699807) baseStart_3699807 baseEnd_3699807 := by
    simpa [prefixWord, tailWord_3699807, baseEnd_3699807] using wordTrace_append hprefix tailTrace_3699807
  have hstable : (prefixWord ++ tailWord_3699807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3699807).length < 2 ^ (prefixWord ++ tailWord_3699807).sum := by decide
  have hdescent : baseEnd_3699807 < baseStart_3699807 := by decide
  rcases family_descends (prefixWord ++ tailWord_3699807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3699845 : List Nat := [1, 3, 1, 1, 6, 2, 1, 3, 1, 4]
def baseStart_3699845 : Nat := 118140960795 + 3699845 * 2 ^ 59
def prefixEnd_3699845 : Nat := 4983230072969 + 3 ^ 40 * 3699845 * 2
def baseEnd_3699845 : Nat := 633266277378060691040743

theorem tailTrace_3699845 : CollatzResearch.WordTrace tailWord_3699845 prefixEnd_3699845 633266277378060691040743 := by
  unfold tailWord_3699845
  simp only [CollatzResearch.WordTrace]
  refine ⟨134944433281100923064316989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89962955520733948709544659 134944433281100923064316989)
  ·
    refine ⟨50604162480412846149118871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 134944433281100923064316989 50604162480412846149118871)
    ·
      refine ⟨75906243720619269223678307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50604162480412846149118871 75906243720619269223678307)
      ·
        refine ⟨113859365580928903835517461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75906243720619269223678307 113859365580928903835517461)
        ·
          refine ⟨5337157761606042367289881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 113859365580928903835517461 5337157761606042367289881)
          ·
            refine ⟨4002868321204531775467411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5337157761606042367289881 4002868321204531775467411)
            ·
              refine ⟨6004302481806797663201117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4002868321204531775467411 6004302481806797663201117)
              ·
                refine ⟨2251613430677549123700419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6004302481806797663201117 2251613430677549123700419)
                ·
                  refine ⟨3377420146016323685550629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2251613430677549123700419 3377420146016323685550629)
                  ·
                    refine ⟨633266277378060691040743, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3377420146016323685550629 633266277378060691040743)
                    ·
                      rfl

theorem cell23_3699845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 2, 1, 3, 1, 4].length) (baseStart_3699845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3699845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3699845 prefixEnd_3699845 := by exact prefixLift 3699845
  have htrace : WordTrace (prefixWord ++ tailWord_3699845) baseStart_3699845 baseEnd_3699845 := by
    simpa [prefixWord, tailWord_3699845, baseEnd_3699845] using wordTrace_append hprefix tailTrace_3699845
  have hstable : (prefixWord ++ tailWord_3699845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3699845).length < 2 ^ (prefixWord ++ tailWord_3699845).sum := by decide
  have hdescent : baseEnd_3699845 < baseStart_3699845 := by decide
  rcases family_descends (prefixWord ++ tailWord_3699845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3699868 : List Nat := [2, 2, 3, 2, 1, 2, 3, 1, 3, 1, 3]
def baseStart_3699868 : Nat := 118140960795 + 3699868 * 2 ^ 59
def prefixEnd_3699868 : Nat := 4983230072969 + 3 ^ 40 * 3699868 * 2
def baseEnd_3699868 : Nat := 1899810642189235483134623

theorem tailTrace_3699868 : CollatzResearch.WordTrace tailWord_3699868 prefixEnd_3699868 1899810642189235483134623 := by
  unfold tailWord_3699868
  simp only [CollatzResearch.WordTrace]
  refine ⟨67472636080008798996202129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89963514773345065328269505 67472636080008798996202129)
  ·
    refine ⟨50604477060006599247151597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67472636080008798996202129 50604477060006599247151597)
    ·
      refine ⟨18976678897502474717681849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50604477060006599247151597 18976678897502474717681849)
      ·
        refine ⟨14232509173126856038261387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18976678897502474717681849 14232509173126856038261387)
        ·
          refine ⟨21348763759690284057392081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14232509173126856038261387 21348763759690284057392081)
          ·
            refine ⟨16011572819767713043044061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21348763759690284057392081 16011572819767713043044061)
            ·
              refine ⟨6004339807412892391141523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16011572819767713043044061 6004339807412892391141523)
              ·
                refine ⟨9006509711119338586712285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6004339807412892391141523 9006509711119338586712285)
                ·
                  refine ⟨3377441141669751970017107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9006509711119338586712285 3377441141669751970017107)
                  ·
                    refine ⟨5066161712504627955025661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3377441141669751970017107 5066161712504627955025661)
                    ·
                      refine ⟨1899810642189235483134623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5066161712504627955025661 1899810642189235483134623)
                      ·
                        rfl

theorem cell23_3699868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 3, 1, 3, 1, 3].length) (baseStart_3699868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3699868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3699868 prefixEnd_3699868 := by exact prefixLift 3699868
  have htrace : WordTrace (prefixWord ++ tailWord_3699868) baseStart_3699868 baseEnd_3699868 := by
    simpa [prefixWord, tailWord_3699868, baseEnd_3699868] using wordTrace_append hprefix tailTrace_3699868
  have hstable : (prefixWord ++ tailWord_3699868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3699868).length < 2 ^ (prefixWord ++ tailWord_3699868).sum := by decide
  have hdescent : baseEnd_3699868 < baseStart_3699868 := by decide
  rcases family_descends (prefixWord ++ tailWord_3699868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3699884 : List Nat := [2, 2, 1, 1, 1, 1, 1, 4, 6, 4]
def baseStart_3699884 : Nat := 118140960795 + 3699884 * 2 ^ 59
def prefixEnd_3699884 : Nat := 4983230072969 + 3 ^ 40 * 3699884 * 2
def baseEnd_3699884 : Nat := 633272952626569140178183

theorem tailTrace_3699884 : CollatzResearch.WordTrace tailWord_3699884 prefixEnd_3699884 633272952626569140178183 := by
  unfold tailWord_3699884
  simp only [CollatzResearch.WordTrace]
  refine ⟨67472927863979816362493353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89963903818639755149991137 67472927863979816362493353)
  ·
    refine ⟨50604695897984862271870015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67472927863979816362493353 50604695897984862271870015)
    ·
      refine ⟨75907043846977293407805023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50604695897984862271870015 75907043846977293407805023)
      ·
        refine ⟨113860565770465940111707535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75907043846977293407805023 113860565770465940111707535)
        ·
          refine ⟨170790848655698910167561303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113860565770465940111707535 170790848655698910167561303)
          ·
            refine ⟨256186272983548365251341955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 170790848655698910167561303 256186272983548365251341955)
            ·
              refine ⟨384279409475322547877012933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 256186272983548365251341955 384279409475322547877012933)
              ·
                refine ⟨72052389276622977726939925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 384279409475322547877012933 72052389276622977726939925)
                ·
                  refine ⟨3377455747341702080950309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 72052389276622977726939925 3377455747341702080950309)
                  ·
                    refine ⟨633272952626569140178183, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3377455747341702080950309 633272952626569140178183)
                    ·
                      rfl

theorem cell23_3699884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 6, 4].length) (baseStart_3699884 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3699884 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3699884 prefixEnd_3699884 := by exact prefixLift 3699884
  have htrace : WordTrace (prefixWord ++ tailWord_3699884) baseStart_3699884 baseEnd_3699884 := by
    simpa [prefixWord, tailWord_3699884, baseEnd_3699884] using wordTrace_append hprefix tailTrace_3699884
  have hstable : (prefixWord ++ tailWord_3699884).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3699884).length < 2 ^ (prefixWord ++ tailWord_3699884).sum := by decide
  have hdescent : baseEnd_3699884 < baseStart_3699884 := by decide
  rcases family_descends (prefixWord ++ tailWord_3699884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3699891 : List Nat := [1, 1, 1, 2, 3, 2, 5, 2, 1, 1, 4]
def baseStart_3699891 : Nat := 118140960795 + 3699891 * 2 ^ 59
def prefixEnd_3699891 : Nat := 4983230072969 + 3 ^ 40 * 3699891 * 2
def baseEnd_3699891 : Nat := 1899822452244288893147017

theorem tailTrace_3699891 : CollatzResearch.WordTrace tailWord_3699891 prefixEnd_3699891 1899822452244288893147017 := by
  unfold tailWord_3699891
  simp only [CollatzResearch.WordTrace]
  refine ⟨134946111038934272920491527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89964074025956181946994351 134946111038934272920491527)
  ·
    refine ⟨202419166558401409380737291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134946111038934272920491527 202419166558401409380737291)
    ·
      refine ⟨303628749837602114071105937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 202419166558401409380737291 303628749837602114071105937)
      ·
        refine ⟨227721562378201585553329453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 303628749837602114071105937 227721562378201585553329453)
        ·
          refine ⟨85395585891825594582498545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 227721562378201585553329453 85395585891825594582498545)
          ·
            refine ⟨64046689418869195936873909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85395585891825594582498545 64046689418869195936873909)
            ·
              refine ⟨6004377133018987119081929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 64046689418869195936873909 6004377133018987119081929)
              ·
                refine ⟨4503282849764240339311447, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6004377133018987119081929 4503282849764240339311447)
                ·
                  refine ⟨6754924274646360508967171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4503282849764240339311447 6754924274646360508967171)
                  ·
                    refine ⟨10132386411969540763450757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6754924274646360508967171 10132386411969540763450757)
                    ·
                      refine ⟨1899822452244288893147017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10132386411969540763450757 1899822452244288893147017)
                      ·
                        rfl

theorem cell23_3699891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 5, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 5, 2, 1, 1, 4].length) (baseStart_3699891 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3699891 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3699891 prefixEnd_3699891 := by exact prefixLift 3699891
  have htrace : WordTrace (prefixWord ++ tailWord_3699891) baseStart_3699891 baseEnd_3699891 := by
    simpa [prefixWord, tailWord_3699891, baseEnd_3699891] using wordTrace_append hprefix tailTrace_3699891
  have hstable : (prefixWord ++ tailWord_3699891).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3699891).length < 2 ^ (prefixWord ++ tailWord_3699891).sum := by decide
  have hdescent : baseEnd_3699891 < baseStart_3699891 := by decide
  rcases family_descends (prefixWord ++ tailWord_3699891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3699905 : List Nat := [1, 2, 6, 1, 1, 2, 3, 1, 1, 5]
def baseStart_3699905 : Nat := 118140960795 + 3699905 * 2 ^ 59
def prefixEnd_3699905 : Nat := 4983230072969 + 3 ^ 40 * 3699905 * 2
def baseEnd_3699905 : Nat := 633276546991150612790651

theorem tailTrace_3699905 : CollatzResearch.WordTrace tailWord_3699905 prefixEnd_3699905 633276546991150612790651 := by
  unfold tailWord_3699905
  simp only [CollatzResearch.WordTrace]
  refine ⟨134946621660883553311501169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89964414440589035541000779 134946621660883553311501169)
  ·
    refine ⟨101209966245662664983625877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134946621660883553311501169 101209966245662664983625877)
    ·
      refine ⟨4744217167765437421107463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 101209966245662664983625877 4744217167765437421107463)
      ·
        refine ⟨7116325751648156131661195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4744217167765437421107463 7116325751648156131661195)
        ·
          refine ⟨10674488627472234197491793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7116325751648156131661195 10674488627472234197491793)
          ·
            refine ⟨8005866470604175648118845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10674488627472234197491793 8005866470604175648118845)
            ·
              refine ⟨3002199926476565868044567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8005866470604175648118845 3002199926476565868044567)
              ·
                refine ⟨4503299889714848802066851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3002199926476565868044567 4503299889714848802066851)
                ·
                  refine ⟨6754949834572273203100277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4503299889714848802066851 6754949834572273203100277)
                  ·
                    refine ⟨633276546991150612790651, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6754949834572273203100277 633276546991150612790651)
                    ·
                      rfl

theorem cell23_3699905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 2, 3, 1, 1, 5].length) (baseStart_3699905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3699905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3699905 prefixEnd_3699905 := by exact prefixLift 3699905
  have htrace : WordTrace (prefixWord ++ tailWord_3699905) baseStart_3699905 baseEnd_3699905 := by
    simpa [prefixWord, tailWord_3699905, baseEnd_3699905] using wordTrace_append hprefix tailTrace_3699905
  have hstable : (prefixWord ++ tailWord_3699905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3699905).length < 2 ^ (prefixWord ++ tailWord_3699905).sum := by decide
  have hdescent : baseEnd_3699905 < baseStart_3699905 := by decide
  rcases family_descends (prefixWord ++ tailWord_3699905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3699911 : List Nat := [1, 1, 4, 1, 1, 1, 1, 7, 1, 2, 3]
def baseStart_3699911 : Nat := 118140960795 + 3699911 * 2 ^ 59
def prefixEnd_3699911 : Nat := 4983230072969 + 3 ^ 40 * 3699911 * 2
def baseEnd_3699911 : Nat := 1899832721857378814896925

theorem tailTrace_3699911 : CollatzResearch.WordTrace tailWord_3699911 prefixEnd_3699911 1899832721857378814896925 := by
  unfold tailWord_3699911
  simp only [CollatzResearch.WordTrace]
  refine ⟨134946840498861816336219587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89964560332574544224146391 134946840498861816336219587)
  ·
    refine ⟨202420260748292724504329381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134946840498861816336219587 202420260748292724504329381)
    ·
      refine ⟨37953798890304885844561759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 202420260748292724504329381 37953798890304885844561759)
      ·
        refine ⟨56930698335457328766842639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37953798890304885844561759 56930698335457328766842639)
        ·
          refine ⟨85396047503185993150263959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56930698335457328766842639 85396047503185993150263959)
          ·
            refine ⟨128094071254778989725395939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85396047503185993150263959 128094071254778989725395939)
            ·
              refine ⟨192141106882168484588093909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 128094071254778989725395939 192141106882168484588093909)
              ·
                refine ⟨4503307192550823857533451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 192141106882168484588093909 4503307192550823857533451)
                ·
                  refine ⟨6754960788826235786300177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4503307192550823857533451 6754960788826235786300177)
                  ·
                    refine ⟨5066220591619676839725133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6754960788826235786300177 5066220591619676839725133)
                    ·
                      refine ⟨1899832721857378814896925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5066220591619676839725133 1899832721857378814896925)
                      ·
                        rfl

theorem cell23_3699911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 7, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 7, 1, 2, 3].length) (baseStart_3699911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3699911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3699911 prefixEnd_3699911 := by exact prefixLift 3699911
  have htrace : WordTrace (prefixWord ++ tailWord_3699911) baseStart_3699911 baseEnd_3699911 := by
    simpa [prefixWord, tailWord_3699911, baseEnd_3699911] using wordTrace_append hprefix tailTrace_3699911
  have hstable : (prefixWord ++ tailWord_3699911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3699911).length < 2 ^ (prefixWord ++ tailWord_3699911).sum := by decide
  have hdescent : baseEnd_3699911 < baseStart_3699911 := by decide
  rcases family_descends (prefixWord ++ tailWord_3699911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3699944 : List Nat := [2, 1, 4, 1, 2, 1, 1, 2, 2, 7]
def baseStart_3699944 : Nat := 118140960795 + 3699944 * 2 ^ 59
def prefixEnd_3699944 : Nat := 4983230072969 + 3 ^ 40 * 3699944 * 2
def baseEnd_3699944 : Nat := 633283222239659061928091

theorem tailTrace_3699944 : CollatzResearch.WordTrace tailWord_3699944 prefixEnd_3699944 633283222239659061928091 := by
  unfold tailWord_3699944
  simp only [CollatzResearch.WordTrace]
  refine ⟨67474022053871131486085443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89965362738494841981447257 67474022053871131486085443)
  ·
    refine ⟨101211033080806697229128165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67474022053871131486085443 101211033080806697229128165)
    ·
      refine ⟨18977068702651255730461531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 101211033080806697229128165 18977068702651255730461531)
      ·
        refine ⟨28465603053976883595692297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18977068702651255730461531 28465603053976883595692297)
        ·
          refine ⟨21349202290482662696769223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28465603053976883595692297 21349202290482662696769223)
          ·
            refine ⟨32023803435723994045153835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21349202290482662696769223 32023803435723994045153835)
            ·
              refine ⟨48035705153585991067730753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32023803435723994045153835 48035705153585991067730753)
              ·
                refine ⟨36026778865189493300798065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48035705153585991067730753 36026778865189493300798065)
                ·
                  refine ⟨27020084148892119975598549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36026778865189493300798065 27020084148892119975598549)
                  ·
                    refine ⟨633283222239659061928091, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 27020084148892119975598549 633283222239659061928091)
                    ·
                      rfl

theorem cell23_3699944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 1, 2, 2, 7].length) (baseStart_3699944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3699944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3699944 prefixEnd_3699944 := by exact prefixLift 3699944
  have htrace : WordTrace (prefixWord ++ tailWord_3699944) baseStart_3699944 baseEnd_3699944 := by
    simpa [prefixWord, tailWord_3699944, baseEnd_3699944] using wordTrace_append hprefix tailTrace_3699944
  have hstable : (prefixWord ++ tailWord_3699944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3699944).length < 2 ^ (prefixWord ++ tailWord_3699944).sum := by decide
  have hdescent : baseEnd_3699944 < baseStart_3699944 := by decide
  rcases family_descends (prefixWord ++ tailWord_3699944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3699956 : List Nat := [2, 6, 1, 2, 2, 1, 2, 1, 1, 5]
def baseStart_3699956 : Nat := 118140960795 + 3699956 * 2 ^ 59
def prefixEnd_3699956 : Nat := 4983230072969 + 3 ^ 40 * 3699956 * 2
def baseEnd_3699956 : Nat := 633285276162277046278073

theorem tailTrace_3699956 : CollatzResearch.WordTrace tailWord_3699956 prefixEnd_3699956 633285276162277046278073 := by
  unfold tailWord_3699956
  simp only [CollatzResearch.WordTrace]
  refine ⟨67474240891849394510803861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89965654522465859347738481 67474240891849394510803861)
  ·
    refine ⟨3162855041805440367693931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 67474240891849394510803861 3162855041805440367693931)
    ·
      refine ⟨4744282562708160551540897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3162855041805440367693931 4744282562708160551540897)
      ·
        refine ⟨3558211922031120413655673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4744282562708160551540897 3558211922031120413655673)
        ·
          refine ⟨2668658941523340310241755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3558211922031120413655673 2668658941523340310241755)
          ·
            refine ⟨4002988412285010465362633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2668658941523340310241755 4002988412285010465362633)
            ·
              refine ⟨3002241309213757849021975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4002988412285010465362633 3002241309213757849021975)
              ·
                refine ⟨4503361963820636773532963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3002241309213757849021975 4503361963820636773532963)
                ·
                  refine ⟨6755042945730955160299445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4503361963820636773532963 6755042945730955160299445)
                  ·
                    refine ⟨633285276162277046278073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6755042945730955160299445 633285276162277046278073)
                    ·
                      rfl

theorem cell23_3699956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 2, 1, 2, 1, 1, 5].length) (baseStart_3699956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3699956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3699956 prefixEnd_3699956 := by exact prefixLift 3699956
  have htrace : WordTrace (prefixWord ++ tailWord_3699956) baseStart_3699956 baseEnd_3699956 := by
    simpa [prefixWord, tailWord_3699956, baseEnd_3699956] using wordTrace_append hprefix tailTrace_3699956
  have hstable : (prefixWord ++ tailWord_3699956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3699956).length < 2 ^ (prefixWord ++ tailWord_3699956).sum := by decide
  have hdescent : baseEnd_3699956 < baseStart_3699956 := by decide
  rcases family_descends (prefixWord ++ tailWord_3699956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3699958 : List Nat := [5, 1, 1, 1, 1, 1, 1, 4, 4, 1, 3]
def baseStart_3699958 : Nat := 118140960795 + 3699958 * 2 ^ 59
def prefixEnd_3699958 : Nat := 4983230072969 + 3 ^ 40 * 3699958 * 2
def baseEnd_3699958 : Nat := 1899856855448140131009209

theorem tailTrace_3699958 : CollatzResearch.WordTrace tailWord_3699958 prefixEnd_3699958 1899856855448140131009209 := by
  unfold tailWord_3699958
  simp only [CollatzResearch.WordTrace]
  refine ⟨8434284670605721460198783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 89965703153127695575453685 8434284670605721460198783)
  ·
    refine ⟨12651427005908582190298175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8434284670605721460198783 12651427005908582190298175)
    ·
      refine ⟨18977140508862873285447263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12651427005908582190298175 18977140508862873285447263)
      ·
        refine ⟨28465710763294309928170895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18977140508862873285447263 28465710763294309928170895)
        ·
          refine ⟨42698566144941464892256343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28465710763294309928170895 42698566144941464892256343)
          ·
            refine ⟨64047849217412197338384515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42698566144941464892256343 64047849217412197338384515)
            ·
              refine ⟨96071773826118296007576773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64047849217412197338384515 96071773826118296007576773)
              ·
                refine ⟨18013457592397180501420645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 96071773826118296007576773 18013457592397180501420645)
                ·
                  refine ⟨3377523298574471344016371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18013457592397180501420645 3377523298574471344016371)
                  ·
                    refine ⟨5066284947861707016024557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3377523298574471344016371 5066284947861707016024557)
                    ·
                      refine ⟨1899856855448140131009209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5066284947861707016024557 1899856855448140131009209)
                      ·
                        rfl

theorem cell23_3699958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 4, 4, 1, 3].length) (baseStart_3699958 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3699958 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3699958 prefixEnd_3699958 := by exact prefixLift 3699958
  have htrace : WordTrace (prefixWord ++ tailWord_3699958) baseStart_3699958 baseEnd_3699958 := by
    simpa [prefixWord, tailWord_3699958, baseEnd_3699958] using wordTrace_append hprefix tailTrace_3699958
  have hstable : (prefixWord ++ tailWord_3699958).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3699958).length < 2 ^ (prefixWord ++ tailWord_3699958).sum := by decide
  have hdescent : baseEnd_3699958 < baseStart_3699958 := by decide
  rcases family_descends (prefixWord ++ tailWord_3699958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3700002 : List Nat := [3, 3, 1, 1, 4, 1, 2, 2, 1, 3, 2]
def baseStart_3700002 : Nat := 118140960795 + 3700002 * 2 ^ 59
def prefixEnd_3700002 : Nat := 4983230072969 + 3 ^ 40 * 3700002 * 2
def baseEnd_3700002 : Nat := 1899879448596937958859007

theorem tailTrace_3700002 : CollatzResearch.WordTrace tailWord_3700002 prefixEnd_3700002 1899879448596937958859007 := by
  unfold tailWord_3700002
  simp only [CollatzResearch.WordTrace]
  refine ⟨33737539885383034719445565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89966773027688092585188173 33737539885383034719445565)
  ·
    refine ⟨12651577457018638019792087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33737539885383034719445565 12651577457018638019792087)
    ·
      refine ⟨18977366185527957029688131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12651577457018638019792087 18977366185527957029688131)
      ·
        refine ⟨28466049278291935544532197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18977366185527957029688131 28466049278291935544532197)
        ·
          refine ⟨5337384239679737914599787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28466049278291935544532197 5337384239679737914599787)
          ·
            refine ⟨8006076359519606871899681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5337384239679737914599787 8006076359519606871899681)
            ·
              refine ⟨6004557269639705153924761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8006076359519606871899681 6004557269639705153924761)
              ·
                refine ⟨4503417952229778865443571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6004557269639705153924761 4503417952229778865443571)
                ·
                  refine ⟨6755126928344668298165357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4503417952229778865443571 6755126928344668298165357)
                  ·
                    refine ⟨2533172598129250611812009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6755126928344668298165357 2533172598129250611812009)
                    ·
                      refine ⟨1899879448596937958859007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2533172598129250611812009 1899879448596937958859007)
                      ·
                        rfl

theorem cell23_3700002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 1, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 1, 2, 2, 1, 3, 2].length) (baseStart_3700002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3700002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3700002 prefixEnd_3700002 := by exact prefixLift 3700002
  have htrace : WordTrace (prefixWord ++ tailWord_3700002) baseStart_3700002 baseEnd_3700002 := by
    simpa [prefixWord, tailWord_3700002, baseEnd_3700002] using wordTrace_append hprefix tailTrace_3700002
  have hstable : (prefixWord ++ tailWord_3700002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3700002).length < 2 ^ (prefixWord ++ tailWord_3700002).sum := by decide
  have hdescent : baseEnd_3700002 < baseStart_3700002 := by decide
  rcases family_descends (prefixWord ++ tailWord_3700002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3700068 : List Nat := [2, 3, 1, 1, 3, 3, 2, 1, 2, 5]
def baseStart_3700068 : Nat := 118140960795 + 3700068 * 2 ^ 59
def prefixEnd_3700068 : Nat := 4983230072969 + 3 ^ 40 * 3700068 * 2
def baseEnd_3700068 : Nat := 633304446106711566877901

theorem tailTrace_3700068 : CollatzResearch.WordTrace tailWord_3700068 prefixEnd_3700068 633304446106711566877901 := by
  unfold tailWord_3700068
  simp only [CollatzResearch.WordTrace]
  refine ⟨67476283379646516074842429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89968377839528688099789905 67476283379646516074842429)
  ·
    refine ⟨25303606267367443528065911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67476283379646516074842429 25303606267367443528065911)
    ·
      refine ⟨37955409401051165292098867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25303606267367443528065911 37955409401051165292098867)
      ·
        refine ⟨56933114101576747938148301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37955409401051165292098867 56933114101576747938148301)
        ·
          refine ⟨21349917788091280476805613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56933114101576747938148301 21349917788091280476805613)
          ·
            refine ⟨8006219170534230178802105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21349917788091280476805613 8006219170534230178802105)
            ·
              refine ⟨6004664377900672634101579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8006219170534230178802105 6004664377900672634101579)
              ·
                refine ⟨9006996566851008951152369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6004664377900672634101579 9006996566851008951152369)
                ·
                  refine ⟨6755247425138256713364277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9006996566851008951152369 6755247425138256713364277)
                  ·
                    refine ⟨633304446106711566877901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6755247425138256713364277 633304446106711566877901)
                    ·
                      rfl

theorem cell23_3700068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 3, 2, 1, 2, 5].length) (baseStart_3700068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3700068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3700068 prefixEnd_3700068 := by exact prefixLift 3700068
  have htrace : WordTrace (prefixWord ++ tailWord_3700068) baseStart_3700068 baseEnd_3700068 := by
    simpa [prefixWord, tailWord_3700068, baseEnd_3700068] using wordTrace_append hprefix tailTrace_3700068
  have hstable : (prefixWord ++ tailWord_3700068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3700068).length < 2 ^ (prefixWord ++ tailWord_3700068).sum := by decide
  have hdescent : baseEnd_3700068 < baseStart_3700068 := by decide
  rcases family_descends (prefixWord ++ tailWord_3700068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3700105 : List Nat := [1, 2, 1, 1, 7, 1, 1, 1, 2, 4, 2]
def baseStart_3700105 : Nat := 118140960795 + 3700105 * 2 ^ 59
def prefixEnd_3700105 : Nat := 4983230072969 + 3 ^ 40 * 3700105 * 2
def baseEnd_3700105 : Nat := 1899932337104351055871033

theorem tailTrace_3700105 : CollatzResearch.WordTrace tailWord_3700105 prefixEnd_3700105 1899932337104351055871033 := by
  unfold tailWord_3700105
  simp only [CollatzResearch.WordTrace]
  refine ⟨134953916260158987468781769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89969277506772658312521179 134953916260158987468781769)
  ·
    refine ⟨101215437195119240601586327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134953916260158987468781769 101215437195119240601586327)
    ·
      refine ⟨151823155792678860902379491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101215437195119240601586327 151823155792678860902379491)
      ·
        refine ⟨227734733689018291353569237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151823155792678860902379491 227734733689018291353569237)
        ·
          refine ⟨5337532820836366203599279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 227734733689018291353569237 5337532820836366203599279)
          ·
            refine ⟨8006299231254549305398919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5337532820836366203599279 8006299231254549305398919)
            ·
              refine ⟨12009448846881823958098379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8006299231254549305398919 12009448846881823958098379)
              ·
                refine ⟨18014173270322735937147569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12009448846881823958098379 18014173270322735937147569)
                ·
                  refine ⟨13510629952742051952860677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18014173270322735937147569 13510629952742051952860677)
                  ·
                    refine ⟨2533243116139134741161377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13510629952742051952860677 2533243116139134741161377)
                    ·
                      refine ⟨1899932337104351055871033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2533243116139134741161377 1899932337104351055871033)
                      ·
                        rfl

theorem cell23_3700105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 1, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 1, 1, 1, 2, 4, 2].length) (baseStart_3700105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3700105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3700105 prefixEnd_3700105 := by exact prefixLift 3700105
  have htrace : WordTrace (prefixWord ++ tailWord_3700105) baseStart_3700105 baseEnd_3700105 := by
    simpa [prefixWord, tailWord_3700105, baseEnd_3700105] using wordTrace_append hprefix tailTrace_3700105
  have hstable : (prefixWord ++ tailWord_3700105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3700105).length < 2 ^ (prefixWord ++ tailWord_3700105).sum := by decide
  have hdescent : baseEnd_3700105 < baseStart_3700105 := by decide
  rcases family_descends (prefixWord ++ tailWord_3700105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3700125 : List Nat := [1, 4, 2, 1, 3, 1, 3, 1, 2, 2, 3]
def baseStart_3700125 : Nat := 118140960795 + 3700125 * 2 ^ 59
def prefixEnd_3700125 : Nat := 4983230072969 + 3 ^ 40 * 3700125 * 2
def baseEnd_3700125 : Nat := 1899942606717440977620941

theorem tailTrace_3700125 : CollatzResearch.WordTrace tailWord_3700125 prefixEnd_3700125 1899942606717440977620941 := by
  unfold tailWord_3700125
  simp only [CollatzResearch.WordTrace]
  refine ⟨134954645720086530884509829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89969763813391020589673219 134954645720086530884509829)
  ·
    refine ⟨25303996072516224540845593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 134954645720086530884509829 25303996072516224540845593)
    ·
      refine ⟨18977997054387168405634195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25303996072516224540845593 18977997054387168405634195)
      ·
        refine ⟨28466995581580752608451293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18977997054387168405634195 28466995581580752608451293)
        ·
          refine ⟨10675123343092782228169235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28466995581580752608451293 10675123343092782228169235)
          ·
            refine ⟨16012685014639173342253853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10675123343092782228169235 16012685014639173342253853)
            ·
              refine ⟨6004756880489690003345195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16012685014639173342253853 6004756880489690003345195)
              ·
                refine ⟨9007135320734535005017793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6004756880489690003345195 9007135320734535005017793)
                ·
                  refine ⟨6755351490550901253763345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9007135320734535005017793 6755351490550901253763345)
                  ·
                    refine ⟨5066513617913175940322509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6755351490550901253763345 5066513617913175940322509)
                    ·
                      refine ⟨1899942606717440977620941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5066513617913175940322509 1899942606717440977620941)
                      ·
                        rfl

theorem cell23_3700125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 3, 1, 2, 2, 3].length) (baseStart_3700125 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3700125 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3700125 prefixEnd_3700125 := by exact prefixLift 3700125
  have htrace : WordTrace (prefixWord ++ tailWord_3700125) baseStart_3700125 baseEnd_3700125 := by
    simpa [prefixWord, tailWord_3700125, baseEnd_3700125] using wordTrace_append hprefix tailTrace_3700125
  have hstable : (prefixWord ++ tailWord_3700125).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3700125).length < 2 ^ (prefixWord ++ tailWord_3700125).sum := by decide
  have hdescent : baseEnd_3700125 < baseStart_3700125 := by decide
  rcases family_descends (prefixWord ++ tailWord_3700125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3700182 : List Nat := [5, 2, 1, 1, 1, 2, 2, 1, 1, 5, 2]
def baseStart_3700182 : Nat := 118140960795 + 3700182 * 2 ^ 59
def prefixEnd_3700182 : Nat := 4983230072969 + 3 ^ 40 * 3700182 * 2
def baseEnd_3700182 : Nat := 1899971875114747254608179

theorem tailTrace_3700182 : CollatzResearch.WordTrace tailWord_3700182 prefixEnd_3700182 1899971875114747254608179 := by
  unfold tailWord_3700182
  simp only [CollatzResearch.WordTrace]
  refine ⟨8434795292555001851208425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 89971149787253353079556533 8434795292555001851208425)
  ·
    refine ⟨6326096469416251388406319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8434795292555001851208425 6326096469416251388406319)
    ·
      refine ⟨9489144704124377082609479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6326096469416251388406319 9489144704124377082609479)
      ·
        refine ⟨14233717056186565623914219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9489144704124377082609479 14233717056186565623914219)
        ·
          refine ⟨21350575584279848435871329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14233717056186565623914219 21350575584279848435871329)
          ·
            refine ⟨16012931688209886326903497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21350575584279848435871329 16012931688209886326903497)
            ·
              refine ⟨12009698766157414745177623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16012931688209886326903497 12009698766157414745177623)
              ·
                refine ⟨18014548149236122117766435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12009698766157414745177623 18014548149236122117766435)
                ·
                  refine ⟨27021822223854183176649653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18014548149236122117766435 27021822223854183176649653)
                  ·
                    refine ⟨2533295833486329672810905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 27021822223854183176649653 2533295833486329672810905)
                    ·
                      refine ⟨1899971875114747254608179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2533295833486329672810905 1899971875114747254608179)
                      ·
                        rfl

theorem cell23_3700182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 2, 1, 1, 5, 2].length) (baseStart_3700182 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3700182 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3700182 prefixEnd_3700182 := by exact prefixLift 3700182
  have htrace : WordTrace (prefixWord ++ tailWord_3700182) baseStart_3700182 baseEnd_3700182 := by
    simpa [prefixWord, tailWord_3700182, baseEnd_3700182] using wordTrace_append hprefix tailTrace_3700182
  have hstable : (prefixWord ++ tailWord_3700182).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3700182).length < 2 ^ (prefixWord ++ tailWord_3700182).sum := by decide
  have hdescent : baseEnd_3700182 < baseStart_3700182 := by decide
  rcases family_descends (prefixWord ++ tailWord_3700182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3700189 : List Nat := [1, 4, 3, 1, 1, 2, 3, 3, 1, 1, 3]
def baseStart_3700189 : Nat := 118140960795 + 3700189 * 2 ^ 59
def prefixEnd_3700189 : Nat := 4983230072969 + 3 ^ 40 * 3700189 * 2
def baseEnd_3700189 : Nat := 1899975469479328727220647

theorem tailTrace_3700189 : CollatzResearch.WordTrace tailWord_3700189 prefixEnd_3700189 1899975469479328727220647 := by
  unfold tailWord_3700189
  simp only [CollatzResearch.WordTrace]
  refine ⟨134956979991854669814839621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89971319994569779876559747 134956979991854669814839621)
  ·
    refine ⟨25304433748472750590282429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 134956979991854669814839621 25304433748472750590282429)
    ·
      refine ⟨9489162655677281471355911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25304433748472750590282429 9489162655677281471355911)
      ·
        refine ⟨14233743983515922207033867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9489162655677281471355911 14233743983515922207033867)
        ·
          refine ⟨21350615975273883310550801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14233743983515922207033867 21350615975273883310550801)
          ·
            refine ⟨16012961981455412482913101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21350615975273883310550801 16012961981455412482913101)
            ·
              refine ⟨6004860743045779681092413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16012961981455412482913101 6004860743045779681092413)
              ·
                refine ⟨2251822778642167380409655, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6004860743045779681092413 2251822778642167380409655)
                ·
                  refine ⟨3377734167963251070614483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2251822778642167380409655 3377734167963251070614483)
                  ·
                    refine ⟨5066601251944876605921725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3377734167963251070614483 5066601251944876605921725)
                    ·
                      refine ⟨1899975469479328727220647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5066601251944876605921725 1899975469479328727220647)
                      ·
                        rfl

theorem cell23_3700189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 3, 3, 1, 1, 3].length) (baseStart_3700189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3700189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3700189 prefixEnd_3700189 := by exact prefixLift 3700189
  have htrace : WordTrace (prefixWord ++ tailWord_3700189) baseStart_3700189 baseEnd_3700189 := by
    simpa [prefixWord, tailWord_3700189, baseEnd_3700189] using wordTrace_append hprefix tailTrace_3700189
  have hstable : (prefixWord ++ tailWord_3700189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3700189).length < 2 ^ (prefixWord ++ tailWord_3700189).sum := by decide
  have hdescent : baseEnd_3700189 < baseStart_3700189 := by decide
  rcases family_descends (prefixWord ++ tailWord_3700189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3700195 : List Nat := [1, 1, 1, 6, 2, 1, 2, 3, 1, 1, 4]
def baseStart_3700195 : Nat := 118140960795 + 3700195 * 2 ^ 59
def prefixEnd_3700195 : Nat := 4983230072969 + 3 ^ 40 * 3700195 * 2
def baseEnd_3700195 : Nat := 1899978550363255703745619

theorem tailTrace_3700195 : CollatzResearch.WordTrace tailWord_3700195 prefixEnd_3700195 1899978550363255703745619 := by
  unfold tailWord_3700195
  simp only [CollatzResearch.WordTrace]
  refine ⟨134957198829832932839558039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89971465886555288559705359 134957198829832932839558039)
  ·
    refine ⟨202435798244749399259337059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134957198829832932839558039 202435798244749399259337059)
    ·
      refine ⟨303653697367124098889005589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 202435798244749399259337059 303653697367124098889005589)
      ·
        refine ⟨14233767064083942135422137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 303653697367124098889005589 14233767064083942135422137)
        ·
          refine ⟨10675325298062956601566603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14233767064083942135422137 10675325298062956601566603)
          ·
            refine ⟨16012987947094434902349905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10675325298062956601566603 16012987947094434902349905)
            ·
              refine ⟨12009740960320826176762429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16012987947094434902349905 12009740960320826176762429)
              ·
                refine ⟨4503652860120309816285911, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12009740960320826176762429 4503652860120309816285911)
                ·
                  refine ⟨6755479290180464724428867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4503652860120309816285911 6755479290180464724428867)
                  ·
                    refine ⟨10133218935270697086643301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6755479290180464724428867 10133218935270697086643301)
                    ·
                      refine ⟨1899978550363255703745619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10133218935270697086643301 1899978550363255703745619)
                      ·
                        rfl

theorem cell23_3700195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 2, 3, 1, 1, 4].length) (baseStart_3700195 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3700195 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3700195 prefixEnd_3700195 := by exact prefixLift 3700195
  have htrace : WordTrace (prefixWord ++ tailWord_3700195) baseStart_3700195 baseEnd_3700195 := by
    simpa [prefixWord, tailWord_3700195, baseEnd_3700195] using wordTrace_append hprefix tailTrace_3700195
  have hstable : (prefixWord ++ tailWord_3700195).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3700195).length < 2 ^ (prefixWord ++ tailWord_3700195).sum := by decide
  have hdescent : baseEnd_3700195 < baseStart_3700195 := by decide
  rcases family_descends (prefixWord ++ tailWord_3700195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3700245 : List Nat := [1, 3, 2, 1, 3, 3, 1, 2, 1, 3, 3]
def baseStart_3700245 : Nat := 118140960795 + 3700245 * 2 ^ 59
def prefixEnd_3700245 : Nat := 4983230072969 + 3 ^ 40 * 3700245 * 2
def baseEnd_3700245 : Nat := 1900004224395980508120389

theorem tailTrace_3700245 : CollatzResearch.WordTrace tailWord_3700245 prefixEnd_3700245 1900004224395980508120389 := by
  unfold tailWord_3700245
  simp only [CollatzResearch.WordTrace]
  refine ⟨134959022479651791378878189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89972681653101194252585459 134959022479651791378878189)
  ·
    refine ⟨50609633429869421767079321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 134959022479651791378878189 50609633429869421767079321)
    ·
      refine ⟨37957225072402066325309491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50609633429869421767079321 37957225072402066325309491)
      ·
        refine ⟨56935837608603099487964237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37957225072402066325309491 56935837608603099487964237)
        ·
          refine ⟨21350939103226162307986589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56935837608603099487964237 21350939103226162307986589)
          ·
            refine ⟨8006602163709810865494971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21350939103226162307986589 8006602163709810865494971)
            ·
              refine ⟨12009903245564716298242457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8006602163709810865494971 12009903245564716298242457)
              ·
                refine ⟨9007427434173537223681843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12009903245564716298242457 9007427434173537223681843)
                ·
                  refine ⟨13511141151260305835522765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9007427434173537223681843 13511141151260305835522765)
                  ·
                    refine ⟨5066677931722614688321037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13511141151260305835522765 5066677931722614688321037)
                    ·
                      refine ⟨1900004224395980508120389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5066677931722614688321037 1900004224395980508120389)
                      ·
                        rfl

theorem cell23_3700245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 3, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 3, 1, 2, 1, 3, 3].length) (baseStart_3700245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3700245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3700245 prefixEnd_3700245 := by exact prefixLift 3700245
  have htrace : WordTrace (prefixWord ++ tailWord_3700245) baseStart_3700245 baseEnd_3700245 := by
    simpa [prefixWord, tailWord_3700245, baseEnd_3700245] using wordTrace_append hprefix tailTrace_3700245
  have hstable : (prefixWord ++ tailWord_3700245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3700245).length < 2 ^ (prefixWord ++ tailWord_3700245).sum := by decide
  have hdescent : baseEnd_3700245 < baseStart_3700245 := by decide
  rcases family_descends (prefixWord ++ tailWord_3700245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3700258 : List Nat := [3, 3, 1, 1, 1, 1, 2, 2, 2, 2, 5]
def baseStart_3700258 : Nat := 118140960795 + 3700258 * 2 ^ 59
def prefixEnd_3700258 : Nat := 4983230072969 + 3 ^ 40 * 3700258 * 2
def baseEnd_3700258 : Nat := 1900010899644488957257829

theorem tailTrace_3700258 : CollatzResearch.WordTrace tailWord_3700258 prefixEnd_3700258 1900010899644488957257829 := by
  unfold tailWord_3700258
  simp only [CollatzResearch.WordTrace]
  refine ⟨33739874157151173649775357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89972997752403129732734285 33739874157151173649775357)
  ·
    refine ⟨12652452808931690118665759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33739874157151173649775357 12652452808931690118665759)
    ·
      refine ⟨18978679213397535177998639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12652452808931690118665759 18978679213397535177998639)
      ·
        refine ⟨28468018820096302766997959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18978679213397535177998639 28468018820096302766997959)
        ·
          refine ⟨42702028230144454150496939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28468018820096302766997959 42702028230144454150496939)
          ·
            refine ⟨64053042345216681225745409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42702028230144454150496939 64053042345216681225745409)
            ·
              refine ⟨48039781758912510919309057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64053042345216681225745409 48039781758912510919309057)
              ·
                refine ⟨36029836319184383189481793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48039781758912510919309057 36029836319184383189481793)
                ·
                  refine ⟨27022377239388287392111345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36029836319184383189481793 27022377239388287392111345)
                  ·
                    refine ⟨20266782929541215544083509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27022377239388287392111345 20266782929541215544083509)
                    ·
                      refine ⟨1900010899644488957257829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20266782929541215544083509 1900010899644488957257829)
                      ·
                        rfl

theorem cell23_3700258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 2, 2, 2, 2, 5].length) (baseStart_3700258 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3700258 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3700258 prefixEnd_3700258 := by exact prefixLift 3700258
  have htrace : WordTrace (prefixWord ++ tailWord_3700258) baseStart_3700258 baseEnd_3700258 := by
    simpa [prefixWord, tailWord_3700258, baseEnd_3700258] using wordTrace_append hprefix tailTrace_3700258
  have hstable : (prefixWord ++ tailWord_3700258).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3700258).length < 2 ^ (prefixWord ++ tailWord_3700258).sum := by decide
  have hdescent : baseEnd_3700258 < baseStart_3700258 := by decide
  rcases family_descends (prefixWord ++ tailWord_3700258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3700288 : List Nat := [2, 1, 1, 2, 2, 2, 1, 1, 4, 4, 3]
def baseStart_3700288 : Nat := 118140960795 + 3700288 * 2 ^ 59
def prefixEnd_3700288 : Nat := 4983230072969 + 3 ^ 40 * 3700288 * 2
def baseEnd_3700288 : Nat := 1900026304064123839882691

theorem tailTrace_3700288 : CollatzResearch.WordTrace tailWord_3700288 prefixEnd_3700288 1900026304064123839882691 := by
  unfold tailWord_3700288
  simp only [CollatzResearch.WordTrace]
  refine ⟨67480295409248004861346759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89973727212330673148462345 67480295409248004861346759)
  ·
    refine ⟨101220443113872007292020139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67480295409248004861346759 101220443113872007292020139)
    ·
      refine ⟨151830664670808010938030209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101220443113872007292020139 151830664670808010938030209)
      ·
        refine ⟨113872998503106008203522657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 151830664670808010938030209 113872998503106008203522657)
        ·
          refine ⟨85404748877329506152641993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 113872998503106008203522657 85404748877329506152641993)
          ·
            refine ⟨64053561657997129614481495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85404748877329506152641993 64053561657997129614481495)
            ·
              refine ⟨96080342486995694421722243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64053561657997129614481495 96080342486995694421722243)
              ·
                refine ⟨144120513730493541632583365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 96080342486995694421722243 144120513730493541632583365)
                ·
                  refine ⟨27022596324467539056109381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 144120513730493541632583365 27022596324467539056109381)
                  ·
                    refine ⟨5066736810837663573020509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27022596324467539056109381 5066736810837663573020509)
                    ·
                      refine ⟨1900026304064123839882691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5066736810837663573020509 1900026304064123839882691)
                      ·
                        rfl

theorem cell23_3700288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 1, 4, 4, 3].length) (baseStart_3700288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3700288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3700288 prefixEnd_3700288 := by exact prefixLift 3700288
  have htrace : WordTrace (prefixWord ++ tailWord_3700288) baseStart_3700288 baseEnd_3700288 := by
    simpa [prefixWord, tailWord_3700288, baseEnd_3700288] using wordTrace_append hprefix tailTrace_3700288
  have hstable : (prefixWord ++ tailWord_3700288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3700288).length < 2 ^ (prefixWord ++ tailWord_3700288).sum := by decide
  have hdescent : baseEnd_3700288 < baseStart_3700288 := by decide
  rcases family_descends (prefixWord ++ tailWord_3700288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3700298 : List Nat := [3, 1, 2, 1, 1, 3, 1, 2, 1, 4, 4]
def baseStart_3700298 : Nat := 118140960795 + 3700298 * 2 ^ 59
def prefixEnd_3700298 : Nat := 4983230072969 + 3 ^ 40 * 3700298 * 2
def baseEnd_3700298 : Nat := 1900031438870668800757645

theorem tailTrace_3700298 : CollatzResearch.WordTrace tailWord_3700298 prefixEnd_3700298 1900031438870668800757645 := by
  unfold tailWord_3700298
  simp only [CollatzResearch.WordTrace]
  refine ⟨33740238887114945357639387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89973970365639854287038365 33740238887114945357639387)
  ·
    refine ⟨50610358330672418036459081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33740238887114945357639387 50610358330672418036459081)
    ·
      refine ⟨37957768748004313527344311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50610358330672418036459081 37957768748004313527344311)
      ·
        refine ⟨56936653122006470291016467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37957768748004313527344311 56936653122006470291016467)
        ·
          refine ⟨85404979683009705436524701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56936653122006470291016467 85404979683009705436524701)
          ·
            refine ⟨32026867381128639538696763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 85404979683009705436524701 32026867381128639538696763)
            ·
              refine ⟨48040301071692959308045145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32026867381128639538696763 48040301071692959308045145)
              ·
                refine ⟨36030225803769719481033859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48040301071692959308045145 36030225803769719481033859)
                ·
                  refine ⟨54045338705654579221550789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36030225803769719481033859 54045338705654579221550789)
                  ·
                    refine ⟨10133501007310233604040773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 54045338705654579221550789 10133501007310233604040773)
                    ·
                      refine ⟨1900031438870668800757645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10133501007310233604040773 1900031438870668800757645)
                      ·
                        rfl

theorem cell23_3700298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 1, 2, 1, 4, 4].length) (baseStart_3700298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3700298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3700298 prefixEnd_3700298 := by exact prefixLift 3700298
  have htrace : WordTrace (prefixWord ++ tailWord_3700298) baseStart_3700298 baseEnd_3700298 := by
    simpa [prefixWord, tailWord_3700298, baseEnd_3700298] using wordTrace_append hprefix tailTrace_3700298
  have hstable : (prefixWord ++ tailWord_3700298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3700298).length < 2 ^ (prefixWord ++ tailWord_3700298).sum := by decide
  have hdescent : baseEnd_3700298 < baseStart_3700298 := by decide
  rcases family_descends (prefixWord ++ tailWord_3700298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3700302 : List Nat := [4, 1, 1, 1, 1, 2, 1, 4, 4, 2, 2]
def baseStart_3700302 : Nat := 118140960795 + 3700302 * 2 ^ 59
def prefixEnd_3700302 : Nat := 4983230072969 + 3 ^ 40 * 3700302 * 2
def baseEnd_3700302 : Nat := 1900033492793286785107627

theorem tailTrace_3700302 : CollatzResearch.WordTrace tailWord_3700302 prefixEnd_3700302 1900033492793286785107627 := by
  unfold tailWord_3700302
  simp only [CollatzResearch.WordTrace]
  refine ⟨16870137680055661264212895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 89974067626963526742468773 16870137680055661264212895)
  ·
    refine ⟨25305206520083491896319343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16870137680055661264212895 25305206520083491896319343)
    ·
      refine ⟨37957809780125237844479015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25305206520083491896319343 37957809780125237844479015)
      ·
        refine ⟨56936714670187856766718523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37957809780125237844479015 56936714670187856766718523)
        ·
          refine ⟨85405072005281785150077785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56936714670187856766718523 85405072005281785150077785)
          ·
            refine ⟨64053804003961338862558339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85405072005281785150077785 64053804003961338862558339)
            ·
              refine ⟨96080706005942008293837509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64053804003961338862558339 96080706005942008293837509)
              ·
                refine ⟨18015132376114126555094533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 96080706005942008293837509 18015132376114126555094533)
                ·
                  refine ⟨3377837320521398729080225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18015132376114126555094533 3377837320521398729080225)
                  ·
                    refine ⟨2533377990391049046810169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3377837320521398729080225 2533377990391049046810169)
                    ·
                      refine ⟨1900033492793286785107627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2533377990391049046810169 1900033492793286785107627)
                      ·
                        rfl

theorem cell23_3700302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 4, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 4, 4, 2, 2].length) (baseStart_3700302 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3700302 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3700302 prefixEnd_3700302 := by exact prefixLift 3700302
  have htrace : WordTrace (prefixWord ++ tailWord_3700302) baseStart_3700302 baseEnd_3700302 := by
    simpa [prefixWord, tailWord_3700302, baseEnd_3700302] using wordTrace_append hprefix tailTrace_3700302
  have hstable : (prefixWord ++ tailWord_3700302).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3700302).length < 2 ^ (prefixWord ++ tailWord_3700302).sum := by decide
  have hdescent : baseEnd_3700302 < baseStart_3700302 := by decide
  rcases family_descends (prefixWord ++ tailWord_3700302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3700306 : List Nat := [3, 2, 2, 1, 2, 4, 2, 1, 1, 3, 2]
def baseStart_3700306 : Nat := 118140960795 + 3700306 * 2 ^ 59
def prefixEnd_3700306 : Nat := 4983230072969 + 3 ^ 40 * 3700306 * 2
def baseEnd_3700306 : Nat := 1900035546715904769457609

theorem tailTrace_3700306 : CollatzResearch.WordTrace tailWord_3700306 prefixEnd_3700306 1900035546715904769457609 := by
  unfold tailWord_3700306
  simp only [CollatzResearch.WordTrace]
  refine ⟨33740311833107699699212193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89974164888287199197899181 33740311833107699699212193)
  ·
    refine ⟨25305233874830774774409145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33740311833107699699212193 25305233874830774774409145)
    ·
      refine ⟨18978925406123081080806859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25305233874830774774409145 18978925406123081080806859)
      ·
        refine ⟨28468388109184621621210289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18978925406123081080806859 28468388109184621621210289)
        ·
          refine ⟨21351291081888466215907717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28468388109184621621210289 21351291081888466215907717)
          ·
            refine ⟨4003367077854087415482697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21351291081888466215907717 4003367077854087415482697)
            ·
              refine ⟨3002525308390565561612023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4003367077854087415482697 3002525308390565561612023)
              ·
                refine ⟨4503787962585848342418035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3002525308390565561612023 4503787962585848342418035)
                ·
                  refine ⟨6755681943878772513627053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4503787962585848342418035 6755681943878772513627053)
                  ·
                    refine ⟨2533380728954539692610145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6755681943878772513627053 2533380728954539692610145)
                    ·
                      refine ⟨1900035546715904769457609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2533380728954539692610145 1900035546715904769457609)
                      ·
                        rfl

theorem cell23_3700306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 4, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 4, 2, 1, 1, 3, 2].length) (baseStart_3700306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3700306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3700306 prefixEnd_3700306 := by exact prefixLift 3700306
  have htrace : WordTrace (prefixWord ++ tailWord_3700306) baseStart_3700306 baseEnd_3700306 := by
    simpa [prefixWord, tailWord_3700306, baseEnd_3700306] using wordTrace_append hprefix tailTrace_3700306
  have hstable : (prefixWord ++ tailWord_3700306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3700306).length < 2 ^ (prefixWord ++ tailWord_3700306).sum := by decide
  have hdescent : baseEnd_3700306 < baseStart_3700306 := by decide
  rcases family_descends (prefixWord ++ tailWord_3700306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3700308 : List Nat := [2, 4, 1, 1, 1, 2, 1, 2, 9]
def baseStart_3700308 : Nat := 118140960795 + 3700308 * 2 ^ 59
def prefixEnd_3700308 : Nat := 4983230072969 + 3 ^ 40 * 3700308 * 2
def baseEnd_3700308 : Nat := 211115174853023751292511

theorem tailTrace_3700308 : CollatzResearch.WordTrace tailWord_3700308 prefixEnd_3700308 211115174853023751292511 := by
  unfold tailWord_3700308
  simp only [CollatzResearch.WordTrace]
  refine ⟨67480660139211776569210789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89974213518949035425614385 67480660139211776569210789)
  ·
    refine ⟨12652623776102208106727023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 67480660139211776569210789 12652623776102208106727023)
    ·
      refine ⟨18978935664153312160090535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12652623776102208106727023 18978935664153312160090535)
      ·
        refine ⟨28468403496229968240135803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18978935664153312160090535 28468403496229968240135803)
        ·
          refine ⟨42702605244344952360203705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28468403496229968240135803 42702605244344952360203705)
          ·
            refine ⟨32026953933258714270152779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42702605244344952360203705 32026953933258714270152779)
            ·
              refine ⟨48040430899888071405229169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32026953933258714270152779 48040430899888071405229169)
              ·
                refine ⟨36030323174916053553921877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48040430899888071405229169 36030323174916053553921877)
                ·
                  refine ⟨211115174853023751292511, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 36030323174916053553921877 211115174853023751292511)
                  ·
                    rfl

theorem cell23_3700308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 1, 2, 9].length) (baseStart_3700308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3700308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3700308 prefixEnd_3700308 := by exact prefixLift 3700308
  have htrace : WordTrace (prefixWord ++ tailWord_3700308) baseStart_3700308 baseEnd_3700308 := by
    simpa [prefixWord, tailWord_3700308, baseEnd_3700308] using wordTrace_append hprefix tailTrace_3700308
  have hstable : (prefixWord ++ tailWord_3700308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3700308).length < 2 ^ (prefixWord ++ tailWord_3700308).sum := by decide
  have hdescent : baseEnd_3700308 < baseStart_3700308 := by decide
  rcases family_descends (prefixWord ++ tailWord_3700308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3700325 : List Nat := [1, 3, 1, 3, 3, 2, 2, 1, 7]
def baseStart_3700325 : Nat := 118140960795 + 3700325 * 2 ^ 59
def prefixEnd_3700325 : Nat := 4983230072969 + 3 ^ 40 * 3700325 * 2
def baseEnd_3700325 : Nat := 211116144760926688346669

theorem tailTrace_3700325 : CollatzResearch.WordTrace tailWord_3700325 prefixEnd_3700325 211116144760926688346669 := by
  unfold tailWord_3700325
  simp only [CollatzResearch.WordTrace]
  refine ⟨134961940319361965041790429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89974626879574643361193619 134961940319361965041790429)
  ·
    refine ⟨50610727619760736890671411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 134961940319361965041790429 50610727619760736890671411)
    ·
      refine ⟨75916091429641105336007117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50610727619760736890671411 75916091429641105336007117)
      ·
        refine ⟨28468534286115414501002669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 75916091429641105336007117 28468534286115414501002669)
        ·
          refine ⟨10675700357293280437876001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28468534286115414501002669 10675700357293280437876001)
          ·
            refine ⟨8006775267969960328407001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10675700357293280437876001 8006775267969960328407001)
            ·
              refine ⟨6005081450977470246305251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8006775267969960328407001 6005081450977470246305251)
              ·
                refine ⟨9007622176466205369457877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6005081450977470246305251 9007622176466205369457877)
                ·
                  refine ⟨211116144760926688346669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9007622176466205369457877 211116144760926688346669)
                  ·
                    rfl

theorem cell23_3700325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 2, 2, 1, 7].length) (baseStart_3700325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3700325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3700325 prefixEnd_3700325 := by exact prefixLift 3700325
  have htrace : WordTrace (prefixWord ++ tailWord_3700325) baseStart_3700325 baseEnd_3700325 := by
    simpa [prefixWord, tailWord_3700325, baseEnd_3700325] using wordTrace_append hprefix tailTrace_3700325
  have hstable : (prefixWord ++ tailWord_3700325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3700325).length < 2 ^ (prefixWord ++ tailWord_3700325).sum := by decide
  have hdescent : baseEnd_3700325 < baseStart_3700325 := by decide
  rcases family_descends (prefixWord ++ tailWord_3700325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3700336 : List Nat := [2, 1, 1, 1, 6, 2, 3, 1, 2, 2, 2]
def baseStart_3700336 : Nat := 118140960795 + 3700336 * 2 ^ 59
def prefixEnd_3700336 : Nat := 4983230072969 + 3 ^ 40 * 3700336 * 2
def baseEnd_3700336 : Nat := 1900050951135539652082471

theorem tailTrace_3700336 : CollatzResearch.WordTrace tailWord_3700336 prefixEnd_3700336 1900050951135539652082471 := by
  unfold tailWord_3700336
  simp only [CollatzResearch.WordTrace]
  refine ⟨67481170761161056960220431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89974894348214742613627241 67481170761161056960220431)
  ·
    refine ⟨101221756141741585440330647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67481170761161056960220431 101221756141741585440330647)
    ·
      refine ⟨151832634212612378160495971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101221756141741585440330647 151832634212612378160495971)
      ·
        refine ⟨227748951318918567240743957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151832634212612378160495971 227748951318918567240743957)
        ·
          refine ⟨10675732093074307839409873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 227748951318918567240743957 10675732093074307839409873)
          ·
            refine ⟨8006799069805730879557405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10675732093074307839409873 8006799069805730879557405)
            ·
              refine ⟨3002549651177149079834027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8006799069805730879557405 3002549651177149079834027)
              ·
                refine ⟨4503824476765723619751041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3002549651177149079834027 4503824476765723619751041)
                ·
                  refine ⟨3377868357574292714813281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4503824476765723619751041 3377868357574292714813281)
                  ·
                    refine ⟨2533401268180719536109961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3377868357574292714813281 2533401268180719536109961)
                    ·
                      refine ⟨1900050951135539652082471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2533401268180719536109961 1900050951135539652082471)
                      ·
                        rfl

theorem cell23_3700336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 2, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 2, 3, 1, 2, 2, 2].length) (baseStart_3700336 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3700336 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3700336 prefixEnd_3700336 := by exact prefixLift 3700336
  have htrace : WordTrace (prefixWord ++ tailWord_3700336) baseStart_3700336 baseEnd_3700336 := by
    simpa [prefixWord, tailWord_3700336, baseEnd_3700336] using wordTrace_append hprefix tailTrace_3700336
  have hstable : (prefixWord ++ tailWord_3700336).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3700336).length < 2 ^ (prefixWord ++ tailWord_3700336).sum := by decide
  have hdescent : baseEnd_3700336 < baseStart_3700336 := by decide
  rcases family_descends (prefixWord ++ tailWord_3700336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3700348 : List Nat := [2, 2, 2, 1, 1, 2, 1, 2, 3, 2, 5]
def baseStart_3700348 : Nat := 118140960795 + 3700348 * 2 ^ 59
def prefixEnd_3700348 : Nat := 4983230072969 + 3 ^ 40 * 3700348 * 2
def baseEnd_3700348 : Nat := 1900057112903393605132415

theorem tailTrace_3700348 : CollatzResearch.WordTrace tailWord_3700348 prefixEnd_3700348 1900057112903393605132415 := by
  unfold tailWord_3700348
  simp only [CollatzResearch.WordTrace]
  refine ⟨67481389599139319984938849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89975186132185759979918465 67481389599139319984938849)
  ·
    refine ⟨50611042199354489988704137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67481389599139319984938849 50611042199354489988704137)
    ·
      refine ⟨37958281649515867491528103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50611042199354489988704137 37958281649515867491528103)
      ·
        refine ⟨56937422474273801237292155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37958281649515867491528103 56937422474273801237292155)
        ·
          refine ⟨85406133711410701855938233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56937422474273801237292155 85406133711410701855938233)
          ·
            refine ⟨64054600283558026391953675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85406133711410701855938233 64054600283558026391953675)
            ·
              refine ⟨96081900425337039587930513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64054600283558026391953675 96081900425337039587930513)
              ·
                refine ⟨72061425319002779690947885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 96081900425337039587930513 72061425319002779690947885)
                ·
                  refine ⟨27023034494626042384105457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 72061425319002779690947885 27023034494626042384105457)
                  ·
                    refine ⟨20267275870969531788079093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27023034494626042384105457 20267275870969531788079093)
                    ·
                      refine ⟨1900057112903393605132415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20267275870969531788079093 1900057112903393605132415)
                      ·
                        rfl

theorem cell23_3700348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 2, 3, 2, 5].length) (baseStart_3700348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3700348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3700348 prefixEnd_3700348 := by exact prefixLift 3700348
  have htrace : WordTrace (prefixWord ++ tailWord_3700348) baseStart_3700348 baseEnd_3700348 := by
    simpa [prefixWord, tailWord_3700348, baseEnd_3700348] using wordTrace_append hprefix tailTrace_3700348
  have hstable : (prefixWord ++ tailWord_3700348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3700348).length < 2 ^ (prefixWord ++ tailWord_3700348).sum := by decide
  have hdescent : baseEnd_3700348 < baseStart_3700348 := by decide
  rcases family_descends (prefixWord ++ tailWord_3700348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3700375 : List Nat := [1, 1, 3, 3, 2, 2, 1, 1, 4, 1, 4]
def baseStart_3700375 : Nat := 118140960795 + 3700375 * 2 ^ 59
def prefixEnd_3700375 : Nat := 4983230072969 + 3 ^ 40 * 3700375 * 2
def baseEnd_3700375 : Nat := 1900070976881064999494791

theorem tailTrace_3700375 : CollatzResearch.WordTrace tailWord_3700375 prefixEnd_3700375 1900070976881064999494791 := by
  unfold tailWord_3700375
  simp only [CollatzResearch.WordTrace]
  refine ⟨134963763969180823581110579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89975842646120549054073719 134963763969180823581110579)
  ·
    refine ⟨202445645953771235371665869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134963763969180823581110579 202445645953771235371665869)
    ·
      refine ⟨75917117232664213264374701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 202445645953771235371665869 75917117232664213264374701)
      ·
        refine ⟨28468918962249079974140513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 75917117232664213264374701 28468918962249079974140513)
        ·
          refine ⟨21351689221686809980605385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28468918962249079974140513 21351689221686809980605385)
          ·
            refine ⟨16013766916265107485454039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21351689221686809980605385 16013766916265107485454039)
            ·
              refine ⟨24020650374397661228181059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16013766916265107485454039 24020650374397661228181059)
              ·
                refine ⟨36030975561596491842271589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24020650374397661228181059 36030975561596491842271589)
                ·
                  refine ⟨6755807917799342220425923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36030975561596491842271589 6755807917799342220425923)
                  ·
                    refine ⟨10133711876699013330638885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6755807917799342220425923 10133711876699013330638885)
                    ·
                      refine ⟨1900070976881064999494791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10133711876699013330638885 1900070976881064999494791)
                      ·
                        rfl

theorem cell23_3700375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 1, 1, 4, 1, 4].length) (baseStart_3700375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3700375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3700375 prefixEnd_3700375 := by exact prefixLift 3700375
  have htrace : WordTrace (prefixWord ++ tailWord_3700375) baseStart_3700375 baseEnd_3700375 := by
    simpa [prefixWord, tailWord_3700375, baseEnd_3700375] using wordTrace_append hprefix tailTrace_3700375
  have hstable : (prefixWord ++ tailWord_3700375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3700375).length < 2 ^ (prefixWord ++ tailWord_3700375).sum := by decide
  have hdescent : baseEnd_3700375 < baseStart_3700375 := by decide
  rcases family_descends (prefixWord ++ tailWord_3700375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3700382 : List Nat := [4, 3, 1, 1, 1, 3, 1, 1, 1, 2, 5]
def baseStart_3700382 : Nat := 118140960795 + 3700382 * 2 ^ 59
def prefixEnd_3700382 : Nat := 4983230072969 + 3 ^ 40 * 3700382 * 2
def baseEnd_3700382 : Nat := 1900074571245646472107259

theorem tailTrace_3700382 : CollatzResearch.WordTrace tailWord_3700382 prefixEnd_3700382 1900074571245646472107259 := by
  unfold tailWord_3700382
  simp only [CollatzResearch.WordTrace]
  refine ⟨16870502410019432972076925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 89976012853436975851076933 16870502410019432972076925)
  ·
    refine ⟨6326438403757287364528847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16870502410019432972076925 6326438403757287364528847)
    ·
      refine ⟨9489657605635931046793271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6326438403757287364528847 9489657605635931046793271)
      ·
        refine ⟨14234486408453896570189907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9489657605635931046793271 14234486408453896570189907)
        ·
          refine ⟨21351729612680844855284861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14234486408453896570189907 21351729612680844855284861)
          ·
            refine ⟨8006898604755316820731823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21351729612680844855284861 8006898604755316820731823)
            ·
              refine ⟨12010347907132975231097735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8006898604755316820731823 12010347907132975231097735)
              ·
                refine ⟨18015521860699462846646603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12010347907132975231097735 18015521860699462846646603)
                ·
                  refine ⟨27023282791049194269969905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18015521860699462846646603 27023282791049194269969905)
                  ·
                    refine ⟨20267462093286895702477429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27023282791049194269969905 20267462093286895702477429)
                    ·
                      refine ⟨1900074571245646472107259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20267462093286895702477429 1900074571245646472107259)
                      ·
                        rfl

theorem cell23_3700382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 3, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 3, 1, 1, 1, 2, 5].length) (baseStart_3700382 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3700382 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3700382 prefixEnd_3700382 := by exact prefixLift 3700382
  have htrace : WordTrace (prefixWord ++ tailWord_3700382) baseStart_3700382 baseEnd_3700382 := by
    simpa [prefixWord, tailWord_3700382, baseEnd_3700382] using wordTrace_append hprefix tailTrace_3700382
  have hstable : (prefixWord ++ tailWord_3700382).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3700382).length < 2 ^ (prefixWord ++ tailWord_3700382).sum := by decide
  have hdescent : baseEnd_3700382 < baseStart_3700382 := by decide
  rcases family_descends (prefixWord ++ tailWord_3700382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3700412 : List Nat := [2, 2, 2, 3, 1, 2, 1, 3, 2, 2, 3]
def baseStart_3700412 : Nat := 118140960795 + 3700412 * 2 ^ 59
def prefixEnd_3700412 : Nat := 4983230072969 + 3 ^ 40 * 3700412 * 2
def baseEnd_3700412 : Nat := 1900089975665281354732121

theorem tailTrace_3700412 : CollatzResearch.WordTrace tailWord_3700412 prefixEnd_3700412 1900089975665281354732121 := by
  unfold tailWord_3700412
  simp only [CollatzResearch.WordTrace]
  refine ⟨67482556735023389450103745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89976742313364519266804993 67482556735023389450103745)
  ·
    refine ⟨50611917551267542087577809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67482556735023389450103745 50611917551267542087577809)
    ·
      refine ⟨37958938163450656565683357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50611917551267542087577809 37958938163450656565683357)
      ·
        refine ⟨14234601811293996212131259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37958938163450656565683357 14234601811293996212131259)
        ·
          refine ⟨21351902716940994318196889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14234601811293996212131259 21351902716940994318196889)
          ·
            refine ⟨16013927037705745738647667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21351902716940994318196889 16013927037705745738647667)
            ·
              refine ⟨24020890556558618607971501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16013927037705745738647667 24020890556558618607971501)
              ·
                refine ⟨9007833958709481977989313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24020890556558618607971501 9007833958709481977989313)
                ·
                  refine ⟨6755875469032111483491985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9007833958709481977989313 6755875469032111483491985)
                  ·
                    refine ⟨5066906601774083612618989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6755875469032111483491985 5066906601774083612618989)
                    ·
                      refine ⟨1900089975665281354732121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5066906601774083612618989 1900089975665281354732121)
                      ·
                        rfl

theorem cell23_3700412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 1, 3, 2, 2, 3].length) (baseStart_3700412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3700412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3700412 prefixEnd_3700412 := by exact prefixLift 3700412
  have htrace : WordTrace (prefixWord ++ tailWord_3700412) baseStart_3700412 baseEnd_3700412 := by
    simpa [prefixWord, tailWord_3700412, baseEnd_3700412] using wordTrace_append hprefix tailTrace_3700412
  have hstable : (prefixWord ++ tailWord_3700412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3700412).length < 2 ^ (prefixWord ++ tailWord_3700412).sum := by decide
  have hdescent : baseEnd_3700412 < baseStart_3700412 := by decide
  rcases family_descends (prefixWord ++ tailWord_3700412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3700436 : List Nat := [2, 4, 1, 3, 1, 2, 1, 4, 1, 4]
def baseStart_3700436 : Nat := 118140960795 + 3700436 * 2 ^ 59
def prefixEnd_3700436 : Nat := 4983230072969 + 3 ^ 40 * 3700436 * 2
def baseEnd_3700436 : Nat := 633367433066996420277337

theorem tailTrace_3700436 : CollatzResearch.WordTrace tailWord_3700436 prefixEnd_3700436 633367433066996420277337 := by
  unfold tailWord_3700436
  simp only [CollatzResearch.WordTrace]
  refine ⟨67482994410979915499540581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89977325881306553999387441 67482994410979915499540581)
  ·
    refine ⟨12653061452058734156163859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 67482994410979915499540581 12653061452058734156163859)
    ·
      refine ⟨18979592178088101234245789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12653061452058734156163859 18979592178088101234245789)
      ·
        refine ⟨7117347066783037962842171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18979592178088101234245789 7117347066783037962842171)
        ·
          refine ⟨10676020600174556944263257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7117347066783037962842171 10676020600174556944263257)
          ·
            refine ⟨8007015450130917708197443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10676020600174556944263257 8007015450130917708197443)
            ·
              refine ⟨12010523175196376562296165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8007015450130917708197443 12010523175196376562296165)
              ·
                refine ⟨2251973095349320605430531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12010523175196376562296165 2251973095349320605430531)
                ·
                  refine ⟨3377959643023980908145797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2251973095349320605430531 3377959643023980908145797)
                  ·
                    refine ⟨633367433066996420277337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3377959643023980908145797 633367433066996420277337)
                    ·
                      rfl

theorem cell23_3700436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 2, 1, 4, 1, 4].length) (baseStart_3700436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3700436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3700436 prefixEnd_3700436 := by exact prefixLift 3700436
  have htrace : WordTrace (prefixWord ++ tailWord_3700436) baseStart_3700436 baseEnd_3700436 := by
    simpa [prefixWord, tailWord_3700436, baseEnd_3700436] using wordTrace_append hprefix tailTrace_3700436
  have hstable : (prefixWord ++ tailWord_3700436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3700436).length < 2 ^ (prefixWord ++ tailWord_3700436).sum := by decide
  have hdescent : baseEnd_3700436 < baseStart_3700436 := by decide
  rcases family_descends (prefixWord ++ tailWord_3700436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3700452 : List Nat := [2, 3, 1, 1, 1, 3, 2, 2, 1, 5, 2]
def baseStart_3700452 : Nat := 118140960795 + 3700452 * 2 ^ 59
def prefixEnd_3700452 : Nat := 4983230072969 + 3 ^ 40 * 3700452 * 2
def baseEnd_3700452 : Nat := 1900110514891461198231937

theorem tailTrace_3700452 : CollatzResearch.WordTrace tailWord_3700452 prefixEnd_3700452 1900110514891461198231937 := by
  unfold tailWord_3700452
  simp only [CollatzResearch.WordTrace]
  refine ⟨67483286194950932865831805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89977714926601243821109073 67483286194950932865831805)
  ·
    refine ⟨25306232323106599824686927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67483286194950932865831805 25306232323106599824686927)
    ·
      refine ⟨37959348484659899737030391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25306232323106599824686927 37959348484659899737030391)
      ·
        refine ⟨56939022726989849605545587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37959348484659899737030391 56939022726989849605545587)
        ·
          refine ⟨85408534090484774408318381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56939022726989849605545587 85408534090484774408318381)
          ·
            refine ⟨32028200283931790403119393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 85408534090484774408318381 32028200283931790403119393)
            ·
              refine ⟨24021150212948842802339545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32028200283931790403119393 24021150212948842802339545)
              ·
                refine ⟨18015862659711632101754659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24021150212948842802339545 18015862659711632101754659)
                ·
                  refine ⟨27023793989567448152631989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18015862659711632101754659 27023793989567448152631989)
                  ·
                    refine ⟨2533480686521948264309249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 27023793989567448152631989 2533480686521948264309249)
                    ·
                      refine ⟨1900110514891461198231937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2533480686521948264309249 1900110514891461198231937)
                      ·
                        rfl

theorem cell23_3700452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 2, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 2, 2, 1, 5, 2].length) (baseStart_3700452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3700452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3700452 prefixEnd_3700452 := by exact prefixLift 3700452
  have htrace : WordTrace (prefixWord ++ tailWord_3700452) baseStart_3700452 baseEnd_3700452 := by
    simpa [prefixWord, tailWord_3700452, baseEnd_3700452] using wordTrace_append hprefix tailTrace_3700452
  have hstable : (prefixWord ++ tailWord_3700452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3700452).length < 2 ^ (prefixWord ++ tailWord_3700452).sum := by decide
  have hdescent : baseEnd_3700452 < baseStart_3700452 := by decide
  rcases family_descends (prefixWord ++ tailWord_3700452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3700462 : List Nat := [4, 1, 2, 1, 1, 2, 2, 4, 1, 5]
def baseStart_3700462 : Nat := 118140960795 + 3700462 * 2 ^ 59
def prefixEnd_3700462 : Nat := 4983230072969 + 3 ^ 40 * 3700462 * 2
def baseEnd_3700462 : Nat := 633371883232668719702297

theorem tailTrace_3700462 : CollatzResearch.WordTrace tailWord_3700462 prefixEnd_3700462 633371883232668719702297 := by
  unfold tailWord_3700462
  simp only [CollatzResearch.WordTrace]
  refine ⟨16870867139983204679940955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 89977958079910424959685093 16870867139983204679940955)
  ·
    refine ⟨25306300709974807019911433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16870867139983204679940955 25306300709974807019911433)
    ·
      refine ⟨18979725532481105264933575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25306300709974807019911433 18979725532481105264933575)
      ·
        refine ⟨28469588298721657897400363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18979725532481105264933575 28469588298721657897400363)
        ·
          refine ⟨42704382448082486846100545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28469588298721657897400363 42704382448082486846100545)
          ·
            refine ⟨32028286836061865134575409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42704382448082486846100545 32028286836061865134575409)
            ·
              refine ⟨24021215127046398850931557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32028286836061865134575409 24021215127046398850931557)
              ·
                refine ⟨4503977836321199784549667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24021215127046398850931557 4503977836321199784549667)
                ·
                  refine ⟨6755966754481799676824501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4503977836321199784549667 6755966754481799676824501)
                  ·
                    refine ⟨633371883232668719702297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6755966754481799676824501 633371883232668719702297)
                    ·
                      rfl

theorem cell23_3700462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 2, 4, 1, 5].length) (baseStart_3700462 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3700462 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3700462 prefixEnd_3700462 := by exact prefixLift 3700462
  have htrace : WordTrace (prefixWord ++ tailWord_3700462) baseStart_3700462 baseEnd_3700462 := by
    simpa [prefixWord, tailWord_3700462, baseEnd_3700462] using wordTrace_append hprefix tailTrace_3700462
  have hstable : (prefixWord ++ tailWord_3700462).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3700462).length < 2 ^ (prefixWord ++ tailWord_3700462).sum := by decide
  have hdescent : baseEnd_3700462 < baseStart_3700462 := by decide
  rcases family_descends (prefixWord ++ tailWord_3700462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3700476 : List Nat := [2, 2, 2, 1, 3, 1, 4, 3, 1, 1, 3]
def baseStart_3700476 : Nat := 118140960795 + 3700476 * 2 ^ 59
def prefixEnd_3700476 : Nat := 4983230072969 + 3 ^ 40 * 3700476 * 2
def baseEnd_3700476 : Nat := 1900122838427169104331827

theorem tailTrace_3700476 : CollatzResearch.WordTrace tailWord_3700476 prefixEnd_3700476 1900122838427169104331827 := by
  unfold tailWord_3700476
  simp only [CollatzResearch.WordTrace]
  refine ⟨67483723870907458915268641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89978298494543278553691521 67483723870907458915268641)
  ·
    refine ⟨50612792903180594186451481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67483723870907458915268641 50612792903180594186451481)
    ·
      refine ⟨37959594677385445639838611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50612792903180594186451481 37959594677385445639838611)
      ·
        refine ⟨56939392016078168459757917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37959594677385445639838611 56939392016078168459757917)
        ·
          refine ⟨21352272006029313172409219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56939392016078168459757917 21352272006029313172409219)
          ·
            refine ⟨32028408009043969758613829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21352272006029313172409219 32028408009043969758613829)
            ·
              refine ⟨6005326501695744329740093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32028408009043969758613829 6005326501695744329740093)
              ·
                refine ⟨2251997438135904123652535, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6005326501695744329740093 2251997438135904123652535)
                ·
                  refine ⟨3377996157203856185478803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2251997438135904123652535 3377996157203856185478803)
                  ·
                    refine ⟨5066994235805784278218205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3377996157203856185478803 5066994235805784278218205)
                    ·
                      refine ⟨1900122838427169104331827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5066994235805784278218205 1900122838427169104331827)
                      ·
                        rfl

theorem cell23_3700476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 4, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 4, 3, 1, 1, 3].length) (baseStart_3700476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3700476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3700476 prefixEnd_3700476 := by exact prefixLift 3700476
  have htrace : WordTrace (prefixWord ++ tailWord_3700476) baseStart_3700476 baseEnd_3700476 := by
    simpa [prefixWord, tailWord_3700476, baseEnd_3700476] using wordTrace_append hprefix tailTrace_3700476
  have hstable : (prefixWord ++ tailWord_3700476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3700476).length < 2 ^ (prefixWord ++ tailWord_3700476).sum := by decide
  have hdescent : baseEnd_3700476 < baseStart_3700476 := by decide
  rcases family_descends (prefixWord ++ tailWord_3700476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3700516 : List Nat := [2, 3, 1, 3, 2, 1, 2, 2, 3, 2, 2]
def baseStart_3700516 : Nat := 118140960795 + 3700516 * 2 ^ 59
def prefixEnd_3700516 : Nat := 4983230072969 + 3 ^ 40 * 3700516 * 2
def baseEnd_3700516 : Nat := 1900143377653348947831643

theorem tailTrace_3700516 : CollatzResearch.WordTrace tailWord_3700516 prefixEnd_3700516 1900143377653348947831643 := by
  unfold tailWord_3700516
  simp only [CollatzResearch.WordTrace]
  refine ⟨67484453330835002330996701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89979271107780003107995601 67484453330835002330996701)
  ·
    refine ⟨25306669999063125874123763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67484453330835002330996701 25306669999063125874123763)
    ·
      refine ⟨37960004998594688811185645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25306669999063125874123763 37960004998594688811185645)
      ·
        refine ⟨14235001874473008304194617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37960004998594688811185645 14235001874473008304194617)
        ·
          refine ⟨10676251405854756228145963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14235001874473008304194617 10676251405854756228145963)
          ·
            refine ⟨16014377108782134342218945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10676251405854756228145963 16014377108782134342218945)
            ·
              refine ⟨12010782831586600756664209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16014377108782134342218945 12010782831586600756664209)
              ·
                refine ⟨9008087123689950567498157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12010782831586600756664209 9008087123689950567498157)
                ·
                  refine ⟨3378032671383731462811809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9008087123689950567498157 3378032671383731462811809)
                  ·
                    refine ⟨2533524503537798597108857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3378032671383731462811809 2533524503537798597108857)
                    ·
                      refine ⟨1900143377653348947831643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2533524503537798597108857 1900143377653348947831643)
                      ·
                        rfl

theorem cell23_3700516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 2, 2, 3, 2, 2].length) (baseStart_3700516 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3700516 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3700516 prefixEnd_3700516 := by exact prefixLift 3700516
  have htrace : WordTrace (prefixWord ++ tailWord_3700516) baseStart_3700516 baseEnd_3700516 := by
    simpa [prefixWord, tailWord_3700516, baseEnd_3700516] using wordTrace_append hprefix tailTrace_3700516
  have hstable : (prefixWord ++ tailWord_3700516).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3700516).length < 2 ^ (prefixWord ++ tailWord_3700516).sum := by decide
  have hdescent : baseEnd_3700516 < baseStart_3700516 := by decide
  rcases family_descends (prefixWord ++ tailWord_3700516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3700549 : List Nat := [1, 3, 1, 1, 1, 2, 4, 4, 2, 1, 3]
def baseStart_3700549 : Nat := 118140960795 + 3700549 * 2 ^ 59
def prefixEnd_3700549 : Nat := 4983230072969 + 3 ^ 40 * 3700549 * 2
def baseEnd_3700549 : Nat := 1900160322514947318718991

theorem tailTrace_3700549 : CollatzResearch.WordTrace tailWord_3700549 prefixEnd_3700549 1900160322514947318718991 := by
  unfold tailWord_3700549
  simp only [CollatzResearch.WordTrace]
  refine ⟨134970110270550451297944701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89980073513700300865296467 134970110270550451297944701)
  ·
    refine ⟨50613791351456419236729263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 134970110270550451297944701 50613791351456419236729263)
    ·
      refine ⟨75920687027184628855093895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50613791351456419236729263 75920687027184628855093895)
      ·
        refine ⟨113881030540776943282640843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75920687027184628855093895 113881030540776943282640843)
        ·
          refine ⟨170821545811165414923961265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113881030540776943282640843 170821545811165414923961265)
          ·
            refine ⟨128116159358374061192970949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 170821545811165414923961265 128116159358374061192970949)
            ·
              refine ⟨24021779879695136473682053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 128116159358374061192970949 24021779879695136473682053)
              ·
                refine ⟨4504083727442838088815385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24021779879695136473682053 4504083727442838088815385)
                ·
                  refine ⟨3378062795582128566611539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4504083727442838088815385 3378062795582128566611539)
                  ·
                    refine ⟨5067094193373192849917309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3378062795582128566611539 5067094193373192849917309)
                    ·
                      refine ⟨1900160322514947318718991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5067094193373192849917309 1900160322514947318718991)
                      ·
                        rfl

theorem cell23_3700549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 4, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 4, 4, 2, 1, 3].length) (baseStart_3700549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3700549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3700549 prefixEnd_3700549 := by exact prefixLift 3700549
  have htrace : WordTrace (prefixWord ++ tailWord_3700549) baseStart_3700549 baseEnd_3700549 := by
    simpa [prefixWord, tailWord_3700549, baseEnd_3700549] using wordTrace_append hprefix tailTrace_3700549
  have hstable : (prefixWord ++ tailWord_3700549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3700549).length < 2 ^ (prefixWord ++ tailWord_3700549).sum := by decide
  have hdescent : baseEnd_3700549 < baseStart_3700549 := by decide
  rcases family_descends (prefixWord ++ tailWord_3700549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3700550 : List Nat := [6, 1, 1, 2, 1, 1, 3, 1, 3, 2, 2]
def baseStart_3700550 : Nat := 118140960795 + 3700550 * 2 ^ 59
def prefixEnd_3700550 : Nat := 4983230072969 + 3 ^ 40 * 3700550 * 2
def baseEnd_3700550 : Nat := 1900160835995601814806487

theorem tailTrace_3700550 : CollatzResearch.WordTrace tailWord_3700550 prefixEnd_3700550 1900160835995601814806487 := by
  unfold tailWord_3700550
  simp only [CollatzResearch.WordTrace]
  refine ⟨4217817085735838389647847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 89980097829031218979154069 4217817085735838389647847)
  ·
    refine ⟨6326725628603757584471771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4217817085735838389647847 6326725628603757584471771)
    ·
      refine ⟨9490088442905636376707657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6326725628603757584471771 9490088442905636376707657)
      ·
        refine ⟨7117566332179227282530743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9490088442905636376707657 7117566332179227282530743)
        ·
          refine ⟨10676349498268840923796115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7117566332179227282530743 10676349498268840923796115)
          ·
            refine ⟨16014524247403261385694173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10676349498268840923796115 16014524247403261385694173)
            ·
              refine ⟨6005446592776223019635315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16014524247403261385694173 6005446592776223019635315)
              ·
                refine ⟨9008169889164334529452973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6005446592776223019635315 9008169889164334529452973)
                ·
                  refine ⟨3378063708436625448544865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9008169889164334529452973 3378063708436625448544865)
                  ·
                    refine ⟨2533547781327469086408649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3378063708436625448544865 2533547781327469086408649)
                    ·
                      refine ⟨1900160835995601814806487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2533547781327469086408649 1900160835995601814806487)
                      ·
                        rfl

theorem cell23_3700550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 3, 1, 3, 2, 2].length) (baseStart_3700550 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3700550 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3700550 prefixEnd_3700550 := by exact prefixLift 3700550
  have htrace : WordTrace (prefixWord ++ tailWord_3700550) baseStart_3700550 baseEnd_3700550 := by
    simpa [prefixWord, tailWord_3700550, baseEnd_3700550] using wordTrace_append hprefix tailTrace_3700550
  have hstable : (prefixWord ++ tailWord_3700550).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3700550).length < 2 ^ (prefixWord ++ tailWord_3700550).sum := by decide
  have hdescent : baseEnd_3700550 < baseStart_3700550 := by decide
  rcases family_descends (prefixWord ++ tailWord_3700550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3700576 : List Nat := [2, 1, 1, 3, 3, 2, 3, 2, 1, 3, 2]
def baseStart_3700576 : Nat := 118140960795 + 3700576 * 2 ^ 59
def prefixEnd_3700576 : Nat := 4983230072969 + 3 ^ 40 * 3700576 * 2
def baseEnd_3700576 : Nat := 1900174186492618713081367

theorem tailTrace_3700576 : CollatzResearch.WordTrace tailWord_3700576 prefixEnd_3700576 1900174186492618713081367 := by
  unfold tailWord_3700576
  simp only [CollatzResearch.WordTrace]
  refine ⟨67485547520726317454588791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89980730027635089939451721 67485547520726317454588791)
  ·
    refine ⟨101228321281089476181883187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67485547520726317454588791 101228321281089476181883187)
    ·
      refine ⟨151842481921634214272824781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101228321281089476181883187 151842481921634214272824781)
      ·
        refine ⟨56940930720612830352309293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 151842481921634214272824781 56940930720612830352309293)
        ·
          refine ⟨21352849020229811382115985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56940930720612830352309293 21352849020229811382115985)
          ·
            refine ⟨16014636765172358536586989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21352849020229811382115985 16014636765172358536586989)
            ·
              refine ⟨6005488786939634451220121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16014636765172358536586989 6005488786939634451220121)
              ·
                refine ⟨4504116590204725838415091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6005488786939634451220121 4504116590204725838415091)
                ·
                  refine ⟨6756174885307088757622637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4504116590204725838415091 6756174885307088757622637)
                  ·
                    refine ⟨2533565581990158284108489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6756174885307088757622637 2533565581990158284108489)
                    ·
                      refine ⟨1900174186492618713081367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2533565581990158284108489 1900174186492618713081367)
                      ·
                        rfl

theorem cell23_3700576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 3, 2, 1, 3, 2].length) (baseStart_3700576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3700576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3700576 prefixEnd_3700576 := by exact prefixLift 3700576
  have htrace : WordTrace (prefixWord ++ tailWord_3700576) baseStart_3700576 baseEnd_3700576 := by
    simpa [prefixWord, tailWord_3700576, baseEnd_3700576] using wordTrace_append hprefix tailTrace_3700576
  have hstable : (prefixWord ++ tailWord_3700576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3700576).length < 2 ^ (prefixWord ++ tailWord_3700576).sum := by decide
  have hdescent : baseEnd_3700576 < baseStart_3700576 := by decide
  rcases family_descends (prefixWord ++ tailWord_3700576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3700589 : List Nat := [1, 5, 1, 1, 1, 1, 3, 1, 3, 4, 2]
def baseStart_3700589 : Nat := 118140960795 + 3700589 * 2 ^ 59
def prefixEnd_3700589 : Nat := 4983230072969 + 3 ^ 40 * 3700589 * 2
def baseEnd_3700589 : Nat := 1900180861741127162218807

theorem tailTrace_3700589 : CollatzResearch.WordTrace tailWord_3700589 prefixEnd_3700589 1900180861741127162218807 := by
  unfold tailWord_3700589
  simp only [CollatzResearch.WordTrace]
  refine ⟨134971569190405538129400821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89981046126937025419600547 134971569190405538129400821)
  ·
    refine ⟨12653584611600519199631327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 134971569190405538129400821 12653584611600519199631327)
    ·
      refine ⟨18980376917400778799446991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12653584611600519199631327 18980376917400778799446991)
      ·
        refine ⟨28470565376101168199170487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18980376917400778799446991 28470565376101168199170487)
        ·
          refine ⟨42705848064151752298755731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28470565376101168199170487 42705848064151752298755731)
          ·
            refine ⟨64058772096227628448133597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42705848064151752298755731 64058772096227628448133597)
            ·
              refine ⟨24022039536085360668050099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 64058772096227628448133597 24022039536085360668050099)
              ·
                refine ⟨36033059304128041002075149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24022039536085360668050099 36033059304128041002075149)
                ·
                  refine ⟨13512397239048015375778181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36033059304128041002075149 13512397239048015375778181)
                  ·
                    refine ⟨2533574482321502882958409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13512397239048015375778181 2533574482321502882958409)
                    ·
                      refine ⟨1900180861741127162218807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2533574482321502882958409 1900180861741127162218807)
                      ·
                        rfl

theorem cell23_3700589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 3, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 3, 1, 3, 4, 2].length) (baseStart_3700589 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3700589 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3700589 prefixEnd_3700589 := by exact prefixLift 3700589
  have htrace : WordTrace (prefixWord ++ tailWord_3700589) baseStart_3700589 baseEnd_3700589 := by
    simpa [prefixWord, tailWord_3700589, baseEnd_3700589] using wordTrace_append hprefix tailTrace_3700589
  have hstable : (prefixWord ++ tailWord_3700589).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3700589).length < 2 ^ (prefixWord ++ tailWord_3700589).sum := by decide
  have hdescent : baseEnd_3700589 < baseStart_3700589 := by decide
  rcases family_descends (prefixWord ++ tailWord_3700589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3700739 : List Nat := [1, 1, 1, 3, 2, 1, 1, 3, 3, 5, 2]
def baseStart_3700739 : Nat := 118140960795 + 3700739 * 2 ^ 59
def prefixEnd_3700739 : Nat := 4983230072969 + 3 ^ 40 * 3700739 * 2
def baseEnd_3700739 : Nat := 1900257883839301575343117

theorem tailTrace_3700739 : CollatzResearch.WordTrace tailWord_3700739 prefixEnd_3700739 1900257883839301575343117 := by
  unfold tailWord_3700739
  simp only [CollatzResearch.WordTrace]
  refine ⟨134977040139862113747361271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89984693426574742498240847 134977040139862113747361271)
  ·
    refine ⟨202465560209793170621041907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134977040139862113747361271 202465560209793170621041907)
    ·
      refine ⟨303698340314689755931562861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 202465560209793170621041907 303698340314689755931562861)
      ·
        refine ⟨113886877618008658474336073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 303698340314689755931562861 113886877618008658474336073)
        ·
          refine ⟨85415158213506493855752055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 113886877618008658474336073 85415158213506493855752055)
          ·
            refine ⟨128122737320259740783628083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85415158213506493855752055 128122737320259740783628083)
            ·
              refine ⟨192184105980389611175442125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 128122737320259740783628083 192184105980389611175442125)
              ·
                refine ⟨72069039742646104190790797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 192184105980389611175442125 72069039742646104190790797)
                ·
                  refine ⟨27025889903492289071546549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 72069039742646104190790797 27025889903492289071546549)
                  ·
                    refine ⟨2533677178452402100457489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 27025889903492289071546549 2533677178452402100457489)
                    ·
                      refine ⟨1900257883839301575343117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2533677178452402100457489 1900257883839301575343117)
                      ·
                        rfl

theorem cell23_3700739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 3, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 3, 3, 5, 2].length) (baseStart_3700739 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3700739 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3700739 prefixEnd_3700739 := by exact prefixLift 3700739
  have htrace : WordTrace (prefixWord ++ tailWord_3700739) baseStart_3700739 baseEnd_3700739 := by
    simpa [prefixWord, tailWord_3700739, baseEnd_3700739] using wordTrace_append hprefix tailTrace_3700739
  have hstable : (prefixWord ++ tailWord_3700739).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3700739).length < 2 ^ (prefixWord ++ tailWord_3700739).sum := by decide
  have hdescent : baseEnd_3700739 < baseStart_3700739 := by decide
  rcases family_descends (prefixWord ++ tailWord_3700739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3700752 : List Nat := [2, 1, 1, 1, 1, 1, 1, 4, 2, 5, 4]
def baseStart_3700752 : Nat := 118140960795 + 3700752 * 2 ^ 59
def prefixEnd_3700752 : Nat := 4983230072969 + 3 ^ 40 * 3700752 * 2
def baseEnd_3700752 : Nat := 1900264559087810024480557

theorem tailTrace_3700752 : CollatzResearch.WordTrace tailWord_3700752 prefixEnd_3700752 1900264559087810024480557 := by
  unfold tailWord_3700752
  simp only [CollatzResearch.WordTrace]
  refine ⟨67488757144407508483792255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89985009525876677978389673 67488757144407508483792255)
  ·
    refine ⟨101233135716611262725688383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67488757144407508483792255 101233135716611262725688383)
    ·
      refine ⟨151849703574916894088532575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101233135716611262725688383 151849703574916894088532575)
      ·
        refine ⟨227774555362375341132798863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151849703574916894088532575 227774555362375341132798863)
        ·
          refine ⟨341661833043563011699198295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 227774555362375341132798863 341661833043563011699198295)
          ·
            refine ⟨512492749565344517548797443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 341661833043563011699198295 512492749565344517548797443)
            ·
              refine ⟨768739124348016776323196165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 512492749565344517548797443 768739124348016776323196165)
              ·
                refine ⟨144138585815253145560599281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 768739124348016776323196165 144138585815253145560599281)
                ·
                  refine ⟨108103939361439859170449461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 144138585815253145560599281 108103939361439859170449461)
                  ·
                    refine ⟨10134744315134986797229637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 108103939361439859170449461 10134744315134986797229637)
                    ·
                      refine ⟨1900264559087810024480557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10134744315134986797229637 1900264559087810024480557)
                      ·
                        rfl

theorem cell23_3700752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 4, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 4, 2, 5, 4].length) (baseStart_3700752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3700752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3700752 prefixEnd_3700752 := by exact prefixLift 3700752
  have htrace : WordTrace (prefixWord ++ tailWord_3700752) baseStart_3700752 baseEnd_3700752 := by
    simpa [prefixWord, tailWord_3700752, baseEnd_3700752] using wordTrace_append hprefix tailTrace_3700752
  have hstable : (prefixWord ++ tailWord_3700752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3700752).length < 2 ^ (prefixWord ++ tailWord_3700752).sum := by decide
  have hdescent : baseEnd_3700752 < baseStart_3700752 := by decide
  rcases family_descends (prefixWord ++ tailWord_3700752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3700789 : List Nat := [1, 3, 3, 1, 1, 1, 2, 4, 1, 1, 5]
def baseStart_3700789 : Nat := 118140960795 + 3700789 * 2 ^ 59
def prefixEnd_3700789 : Nat := 4983230072969 + 3 ^ 40 * 3700789 * 2
def baseEnd_3700789 : Nat := 1900283557872026379717887

theorem tailTrace_3700789 : CollatzResearch.WordTrace tailWord_3700789 prefixEnd_3700789 1900283557872026379717887 := by
  unfold tailWord_3700789
  simp only [CollatzResearch.WordTrace]
  refine ⟨134978863789680972286681421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89985909193120648191120947 134978863789680972286681421)
  ·
    refine ⟨50617073921130364607505533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 134978863789680972286681421 50617073921130364607505533)
    ·
      refine ⟨18981402720423886727814575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50617073921130364607505533 18981402720423886727814575)
      ·
        refine ⟨28472104080635830091721863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18981402720423886727814575 28472104080635830091721863)
        ·
          refine ⟨42708156120953745137582795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28472104080635830091721863 42708156120953745137582795)
          ·
            refine ⟨64062234181430617706374193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42708156120953745137582795 64062234181430617706374193)
            ·
              refine ⟨48046675636072963279780645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64062234181430617706374193 48046675636072963279780645)
              ·
                refine ⟨9008751681763680614958871, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 48046675636072963279780645 9008751681763680614958871)
                ·
                  refine ⟨13513127522645520922438307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9008751681763680614958871 13513127522645520922438307)
                  ·
                    refine ⟨20269691283968281383657461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13513127522645520922438307 20269691283968281383657461)
                    ·
                      refine ⟨1900283557872026379717887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20269691283968281383657461 1900283557872026379717887)
                      ·
                        rfl

theorem cell23_3700789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 2, 4, 1, 1, 5].length) (baseStart_3700789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3700789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3700789 prefixEnd_3700789 := by exact prefixLift 3700789
  have htrace : WordTrace (prefixWord ++ tailWord_3700789) baseStart_3700789 baseEnd_3700789 := by
    simpa [prefixWord, tailWord_3700789, baseEnd_3700789] using wordTrace_append hprefix tailTrace_3700789
  have hstable : (prefixWord ++ tailWord_3700789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3700789).length < 2 ^ (prefixWord ++ tailWord_3700789).sum := by decide
  have hdescent : baseEnd_3700789 < baseStart_3700789 := by decide
  rcases family_descends (prefixWord ++ tailWord_3700789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3700796 : List Nat := [2, 2, 2, 2, 2, 1, 1, 5, 2, 4]
def baseStart_3700796 : Nat := 118140960795 + 3700796 * 2 ^ 59
def prefixEnd_3700796 : Nat := 4983230072969 + 3 ^ 40 * 3700796 * 2
def baseEnd_3700796 : Nat := 633429050745535950776785

theorem tailTrace_3700796 : CollatzResearch.WordTrace tailWord_3700796 prefixEnd_3700796 633429050745535950776785 := by
  unfold tailWord_3700796
  simp only [CollatzResearch.WordTrace]
  refine ⟨67489559550327806241093121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89986079400437074988124161 67489559550327806241093121)
  ·
    refine ⟨50617169662745854680819841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67489559550327806241093121 50617169662745854680819841)
    ·
      refine ⟨37962877247059391010614881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50617169662745854680819841 37962877247059391010614881)
      ·
        refine ⟨28472157935294543257961161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37962877247059391010614881 28472157935294543257961161)
        ·
          refine ⟨21354118451470907443470871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28472157935294543257961161 21354118451470907443470871)
          ·
            refine ⟨32031177677206361165206307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21354118451470907443470871 32031177677206361165206307)
            ·
              refine ⟨48046766515809541747809461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32031177677206361165206307 48046766515809541747809461)
              ·
                refine ⟨4504384360857144538857137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 48046766515809541747809461 4504384360857144538857137)
                ·
                  refine ⟨3378288270642858404142853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4504384360857144538857137 3378288270642858404142853)
                  ·
                    refine ⟨633429050745535950776785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3378288270642858404142853 633429050745535950776785)
                    ·
                      rfl

theorem cell23_3700796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 1, 5, 2, 4].length) (baseStart_3700796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3700796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3700796 prefixEnd_3700796 := by exact prefixLift 3700796
  have htrace : WordTrace (prefixWord ++ tailWord_3700796) baseStart_3700796 baseEnd_3700796 := by
    simpa [prefixWord, tailWord_3700796, baseEnd_3700796] using wordTrace_append hprefix tailTrace_3700796
  have hstable : (prefixWord ++ tailWord_3700796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3700796).length < 2 ^ (prefixWord ++ tailWord_3700796).sum := by decide
  have hdescent : baseEnd_3700796 < baseStart_3700796 := by decide
  rcases family_descends (prefixWord ++ tailWord_3700796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3700799 : List Nat := [1, 1, 2, 2, 3, 1, 3, 3, 1, 2, 4]
def baseStart_3700799 : Nat := 118140960795 + 3700799 * 2 ^ 59
def prefixEnd_3700799 : Nat := 4983230072969 + 3 ^ 40 * 3700799 * 2
def baseEnd_3700799 : Nat := 1900288692678571340592841

theorem tailTrace_3700799 : CollatzResearch.WordTrace tailWord_3700799 prefixEnd_3700799 1900288692678571340592841 := by
  unfold tailWord_3700799
  simp only [CollatzResearch.WordTrace]
  refine ⟨134979228519644743994545451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89986152346429829329696967 134979228519644743994545451)
  ·
    refine ⟨202468842779467115991818177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134979228519644743994545451 202468842779467115991818177)
    ·
      refine ⟨151851632084600336993863633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 202468842779467115991818177 151851632084600336993863633)
      ·
        refine ⟨113888724063450252745397725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 151851632084600336993863633 113888724063450252745397725)
        ·
          refine ⟨42708271523793844779524147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 113888724063450252745397725 42708271523793844779524147)
          ·
            refine ⟨64062407285690767169286221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42708271523793844779524147 64062407285690767169286221)
            ·
              refine ⟨24023402732134037688482333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 64062407285690767169286221 24023402732134037688482333)
              ·
                refine ⟨9008776024550264133180875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24023402732134037688482333 9008776024550264133180875)
                ·
                  refine ⟨13513164036825396199771313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9008776024550264133180875 13513164036825396199771313)
                  ·
                    refine ⟨10134873027619047149828485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13513164036825396199771313 10134873027619047149828485)
                    ·
                      refine ⟨1900288692678571340592841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10134873027619047149828485 1900288692678571340592841)
                      ·
                        rfl

theorem cell23_3700799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 3, 3, 1, 2, 4].length) (baseStart_3700799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3700799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3700799 prefixEnd_3700799 := by exact prefixLift 3700799
  have htrace : WordTrace (prefixWord ++ tailWord_3700799) baseStart_3700799 baseEnd_3700799 := by
    simpa [prefixWord, tailWord_3700799, baseEnd_3700799] using wordTrace_append hprefix tailTrace_3700799
  have hstable : (prefixWord ++ tailWord_3700799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3700799).length < 2 ^ (prefixWord ++ tailWord_3700799).sum := by decide
  have hdescent : baseEnd_3700799 < baseStart_3700799 := by decide
  rcases family_descends (prefixWord ++ tailWord_3700799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3700809 : List Nat := [1, 2, 1, 1, 2, 2, 7, 7]
def baseStart_3700809 : Nat := 118140960795 + 3700809 * 2 ^ 59
def prefixEnd_3700809 : Nat := 4983230072969 + 3 ^ 40 * 3700809 * 2
def baseEnd_3700809 : Nat := 70381252869819122276585

theorem tailTrace_3700809 : CollatzResearch.WordTrace tailWord_3700809 prefixEnd_3700809 70381252869819122276585 := by
  unfold tailWord_3700809
  simp only [CollatzResearch.WordTrace]
  refine ⟨134979593249608515702409481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89986395499739010468272987 134979593249608515702409481)
  ·
    refine ⟨101234694937206386776807111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134979593249608515702409481 101234694937206386776807111)
    ·
      refine ⟨151852042405809580165210667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101234694937206386776807111 151852042405809580165210667)
      ·
        refine ⟨227778063608714370247816001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151852042405809580165210667 227778063608714370247816001)
        ·
          refine ⟨170833547706535777685862001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 227778063608714370247816001 170833547706535777685862001)
          ·
            refine ⟨128125160779901833264396501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 170833547706535777685862001 128125160779901833264396501)
            ·
              refine ⟨3002933455778949217134293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 128125160779901833264396501 3002933455778949217134293)
              ·
                refine ⟨70381252869819122276585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3002933455778949217134293 70381252869819122276585)
                ·
                  rfl

theorem cell23_3700809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 7, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 7, 7].length) (baseStart_3700809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3700809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3700809 prefixEnd_3700809 := by exact prefixLift 3700809
  have htrace : WordTrace (prefixWord ++ tailWord_3700809) baseStart_3700809 baseEnd_3700809 := by
    simpa [prefixWord, tailWord_3700809, baseEnd_3700809] using wordTrace_append hprefix tailTrace_3700809
  have hstable : (prefixWord ++ tailWord_3700809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3700809).length < 2 ^ (prefixWord ++ tailWord_3700809).sum := by decide
  have hdescent : baseEnd_3700809 < baseStart_3700809 := by decide
  rcases family_descends (prefixWord ++ tailWord_3700809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3700823 : List Nat := [1, 1, 3, 2, 2, 1, 6, 1, 1, 2, 3]
def baseStart_3700823 : Nat := 118140960795 + 3700823 * 2 ^ 59
def prefixEnd_3700823 : Nat := 4983230072969 + 3 ^ 40 * 3700823 * 2
def baseEnd_3700823 : Nat := 1900301016214279246692731

theorem tailTrace_3700823 : CollatzResearch.WordTrace tailWord_3700823 prefixEnd_3700823 1900301016214279246692731 := by
  unfold tailWord_3700823
  simp only [CollatzResearch.WordTrace]
  refine ⟨134980103871557796093419123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89986735914371864062279415 134980103871557796093419123)
  ·
    refine ⟨202470155807336694140128685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134980103871557796093419123 202470155807336694140128685)
    ·
      refine ⟨75926308427751260302548257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 202470155807336694140128685 75926308427751260302548257)
      ·
        refine ⟨56944731320813445226911193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75926308427751260302548257 56944731320813445226911193)
        ·
          refine ⟨42708548490610083920183395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56944731320813445226911193 42708548490610083920183395)
          ·
            refine ⟨64062822735915125880275093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42708548490610083920183395 64062822735915125880275093)
            ·
              refine ⟨3002944815746021525637895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 64062822735915125880275093 3002944815746021525637895)
              ·
                refine ⟨4504417223619032288456843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3002944815746021525637895 4504417223619032288456843)
                ·
                  refine ⟨6756625835428548432685265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4504417223619032288456843 6756625835428548432685265)
                  ·
                    refine ⟨5067469376571411324513949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6756625835428548432685265 5067469376571411324513949)
                    ·
                      refine ⟨1900301016214279246692731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5067469376571411324513949 1900301016214279246692731)
                      ·
                        rfl

theorem cell23_3700823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 6, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 6, 1, 1, 2, 3].length) (baseStart_3700823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3700823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3700823 prefixEnd_3700823 := by exact prefixLift 3700823
  have htrace : WordTrace (prefixWord ++ tailWord_3700823) baseStart_3700823 baseEnd_3700823 := by
    simpa [prefixWord, tailWord_3700823, baseEnd_3700823] using wordTrace_append hprefix tailTrace_3700823
  have hstable : (prefixWord ++ tailWord_3700823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3700823).length < 2 ^ (prefixWord ++ tailWord_3700823).sum := by decide
  have hdescent : baseEnd_3700823 < baseStart_3700823 := by decide
  rcases family_descends (prefixWord ++ tailWord_3700823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3700889 : List Nat := [1, 2, 1, 2, 1, 2, 1, 3, 4, 2, 4]
def baseStart_3700889 : Nat := 118140960795 + 3700889 * 2 ^ 59
def prefixEnd_3700889 : Nat := 4983230072969 + 3 ^ 40 * 3700889 * 2
def baseEnd_3700889 : Nat := 1900334905937475988467427

theorem tailTrace_3700889 : CollatzResearch.WordTrace tailWord_3700889 prefixEnd_3700889 1900334905937475988467427 := by
  unfold tailWord_3700889
  simp only [CollatzResearch.WordTrace]
  refine ⟨134982511089318689365321721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89988340726212459576881147 134982511089318689365321721)
  ·
    refine ⟨101236883316989017023991291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134982511089318689365321721 101236883316989017023991291)
    ·
      refine ⟨151855324975483525535986937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101236883316989017023991291 151855324975483525535986937)
      ·
        refine ⟨113891493731612644151990203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 151855324975483525535986937 113891493731612644151990203)
        ·
          refine ⟨170837240597418966227985305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113891493731612644151990203 170837240597418966227985305)
          ·
            refine ⟨128127930448064224670988979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 170837240597418966227985305 128127930448064224670988979)
            ·
              refine ⟨192191895672096337006483469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 128127930448064224670988979 192191895672096337006483469)
              ·
                refine ⟨72071960877036126377431301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 192191895672096337006483469 72071960877036126377431301)
                ·
                  refine ⟨13513492664444273695768369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 72071960877036126377431301 13513492664444273695768369)
                  ·
                    refine ⟨10135119498333205271826277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13513492664444273695768369 10135119498333205271826277)
                    ·
                      refine ⟨1900334905937475988467427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10135119498333205271826277 1900334905937475988467427)
                      ·
                        rfl

theorem cell23_3700889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 3, 4, 2, 4].length) (baseStart_3700889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3700889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3700889 prefixEnd_3700889 := by exact prefixLift 3700889
  have htrace : WordTrace (prefixWord ++ tailWord_3700889) baseStart_3700889 baseEnd_3700889 := by
    simpa [prefixWord, tailWord_3700889, baseEnd_3700889] using wordTrace_append hprefix tailTrace_3700889
  have hstable : (prefixWord ++ tailWord_3700889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3700889).length < 2 ^ (prefixWord ++ tailWord_3700889).sum := by decide
  have hdescent : baseEnd_3700889 < baseStart_3700889 := by decide
  rcases family_descends (prefixWord ++ tailWord_3700889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3700930 : List Nat := [3, 5, 1, 1, 1, 1, 2, 1, 2, 1, 5]
def baseStart_3700930 : Nat := 118140960795 + 3700930 * 2 ^ 59
def prefixEnd_3700930 : Nat := 4983230072969 + 3 ^ 40 * 3700930 * 2
def baseEnd_3700930 : Nat := 1900355958644310328054739

theorem tailTrace_3700930 : CollatzResearch.WordTrace tailWord_3700930 prefixEnd_3700930 1900355958644310328054739 := by
  unfold tailWord_3700930
  simp only [CollatzResearch.WordTrace]
  refine ⟨33746001620542538341891061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89989337654780102245042829 33746001620542538341891061)
  ·
    refine ⟨3163687651925862969552287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 33746001620542538341891061 3163687651925862969552287)
    ·
      refine ⟨4745531477888794454328431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3163687651925862969552287 4745531477888794454328431)
      ·
        refine ⟨7118297216833191681492647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4745531477888794454328431 7118297216833191681492647)
        ·
          refine ⟨10677445825249787522238971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7118297216833191681492647 10677445825249787522238971)
          ·
            refine ⟨16016168737874681283358457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10677445825249787522238971 16016168737874681283358457)
            ·
              refine ⟨12012126553406010962518843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16016168737874681283358457 12012126553406010962518843)
              ·
                refine ⟨18018189830109016443778265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12012126553406010962518843 18018189830109016443778265)
                ·
                  refine ⟨13513642372581762332833699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18018189830109016443778265 13513642372581762332833699)
                  ·
                    refine ⟨20270463558872643499250549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13513642372581762332833699 20270463558872643499250549)
                    ·
                      refine ⟨1900355958644310328054739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20270463558872643499250549 1900355958644310328054739)
                      ·
                        rfl

theorem cell23_3700930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 2, 1, 2, 1, 5].length) (baseStart_3700930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3700930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3700930 prefixEnd_3700930 := by exact prefixLift 3700930
  have htrace : WordTrace (prefixWord ++ tailWord_3700930) baseStart_3700930 baseEnd_3700930 := by
    simpa [prefixWord, tailWord_3700930, baseEnd_3700930] using wordTrace_append hprefix tailTrace_3700930
  have hstable : (prefixWord ++ tailWord_3700930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3700930).length < 2 ^ (prefixWord ++ tailWord_3700930).sum := by decide
  have hdescent : baseEnd_3700930 < baseStart_3700930 := by decide
  rcases family_descends (prefixWord ++ tailWord_3700930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3700939 : List Nat := [1, 1, 1, 1, 3, 2, 3, 1, 3, 2, 5]
def baseStart_3700939 : Nat := 118140960795 + 3700939 * 2 ^ 59
def prefixEnd_3700939 : Nat := 4983230072969 + 3 ^ 40 * 3700939 * 2
def baseEnd_3700939 : Nat := 1900360579970200792842197

theorem tailTrace_3700939 : CollatzResearch.WordTrace tailWord_3700939 prefixEnd_3700939 1900360579970200792842197 := by
  unfold tailWord_3700939
  simp only [CollatzResearch.WordTrace]
  refine ⟨134984334739137547904641871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89989556492758365269761247 134984334739137547904641871)
  ·
    refine ⟨202476502108706321856962807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134984334739137547904641871 202476502108706321856962807)
    ·
      refine ⟨303714753163059482785444211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 202476502108706321856962807 303714753163059482785444211)
      ·
        refine ⟨455572129744589224178166317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 303714753163059482785444211 455572129744589224178166317)
        ·
          refine ⟨170839548654220959066812369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 455572129744589224178166317 170839548654220959066812369)
          ·
            refine ⟨128129661490665719300109277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 170839548654220959066812369 128129661490665719300109277)
            ·
              refine ⟨48048623058999644737540979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 128129661490665719300109277 48048623058999644737540979)
              ·
                refine ⟨72072934588499467106311469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48048623058999644737540979 72072934588499467106311469)
                ·
                  refine ⟨27027350470687300164866801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 72072934588499467106311469 27027350470687300164866801)
                  ·
                    refine ⟨20270512853015475123650101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27027350470687300164866801 20270512853015475123650101)
                    ·
                      refine ⟨1900360579970200792842197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20270512853015475123650101 1900360579970200792842197)
                      ·
                        rfl

theorem cell23_3700939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 3, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 3, 1, 3, 2, 5].length) (baseStart_3700939 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3700939 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3700939 prefixEnd_3700939 := by exact prefixLift 3700939
  have htrace : WordTrace (prefixWord ++ tailWord_3700939) baseStart_3700939 baseEnd_3700939 := by
    simpa [prefixWord, tailWord_3700939, baseEnd_3700939] using wordTrace_append hprefix tailTrace_3700939
  have hstable : (prefixWord ++ tailWord_3700939).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3700939).length < 2 ^ (prefixWord ++ tailWord_3700939).sum := by decide
  have hdescent : baseEnd_3700939 < baseStart_3700939 := by decide
  rcases family_descends (prefixWord ++ tailWord_3700939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3700959 : List Nat := [1, 1, 2, 3, 2, 1, 1, 2, 2, 8]
def baseStart_3700959 : Nat := 118140960795 + 3700959 * 2 ^ 59
def prefixEnd_3700959 : Nat := 4983230072969 + 3 ^ 40 * 3700959 * 2
def baseEnd_3700959 : Nat := 633456949861096904864035

theorem tailTrace_3700959 : CollatzResearch.WordTrace tailWord_3700959 prefixEnd_3700959 633456949861096904864035 := by
  unfold tailWord_3700959
  simp only [CollatzResearch.WordTrace]
  refine ⟨134985064199065091320369931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89990042799376727546913287 134985064199065091320369931)
  ·
    refine ⟨202477596298597636980554897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134985064199065091320369931 202477596298597636980554897)
    ·
      refine ⟨151858197223948227735416173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 202477596298597636980554897 151858197223948227735416173)
      ·
        refine ⟨56946823958980585400781065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 151858197223948227735416173 56946823958980585400781065)
        ·
          refine ⟨42710117969235439050585799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56946823958980585400781065 42710117969235439050585799)
          ·
            refine ⟨64065176953853158575878699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42710117969235439050585799 64065176953853158575878699)
            ·
              refine ⟨96097765430779737863818049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64065176953853158575878699 96097765430779737863818049)
              ·
                refine ⟨72073324073084803397863537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 96097765430779737863818049 72073324073084803397863537)
                ·
                  refine ⟨54054993054813602548397653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 72073324073084803397863537 54054993054813602548397653)
                  ·
                    refine ⟨633456949861096904864035, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 54054993054813602548397653 633456949861096904864035)
                    ·
                      rfl

theorem cell23_3700959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 2, 2, 8].length) (baseStart_3700959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3700959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3700959 prefixEnd_3700959 := by exact prefixLift 3700959
  have htrace : WordTrace (prefixWord ++ tailWord_3700959) baseStart_3700959 baseEnd_3700959 := by
    simpa [prefixWord, tailWord_3700959, baseEnd_3700959] using wordTrace_append hprefix tailTrace_3700959
  have hstable : (prefixWord ++ tailWord_3700959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3700959).length < 2 ^ (prefixWord ++ tailWord_3700959).sum := by decide
  have hdescent : baseEnd_3700959 < baseStart_3700959 := by decide
  rcases family_descends (prefixWord ++ tailWord_3700959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3700969 : List Nat := [1, 2, 1, 1, 1, 2, 2, 2, 1, 5, 5]
def baseStart_3700969 : Nat := 118140960795 + 3700969 * 2 ^ 59
def prefixEnd_3700969 : Nat := 4983230072969 + 3 ^ 40 * 3700969 * 2
def baseEnd_3700969 : Nat := 1900375984389835675467059

theorem tailTrace_3700969 : CollatzResearch.WordTrace tailWord_3700969 prefixEnd_3700969 1900375984389835675467059 := by
  unfold tailWord_3700969
  simp only [CollatzResearch.WordTrace]
  refine ⟨134985428929028863028233961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89990285952685908685489307 134985428929028863028233961)
  ·
    refine ⟨101239071696771647271175471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134985428929028863028233961 101239071696771647271175471)
    ·
      refine ⟨151858607545157470906763207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101239071696771647271175471 151858607545157470906763207)
      ·
        refine ⟨227787911317736206360144811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151858607545157470906763207 227787911317736206360144811)
        ·
          refine ⟨341681866976604309540217217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 227787911317736206360144811 341681866976604309540217217)
          ·
            refine ⟨256261400232453232155162913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 341681866976604309540217217 256261400232453232155162913)
            ·
              refine ⟨192196050174339924116372185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 256261400232453232155162913 192196050174339924116372185)
              ·
                refine ⟨144147037630754943087279139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 192196050174339924116372185 144147037630754943087279139)
                ·
                  refine ⟨216220556446132414630918709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 144147037630754943087279139 216220556446132414630918709)
                  ·
                    refine ⟨20270677166824913871648629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 216220556446132414630918709 20270677166824913871648629)
                    ·
                      refine ⟨1900375984389835675467059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20270677166824913871648629 1900375984389835675467059)
                      ·
                        rfl

theorem cell23_3700969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 2, 1, 5, 5].length) (baseStart_3700969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3700969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3700969 prefixEnd_3700969 := by exact prefixLift 3700969
  have htrace : WordTrace (prefixWord ++ tailWord_3700969) baseStart_3700969 baseEnd_3700969 := by
    simpa [prefixWord, tailWord_3700969, baseEnd_3700969] using wordTrace_append hprefix tailTrace_3700969
  have hstable : (prefixWord ++ tailWord_3700969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3700969).length < 2 ^ (prefixWord ++ tailWord_3700969).sum := by decide
  have hdescent : baseEnd_3700969 < baseStart_3700969 := by decide
  rcases family_descends (prefixWord ++ tailWord_3700969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3701006 : List Nat := [4, 1, 1, 2, 1, 2, 3, 1, 8]
def baseStart_3701006 : Nat := 118140960795 + 3701006 * 2 ^ 59
def prefixEnd_3701006 : Nat := 4983230072969 + 3 ^ 40 * 3701006 * 2
def baseEnd_3701006 : Nat := 211154998130450225633821

theorem tailTrace_3701006 : CollatzResearch.WordTrace tailWord_3701006 prefixEnd_3701006 211154998130450225633821 := by
  unfold tailWord_3701006
  simp only [CollatzResearch.WordTrace]
  refine ⟨16873347303736852293416359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 89991185619929878898220581 16873347303736852293416359)
  ·
    refine ⟨25310020955605278440124539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16873347303736852293416359 25310020955605278440124539)
    ·
      refine ⟨37965031433407917660186809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25310020955605278440124539 37965031433407917660186809)
      ·
        refine ⟨28473773575055938245140107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37965031433407917660186809 28473773575055938245140107)
        ·
          refine ⟨42710660362583907367710161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28473773575055938245140107 42710660362583907367710161)
          ·
            refine ⟨32032995271937930525782621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42710660362583907367710161 32032995271937930525782621)
            ·
              refine ⟨12012373226976723947168483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32032995271937930525782621 12012373226976723947168483)
              ·
                refine ⟨18018559840465085920752725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12012373226976723947168483 18018559840465085920752725)
                ·
                  refine ⟨211154998130450225633821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 18018559840465085920752725 211154998130450225633821)
                  ·
                    rfl

theorem cell23_3701006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 3, 1, 8].length) (baseStart_3701006 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3701006 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3701006 prefixEnd_3701006 := by exact prefixLift 3701006
  have htrace : WordTrace (prefixWord ++ tailWord_3701006) baseStart_3701006 baseEnd_3701006 := by
    simpa [prefixWord, tailWord_3701006, baseEnd_3701006] using wordTrace_append hprefix tailTrace_3701006
  have hstable : (prefixWord ++ tailWord_3701006).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3701006).length < 2 ^ (prefixWord ++ tailWord_3701006).sum := by decide
  have hdescent : baseEnd_3701006 < baseStart_3701006 := by decide
  rcases family_descends (prefixWord ++ tailWord_3701006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3701036 : List Nat := [2, 2, 1, 1, 1, 3, 2, 3, 3, 5]
def baseStart_3701036 : Nat := 118140960795 + 3701036 * 2 ^ 59
def prefixEnd_3701036 : Nat := 4983230072969 + 3 ^ 40 * 3701036 * 2
def baseEnd_3701036 : Nat := 633470129197895637776417

theorem tailTrace_3701036 : CollatzResearch.WordTrace tailWord_3701036 prefixEnd_3701036 633470129197895637776417 := by
  unfold tailWord_3701036
  simp only [CollatzResearch.WordTrace]
  refine ⟨67493936309893066735461481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89991915079857422313948641 67493936309893066735461481)
  ·
    refine ⟨50620452232419800051596111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67493936309893066735461481 50620452232419800051596111)
    ·
      refine ⟨75930678348629700077394167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50620452232419800051596111 75930678348629700077394167)
      ·
        refine ⟨113896017522944550116091251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75930678348629700077394167 113896017522944550116091251)
        ·
          refine ⟨170844026284416825174136877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113896017522944550116091251 170844026284416825174136877)
          ·
            refine ⟨64066509856656309440301329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 170844026284416825174136877 64066509856656309440301329)
            ·
              refine ⟨48049882392492232080225997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64066509856656309440301329 48049882392492232080225997)
              ·
                refine ⟨18018705897184587030084749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48049882392492232080225997 18018705897184587030084749)
                ·
                  refine ⟨6757014711444220136281781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18018705897184587030084749 6757014711444220136281781)
                  ·
                    refine ⟨633470129197895637776417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6757014711444220136281781 633470129197895637776417)
                    ·
                      rfl

theorem cell23_3701036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 5].length) (baseStart_3701036 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3701036 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3701036 prefixEnd_3701036 := by exact prefixLift 3701036
  have htrace : WordTrace (prefixWord ++ tailWord_3701036) baseStart_3701036 baseEnd_3701036 := by
    simpa [prefixWord, tailWord_3701036, baseEnd_3701036] using wordTrace_append hprefix tailTrace_3701036
  have hstable : (prefixWord ++ tailWord_3701036).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3701036).length < 2 ^ (prefixWord ++ tailWord_3701036).sum := by decide
  have hdescent : baseEnd_3701036 < baseStart_3701036 := by decide
  rcases family_descends (prefixWord ++ tailWord_3701036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3701043 : List Nat := [1, 1, 1, 2, 5, 1, 1, 3, 1, 5, 2]
def baseStart_3701043 : Nat := 118140960795 + 3701043 * 2 ^ 59
def prefixEnd_3701043 : Nat := 4983230072969 + 3 ^ 40 * 3701043 * 2
def baseEnd_3701043 : Nat := 1900413981958268385941719

theorem tailTrace_3701043 : CollatzResearch.WordTrace tailWord_3701043 prefixEnd_3701043 1900413981958268385941719 := by
  unfold tailWord_3701043
  simp only [CollatzResearch.WordTrace]
  refine ⟨134988127930760773666427783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89992085287173849110951855 134988127930760773666427783)
  ·
    refine ⟨202482191896141160499641675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134988127930760773666427783 202482191896141160499641675)
    ·
      refine ⟨303723287844211740749462513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 202482191896141160499641675 303723287844211740749462513)
      ·
        refine ⟨227792465883158805562096885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 303723287844211740749462513 227792465883158805562096885)
        ·
          refine ⟨21355543676546138021446583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 227792465883158805562096885 21355543676546138021446583)
          ·
            refine ⟨32033315514819207032169875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21355543676546138021446583 32033315514819207032169875)
            ·
              refine ⟨48049973272228810548254813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32033315514819207032169875 48049973272228810548254813)
              ·
                refine ⟨18018739977085803955595555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48049973272228810548254813 18018739977085803955595555)
                ·
                  refine ⟨27028109965628705933393333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18018739977085803955595555 27028109965628705933393333)
                  ·
                    refine ⟨2533885309277691181255625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 27028109965628705933393333 2533885309277691181255625)
                    ·
                      refine ⟨1900413981958268385941719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2533885309277691181255625 1900413981958268385941719)
                      ·
                        rfl

theorem cell23_3701043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 1, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 1, 3, 1, 5, 2].length) (baseStart_3701043 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3701043 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3701043 prefixEnd_3701043 := by exact prefixLift 3701043
  have htrace : WordTrace (prefixWord ++ tailWord_3701043) baseStart_3701043 baseEnd_3701043 := by
    simpa [prefixWord, tailWord_3701043, baseEnd_3701043] using wordTrace_append hprefix tailTrace_3701043
  have hstable : (prefixWord ++ tailWord_3701043).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3701043).length < 2 ^ (prefixWord ++ tailWord_3701043).sum := by decide
  have hdescent : baseEnd_3701043 < baseStart_3701043 := by decide
  rcases family_descends (prefixWord ++ tailWord_3701043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3701044 : List Nat := [2, 5, 1, 1, 1, 4, 1, 3, 1, 4]
def baseStart_3701044 : Nat := 118140960795 + 3701044 * 2 ^ 59
def prefixEnd_3701044 : Nat := 4983230072969 + 3 ^ 40 * 3701044 * 2
def baseEnd_3701044 : Nat := 633471498479640960676405

theorem tailTrace_3701044 : CollatzResearch.WordTrace tailWord_3701044 prefixEnd_3701044 633471498479640960676405 := by
  unfold tailWord_3701044
  simp only [CollatzResearch.WordTrace]
  refine ⟨67494082201878575418607093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89992109602504767224809457 67494082201878575418607093)
  ·
    refine ⟨6327570206426116445494415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 67494082201878575418607093 6327570206426116445494415)
    ·
      refine ⟨9491355309639174668241623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6327570206426116445494415 9491355309639174668241623)
      ·
        refine ⟨14237032964458762002362435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9491355309639174668241623 14237032964458762002362435)
        ·
          refine ⟨21355549446688143003543653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14237032964458762002362435 21355549446688143003543653)
          ·
            refine ⟨4004165521254026813164435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21355549446688143003543653 4004165521254026813164435)
            ·
              refine ⟨6006248281881040219746653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4004165521254026813164435 6006248281881040219746653)
              ·
                refine ⟨2252343105705390082404995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6006248281881040219746653 2252343105705390082404995)
                ·
                  refine ⟨3378514658558085123607493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2252343105705390082404995 3378514658558085123607493)
                  ·
                    refine ⟨633471498479640960676405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3378514658558085123607493 633471498479640960676405)
                    ·
                      rfl

theorem cell23_3701044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 4, 1, 3, 1, 4].length) (baseStart_3701044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3701044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3701044 prefixEnd_3701044 := by exact prefixLift 3701044
  have htrace : WordTrace (prefixWord ++ tailWord_3701044) baseStart_3701044 baseEnd_3701044 := by
    simpa [prefixWord, tailWord_3701044, baseEnd_3701044] using wordTrace_append hprefix tailTrace_3701044
  have hstable : (prefixWord ++ tailWord_3701044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3701044).length < 2 ^ (prefixWord ++ tailWord_3701044).sum := by decide
  have hdescent : baseEnd_3701044 < baseStart_3701044 := by decide
  rcases family_descends (prefixWord ++ tailWord_3701044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3701090 : List Nat := [3, 3, 2, 1, 1, 3, 1, 1, 3, 1, 4]
def baseStart_3701090 : Nat := 118140960795 + 3701090 * 2 ^ 59
def prefixEnd_3701090 : Nat := 4983230072969 + 3 ^ 40 * 3701090 * 2
def baseEnd_3701090 : Nat := 1900438115549029702054003

theorem tailTrace_3701090 : CollatzResearch.WordTrace tailWord_3701090 prefixEnd_3701090 1900438115549029702054003 := by
  unfold tailWord_3701090
  simp only [CollatzResearch.WordTrace]
  refine ⟨33747460540397625173347181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89993228107727000462259149 33747460540397625173347181)
  ·
    refine ⟨12655297702649109440005193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33747460540397625173347181 12655297702649109440005193)
    ·
      refine ⟨9491473276986832080003895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12655297702649109440005193 9491473276986832080003895)
      ·
        refine ⟨14237209915480248120005843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9491473276986832080003895 14237209915480248120005843)
        ·
          refine ⟨21355814873220372180008765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14237209915480248120005843 21355814873220372180008765)
          ·
            refine ⟨8008430577457639567503287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21355814873220372180008765 8008430577457639567503287)
            ·
              refine ⟨12012645866186459351254931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8008430577457639567503287 12012645866186459351254931)
              ·
                refine ⟨18018968799279689026882397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12012645866186459351254931 18018968799279689026882397)
                ·
                  refine ⟨6757113299729883385080899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18018968799279689026882397 6757113299729883385080899)
                  ·
                    refine ⟨10135669949594825077621349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6757113299729883385080899 10135669949594825077621349)
                    ·
                      refine ⟨1900438115549029702054003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10135669949594825077621349 1900438115549029702054003)
                      ·
                        rfl

theorem cell23_3701090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 3, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 3, 1, 1, 3, 1, 4].length) (baseStart_3701090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3701090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3701090 prefixEnd_3701090 := by exact prefixLift 3701090
  have htrace : WordTrace (prefixWord ++ tailWord_3701090) baseStart_3701090 baseEnd_3701090 := by
    simpa [prefixWord, tailWord_3701090, baseEnd_3701090] using wordTrace_append hprefix tailTrace_3701090
  have hstable : (prefixWord ++ tailWord_3701090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3701090).length < 2 ^ (prefixWord ++ tailWord_3701090).sum := by decide
  have hdescent : baseEnd_3701090 < baseStart_3701090 := by decide
  rcases family_descends (prefixWord ++ tailWord_3701090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3701116 : List Nat := [2, 2, 2, 1, 1, 1, 2, 2, 2, 2, 6]
def baseStart_3701116 : Nat := 118140960795 + 3701116 * 2 ^ 59
def prefixEnd_3701116 : Nat := 4983230072969 + 3 ^ 40 * 3701116 * 2
def baseEnd_3701116 : Nat := 1900451466046046600328883

theorem tailTrace_3701116 : CollatzResearch.WordTrace tailWord_3701116 prefixEnd_3701116 1900451466046046600328883 := by
  unfold tailWord_3701116
  simp only [CollatzResearch.WordTrace]
  refine ⟨67495395229748153566917601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89993860306330871422556801 67495395229748153566917601)
  ·
    refine ⟨50621546422311115175188201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67495395229748153566917601 50621546422311115175188201)
    ·
      refine ⟨37966159816733336381391151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50621546422311115175188201 37966159816733336381391151)
      ·
        refine ⟨56949239725100004572086727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37966159816733336381391151 56949239725100004572086727)
        ·
          refine ⟨85423859587650006858130091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56949239725100004572086727 85423859587650006858130091)
          ·
            refine ⟨128135789381475010287195137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85423859587650006858130091 128135789381475010287195137)
            ·
              refine ⟨96101842036106257715396353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 128135789381475010287195137 96101842036106257715396353)
              ·
                refine ⟨72076381527079693286547265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 96101842036106257715396353 72076381527079693286547265)
                ·
                  refine ⟨54057286145309769964910449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 72076381527079693286547265 54057286145309769964910449)
                  ·
                    refine ⟨40542964608982327473682837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 54057286145309769964910449 40542964608982327473682837)
                    ·
                      refine ⟨1900451466046046600328883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 40542964608982327473682837 1900451466046046600328883)
                      ·
                        rfl

theorem cell23_3701116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 2, 2, 2, 6].length) (baseStart_3701116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3701116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3701116 prefixEnd_3701116 := by exact prefixLift 3701116
  have htrace : WordTrace (prefixWord ++ tailWord_3701116) baseStart_3701116 baseEnd_3701116 := by
    simpa [prefixWord, tailWord_3701116, baseEnd_3701116] using wordTrace_append hprefix tailTrace_3701116
  have hstable : (prefixWord ++ tailWord_3701116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3701116).length < 2 ^ (prefixWord ++ tailWord_3701116).sum := by decide
  have hdescent : baseEnd_3701116 < baseStart_3701116 := by decide
  rcases family_descends (prefixWord ++ tailWord_3701116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3701124 : List Nat := [2, 3, 2, 1, 1, 2, 3, 4, 1, 2, 2]
def baseStart_3701124 : Nat := 118140960795 + 3701124 * 2 ^ 59
def prefixEnd_3701124 : Nat := 4983230072969 + 3 ^ 40 * 3701124 * 2
def baseEnd_3701124 : Nat := 1900455573891282569028847

theorem tailTrace_3701124 : CollatzResearch.WordTrace tailWord_3701124 prefixEnd_3701124 1900455573891282569028847 := by
  unfold tailWord_3701124
  simp only [CollatzResearch.WordTrace]
  refine ⟨67495541121733662250063213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89994054828978216333417617 67495541121733662250063213)
  ·
    refine ⟨25310827920650123343773705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67495541121733662250063213 25310827920650123343773705)
    ·
      refine ⟨18983120940487592507830279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25310827920650123343773705 18983120940487592507830279)
      ·
        refine ⟨28474681410731388761745419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18983120940487592507830279 28474681410731388761745419)
        ·
          refine ⟨42712022116097083142618129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28474681410731388761745419 42712022116097083142618129)
          ·
            refine ⟨32034016587072812356963597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42712022116097083142618129 32034016587072812356963597)
            ·
              refine ⟨12012756220152304633861349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32034016587072812356963597 12012756220152304633861349)
              ·
                refine ⟨2252391791278557118849003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12012756220152304633861349 2252391791278557118849003)
                ·
                  refine ⟨3378587686917835678273505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2252391791278557118849003 3378587686917835678273505)
                  ·
                    refine ⟨2533940765188376758705129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3378587686917835678273505 2533940765188376758705129)
                    ·
                      refine ⟨1900455573891282569028847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2533940765188376758705129 1900455573891282569028847)
                      ·
                        rfl

theorem cell23_3701124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 3, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 3, 4, 1, 2, 2].length) (baseStart_3701124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3701124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3701124 prefixEnd_3701124 := by exact prefixLift 3701124
  have htrace : WordTrace (prefixWord ++ tailWord_3701124) baseStart_3701124 baseEnd_3701124 := by
    simpa [prefixWord, tailWord_3701124, baseEnd_3701124] using wordTrace_append hprefix tailTrace_3701124
  have hstable : (prefixWord ++ tailWord_3701124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3701124).length < 2 ^ (prefixWord ++ tailWord_3701124).sum := by decide
  have hdescent : baseEnd_3701124 < baseStart_3701124 := by decide
  rcases family_descends (prefixWord ++ tailWord_3701124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3701136 : List Nat := [2, 1, 1, 1, 1, 1, 2, 1, 6, 2, 5]
def baseStart_3701136 : Nat := 118140960795 + 3701136 * 2 ^ 59
def prefixEnd_3701136 : Nat := 4983230072969 + 3 ^ 40 * 3701136 * 2
def baseEnd_3701136 : Nat := 1900461735659136522078791

theorem tailTrace_3701136 : CollatzResearch.WordTrace tailWord_3701136 prefixEnd_3701136 1900461735659136522078791 := by
  unfold tailWord_3701136
  simp only [CollatzResearch.WordTrace]
  refine ⟨67495759959711925274781631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89994346612949233699708841 67495759959711925274781631)
  ·
    refine ⟨101243639939567887912172447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67495759959711925274781631 101243639939567887912172447)
    ·
      refine ⟨151865459909351831868258671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101243639939567887912172447 151865459909351831868258671)
      ·
        refine ⟨227798189864027747802388007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151865459909351831868258671 227798189864027747802388007)
        ·
          refine ⟨341697284796041621703582011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 227798189864027747802388007 341697284796041621703582011)
          ·
            refine ⟨512545927194062432555373017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 341697284796041621703582011 512545927194062432555373017)
            ·
              refine ⟨384409445395546824416529763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 512545927194062432555373017 384409445395546824416529763)
              ·
                refine ⟨576614168093320236624794645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 384409445395546824416529763 576614168093320236624794645)
                ·
                  refine ⟨27028789129374386091787249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 576614168093320236624794645 27028789129374386091787249)
                  ·
                    refine ⟨20271591847030789568840437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27028789129374386091787249 20271591847030789568840437)
                    ·
                      refine ⟨1900461735659136522078791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20271591847030789568840437 1900461735659136522078791)
                      ·
                        rfl

theorem cell23_3701136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 1, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 1, 6, 2, 5].length) (baseStart_3701136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3701136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3701136 prefixEnd_3701136 := by exact prefixLift 3701136
  have htrace : WordTrace (prefixWord ++ tailWord_3701136) baseStart_3701136 baseEnd_3701136 := by
    simpa [prefixWord, tailWord_3701136, baseEnd_3701136] using wordTrace_append hprefix tailTrace_3701136
  have hstable : (prefixWord ++ tailWord_3701136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3701136).length < 2 ^ (prefixWord ++ tailWord_3701136).sum := by decide
  have hdescent : baseEnd_3701136 < baseStart_3701136 := by decide
  rcases family_descends (prefixWord ++ tailWord_3701136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3701193 : List Nat := [1, 2, 1, 1, 2, 1, 6, 1, 2, 2, 4]
def baseStart_3701193 : Nat := 118140960795 + 3701193 * 2 ^ 59
def prefixEnd_3701193 : Nat := 4983230072969 + 3 ^ 40 * 3701193 * 2
def baseEnd_3701193 : Nat := 1900491004056442799066029

theorem tailTrace_3701193 : CollatzResearch.WordTrace tailWord_3701193 prefixEnd_3701193 1900491004056442799066029 := by
  unfold tailWord_3701193
  simp only [CollatzResearch.WordTrace]
  refine ⟨134993598880217349284388233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89995732586811566189592155 134993598880217349284388233)
  ·
    refine ⟨101245199160163011963291175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134993598880217349284388233 101245199160163011963291175)
    ·
      refine ⟨151867798740244517944936763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101245199160163011963291175 151867798740244517944936763)
      ·
        refine ⟨227801698110366776917405145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151867798740244517944936763 227801698110366776917405145)
        ·
          refine ⟨170851273582775082688053859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 227801698110366776917405145 170851273582775082688053859)
          ·
            refine ⟨256276910374162624032080789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 170851273582775082688053859 256276910374162624032080789)
            ·
              refine ⟨12012980173788873001503787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 256276910374162624032080789 12012980173788873001503787)
              ·
                refine ⟨18019470260683309502255681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12012980173788873001503787 18019470260683309502255681)
                ·
                  refine ⟨13514602695512482126691761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18019470260683309502255681 13514602695512482126691761)
                  ·
                    refine ⟨10135952021634361595018821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13514602695512482126691761 10135952021634361595018821)
                    ·
                      refine ⟨1900491004056442799066029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10135952021634361595018821 1900491004056442799066029)
                      ·
                        rfl

theorem cell23_3701193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 6, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 6, 1, 2, 2, 4].length) (baseStart_3701193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3701193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3701193 prefixEnd_3701193 := by exact prefixLift 3701193
  have htrace : WordTrace (prefixWord ++ tailWord_3701193) baseStart_3701193 baseEnd_3701193 := by
    simpa [prefixWord, tailWord_3701193, baseEnd_3701193] using wordTrace_append hprefix tailTrace_3701193
  have hstable : (prefixWord ++ tailWord_3701193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3701193).length < 2 ^ (prefixWord ++ tailWord_3701193).sum := by decide
  have hdescent : baseEnd_3701193 < baseStart_3701193 := by decide
  rcases family_descends (prefixWord ++ tailWord_3701193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3701240 : List Nat := [2, 1, 2, 1, 1, 4, 2, 1, 2, 5, 2]
def baseStart_3701240 : Nat := 118140960795 + 3701240 * 2 ^ 59
def prefixEnd_3701240 : Nat := 4983230072969 + 3 ^ 40 * 3701240 * 2
def baseEnd_3701240 : Nat := 1900515137647204115178313

theorem tailTrace_3701240 : CollatzResearch.WordTrace tailWord_3701240 prefixEnd_3701240 1900515137647204115178313 := by
  unfold tailWord_3701240
  simp only [CollatzResearch.WordTrace]
  refine ⟨67497656555523538155674587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89996875407364717540899449 67497656555523538155674587)
  ·
    refine ⟨101246484833285307233511881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67497656555523538155674587 101246484833285307233511881)
    ·
      refine ⟨75934863624963980425133911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101246484833285307233511881 75934863624963980425133911)
      ·
        refine ⟨113902295437445970637700867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75934863624963980425133911 113902295437445970637700867)
        ·
          refine ⟨170853443156168955956551301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113902295437445970637700867 170853443156168955956551301)
          ·
            refine ⟨32035020591781679241853369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 170853443156168955956551301 32035020591781679241853369)
            ·
              refine ⟨24026265443836259431390027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32035020591781679241853369 24026265443836259431390027)
              ·
                refine ⟨36039398165754389147085041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24026265443836259431390027 36039398165754389147085041)
                ·
                  refine ⟨27029548624315791860313781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36039398165754389147085041 27029548624315791860313781)
                  ·
                    refine ⟨2534020183529605486904417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 27029548624315791860313781 2534020183529605486904417)
                    ·
                      refine ⟨1900515137647204115178313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2534020183529605486904417 1900515137647204115178313)
                      ·
                        rfl

theorem cell23_3701240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 2, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 2, 1, 2, 5, 2].length) (baseStart_3701240 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3701240 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3701240 prefixEnd_3701240 := by exact prefixLift 3701240
  have htrace : WordTrace (prefixWord ++ tailWord_3701240) baseStart_3701240 baseEnd_3701240 := by
    simpa [prefixWord, tailWord_3701240, baseEnd_3701240] using wordTrace_append hprefix tailTrace_3701240
  have hstable : (prefixWord ++ tailWord_3701240).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3701240).length < 2 ^ (prefixWord ++ tailWord_3701240).sum := by decide
  have hdescent : baseEnd_3701240 < baseStart_3701240 := by decide
  rcases family_descends (prefixWord ++ tailWord_3701240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3701253 : List Nat := [1, 3, 1, 1, 2, 2, 2, 1, 3, 3, 4]
def baseStart_3701253 : Nat := 118140960795 + 3701253 * 2 ^ 59
def prefixEnd_3701253 : Nat := 4983230072969 + 3 ^ 40 * 3701253 * 2
def baseEnd_3701253 : Nat := 1900521812895712564315753

theorem tailTrace_3701253 : CollatzResearch.WordTrace tailWord_3701253 prefixEnd_3701253 1900521812895712564315753 := by
  unfold tailWord_3701253
  simp only [CollatzResearch.WordTrace]
  refine ⟨134995787259999979531572413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89997191506666653021048275 134995787259999979531572413)
  ·
    refine ⟨50623420222499992324339655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 134995787259999979531572413 50623420222499992324339655)
    ·
      refine ⟨75935130333749988486509483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50623420222499992324339655 75935130333749988486509483)
      ·
        refine ⟨113902695500624982729764225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75935130333749988486509483 113902695500624982729764225)
        ·
          refine ⟨85427021625468737047323169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 113902695500624982729764225 85427021625468737047323169)
          ·
            refine ⟨64070266219101552785492377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85427021625468737047323169 64070266219101552785492377)
            ·
              refine ⟨48052699664326164589119283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64070266219101552785492377 48052699664326164589119283)
              ·
                refine ⟨72079049496489246883678925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48052699664326164589119283 72079049496489246883678925)
                ·
                  refine ⟨27029643561183467581379597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 72079049496489246883678925 27029643561183467581379597)
                  ·
                    refine ⟨10136116335443800343017349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27029643561183467581379597 10136116335443800343017349)
                    ·
                      refine ⟨1900521812895712564315753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10136116335443800343017349 1900521812895712564315753)
                      ·
                        rfl

theorem cell23_3701253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 2, 1, 3, 3, 4].length) (baseStart_3701253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3701253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3701253 prefixEnd_3701253 := by exact prefixLift 3701253
  have htrace : WordTrace (prefixWord ++ tailWord_3701253) baseStart_3701253 baseEnd_3701253 := by
    simpa [prefixWord, tailWord_3701253, baseEnd_3701253] using wordTrace_append hprefix tailTrace_3701253
  have hstable : (prefixWord ++ tailWord_3701253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3701253).length < 2 ^ (prefixWord ++ tailWord_3701253).sum := by decide
  have hdescent : baseEnd_3701253 < baseStart_3701253 := by decide
  rcases family_descends (prefixWord ++ tailWord_3701253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3701347 : List Nat := [1, 1, 1, 5, 1, 2, 2, 1, 4, 3, 2]
def baseStart_3701347 : Nat := 118140960795 + 3701347 * 2 ^ 59
def prefixEnd_3701347 : Nat := 4983230072969 + 3 ^ 40 * 3701347 * 2
def baseEnd_3701347 : Nat := 1900570080077235196540321

theorem tailTrace_3701347 : CollatzResearch.WordTrace tailWord_3701347 prefixEnd_3701347 1900570080077235196540321 := by
  unfold tailWord_3701347
  simp only [CollatzResearch.WordTrace]
  refine ⟨134999215721659433585494295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89999477147772955723662863 134999215721659433585494295)
  ·
    refine ⟨202498823582489150378241443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134999215721659433585494295 202498823582489150378241443)
    ·
      refine ⟨303748235373733725567362165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 202498823582489150378241443 303748235373733725567362165)
      ·
        refine ⟨28476397066287536771940203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 303748235373733725567362165 28476397066287536771940203)
        ·
          refine ⟨42714595599431305157910305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28476397066287536771940203 42714595599431305157910305)
          ·
            refine ⟨32035946699573478868432729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42714595599431305157910305 32035946699573478868432729)
            ·
              refine ⟨24026960024680109151324547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32035946699573478868432729 24026960024680109151324547)
              ·
                refine ⟨36040440037020163726986821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24026960024680109151324547 36040440037020163726986821)
                ·
                  refine ⟨6757582506941280698810029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36040440037020163726986821 6757582506941280698810029)
                  ·
                    refine ⟨2534093440102980262053761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6757582506941280698810029 2534093440102980262053761)
                    ·
                      refine ⟨1900570080077235196540321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2534093440102980262053761 1900570080077235196540321)
                      ·
                        rfl

theorem cell23_3701347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 2, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 2, 1, 4, 3, 2].length) (baseStart_3701347 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3701347 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3701347 prefixEnd_3701347 := by exact prefixLift 3701347
  have htrace : WordTrace (prefixWord ++ tailWord_3701347) baseStart_3701347 baseEnd_3701347 := by
    simpa [prefixWord, tailWord_3701347, baseEnd_3701347] using wordTrace_append hprefix tailTrace_3701347
  have hstable : (prefixWord ++ tailWord_3701347).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3701347).length < 2 ^ (prefixWord ++ tailWord_3701347).sum := by decide
  have hdescent : baseEnd_3701347 < baseStart_3701347 := by decide
  rcases family_descends (prefixWord ++ tailWord_3701347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3701354 : List Nat := [3, 1, 3, 2, 1, 1, 4, 1, 3, 1, 3]
def baseStart_3701354 : Nat := 118140960795 + 3701354 * 2 ^ 59
def prefixEnd_3701354 : Nat := 4983230072969 + 3 ^ 40 * 3701354 * 2
def baseEnd_3701354 : Nat := 1900573674441816669152789

theorem tailTrace_3701354 : CollatzResearch.WordTrace tailWord_3701354 prefixEnd_3701354 1900573674441816669152789 := by
  unfold tailWord_3701354
  simp only [CollatzResearch.WordTrace]
  refine ⟨33749867758158518445249779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89999647355089382520666077 33749867758158518445249779)
  ·
    refine ⟨50624801637237777667874669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33749867758158518445249779 50624801637237777667874669)
    ·
      refine ⟨18984300613964166625453001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50624801637237777667874669 18984300613964166625453001)
      ·
        refine ⟨14238225460473124969089751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18984300613964166625453001 14238225460473124969089751)
        ·
          refine ⟨21357338190709687453634627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14238225460473124969089751 21357338190709687453634627)
          ·
            refine ⟨32036007286064531180451941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21357338190709687453634627 32036007286064531180451941)
            ·
              refine ⟨6006751366137099596334739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32036007286064531180451941 6006751366137099596334739)
              ·
                refine ⟨9010127049205649394502109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6006751366137099596334739 9010127049205649394502109)
                ·
                  refine ⟨3378797643452118522938291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9010127049205649394502109 3378797643452118522938291)
                  ·
                    refine ⟨5068196465178177784407437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3378797643452118522938291 5068196465178177784407437)
                    ·
                      refine ⟨1900573674441816669152789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5068196465178177784407437 1900573674441816669152789)
                      ·
                        rfl

theorem cell23_3701354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 4, 1, 3, 1, 3].length) (baseStart_3701354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3701354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3701354 prefixEnd_3701354 := by exact prefixLift 3701354
  have htrace : WordTrace (prefixWord ++ tailWord_3701354) baseStart_3701354 baseEnd_3701354 := by
    simpa [prefixWord, tailWord_3701354, baseEnd_3701354] using wordTrace_append hprefix tailTrace_3701354
  have hstable : (prefixWord ++ tailWord_3701354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3701354).length < 2 ^ (prefixWord ++ tailWord_3701354).sum := by decide
  have hdescent : baseEnd_3701354 < baseStart_3701354 := by decide
  rcases family_descends (prefixWord ++ tailWord_3701354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3701377 : List Nat := [1, 2, 4, 2, 1, 1, 1, 1, 2, 6, 2]
def baseStart_3701377 : Nat := 118140960795 + 3701377 * 2 ^ 59
def prefixEnd_3701377 : Nat := 4983230072969 + 3 ^ 40 * 3701377 * 2
def baseEnd_3701377 : Nat := 1900585484496870079165183

theorem tailTrace_3701377 : CollatzResearch.WordTrace tailWord_3701377 prefixEnd_3701377 1900585484496870079165183 := by
  unfold tailWord_3701377
  simp only [CollatzResearch.WordTrace]
  refine ⟨135000309911550748709086385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90000206607700499139390923 135000309911550748709086385)
  ·
    refine ⟨101250232433663061531814789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135000309911550748709086385 101250232433663061531814789)
    ·
      refine ⟨18984418581311824037215273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 101250232433663061531814789 18984418581311824037215273)
      ·
        refine ⟨14238313935983868027911455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18984418581311824037215273 14238313935983868027911455)
        ·
          refine ⟨21357470903975802041867183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14238313935983868027911455 21357470903975802041867183)
          ·
            refine ⟨32036206355963703062800775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21357470903975802041867183 32036206355963703062800775)
            ·
              refine ⟨48054309533945554594201163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32036206355963703062800775 48054309533945554594201163)
              ·
                refine ⟨72081464300918331891301745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48054309533945554594201163 72081464300918331891301745)
                ·
                  refine ⟨54061098225688748918476309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 72081464300918331891301745 54061098225688748918476309)
                  ·
                    refine ⟨2534113979329160105553577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 54061098225688748918476309 2534113979329160105553577)
                    ·
                      refine ⟨1900585484496870079165183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2534113979329160105553577 1900585484496870079165183)
                      ·
                        rfl

theorem cell23_3701377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 1, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 1, 1, 2, 6, 2].length) (baseStart_3701377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3701377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3701377 prefixEnd_3701377 := by exact prefixLift 3701377
  have htrace : WordTrace (prefixWord ++ tailWord_3701377) baseStart_3701377 baseEnd_3701377 := by
    simpa [prefixWord, tailWord_3701377, baseEnd_3701377] using wordTrace_append hprefix tailTrace_3701377
  have hstable : (prefixWord ++ tailWord_3701377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3701377).length < 2 ^ (prefixWord ++ tailWord_3701377).sum := by decide
  have hdescent : baseEnd_3701377 < baseStart_3701377 := by decide
  rcases family_descends (prefixWord ++ tailWord_3701377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3701394 : List Nat := [3, 2, 3, 1, 2, 1, 2, 3, 1, 1, 4]
def baseStart_3701394 : Nat := 118140960795 + 3701394 * 2 ^ 59
def prefixEnd_3701394 : Nat := 4983230072969 + 3 ^ 40 * 3701394 * 2
def baseEnd_3701394 : Nat := 1900594213667996512652605

theorem tailTrace_3701394 : CollatzResearch.WordTrace tailWord_3701394 prefixEnd_3701394 1900594213667996512652605 := by
  unfold tailWord_3701394
  simp only [CollatzResearch.WordTrace]
  refine ⟨33750232488122290153113809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90000619968326107074970157 33750232488122290153113809)
  ·
    refine ⟨25312674366091717614835357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33750232488122290153113809 25312674366091717614835357)
    ·
      refine ⟨9492252887284394105563259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25312674366091717614835357 9492252887284394105563259)
      ·
        refine ⟨14238379330926591158344889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9492252887284394105563259 14238379330926591158344889)
        ·
          refine ⟨10678784498194943368758667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14238379330926591158344889 10678784498194943368758667)
          ·
            refine ⟨16018176747292415053138001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10678784498194943368758667 16018176747292415053138001)
            ·
              refine ⟨12013632560469311289853501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16018176747292415053138001 12013632560469311289853501)
              ·
                refine ⟨4505112210175991733695063, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12013632560469311289853501 4505112210175991733695063)
                ·
                  refine ⟨6757668315263987600542595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4505112210175991733695063 6757668315263987600542595)
                  ·
                    refine ⟨10136502472895981400813893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6757668315263987600542595 10136502472895981400813893)
                    ·
                      refine ⟨1900594213667996512652605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10136502472895981400813893 1900594213667996512652605)
                      ·
                        rfl

theorem cell23_3701394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 2, 3, 1, 1, 4].length) (baseStart_3701394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3701394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3701394 prefixEnd_3701394 := by exact prefixLift 3701394
  have htrace : WordTrace (prefixWord ++ tailWord_3701394) baseStart_3701394 baseEnd_3701394 := by
    simpa [prefixWord, tailWord_3701394, baseEnd_3701394] using wordTrace_append hprefix tailTrace_3701394
  have hstable : (prefixWord ++ tailWord_3701394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3701394).length < 2 ^ (prefixWord ++ tailWord_3701394).sum := by decide
  have hdescent : baseEnd_3701394 < baseStart_3701394 := by decide
  rcases family_descends (prefixWord ++ tailWord_3701394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3701421 : List Nat := [1, 5, 2, 1, 1, 2, 4, 1, 2, 4]
def baseStart_3701421 : Nat := 118140960795 + 3701421 * 2 ^ 59
def prefixEnd_3701421 : Nat := 4983230072969 + 3 ^ 40 * 3701421 * 2
def baseEnd_3701421 : Nat := 633536025881889302338327

theorem tailTrace_3701421 : CollatzResearch.WordTrace tailWord_3701421 prefixEnd_3701421 633536025881889302338327 := by
  unfold tailWord_3701421
  simp only [CollatzResearch.WordTrace]
  refine ⟨135001914723391344223688117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90001276482260896149125411 135001914723391344223688117)
  ·
    refine ⟨12656429505317938520970761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 135001914723391344223688117 12656429505317938520970761)
    ·
      refine ⟨9492322128988453890728071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12656429505317938520970761 9492322128988453890728071)
      ·
        refine ⟨14238483193482680836092107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9492322128988453890728071 14238483193482680836092107)
        ·
          refine ⟨21357724790224021254138161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14238483193482680836092107 21357724790224021254138161)
          ·
            refine ⟨16018293592668015940603621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21357724790224021254138161 16018293592668015940603621)
            ·
              refine ⟨3003430048625252988863179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16018293592668015940603621 3003430048625252988863179)
              ·
                refine ⟨4505145072937879483294769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3003430048625252988863179 4505145072937879483294769)
                ·
                  refine ⟨3378858804703409612471077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4505145072937879483294769 3378858804703409612471077)
                  ·
                    refine ⟨633536025881889302338327, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3378858804703409612471077 633536025881889302338327)
                    ·
                      rfl

theorem cell23_3701421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 4, 1, 2, 4].length) (baseStart_3701421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3701421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3701421 prefixEnd_3701421 := by exact prefixLift 3701421
  have htrace : WordTrace (prefixWord ++ tailWord_3701421) baseStart_3701421 baseEnd_3701421 := by
    simpa [prefixWord, tailWord_3701421, baseEnd_3701421] using wordTrace_append hprefix tailTrace_3701421
  have hstable : (prefixWord ++ tailWord_3701421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3701421).length < 2 ^ (prefixWord ++ tailWord_3701421).sum := by decide
  have hdescent : baseEnd_3701421 < baseStart_3701421 := by decide
  rcases family_descends (prefixWord ++ tailWord_3701421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3701431 : List Nat := [1, 1, 3, 1, 6, 2, 1, 2, 1, 2, 3]
def baseStart_3701431 : Nat := 118140960795 + 3701431 * 2 ^ 59
def prefixEnd_3701431 : Nat := 4983230072969 + 3 ^ 40 * 3701431 * 2
def baseEnd_3701431 : Nat := 1900613212452212867889935

theorem tailTrace_3701431 : CollatzResearch.WordTrace tailWord_3701431 prefixEnd_3701431 1900613212452212867889935 := by
  unfold tailWord_3701431
  simp only [CollatzResearch.WordTrace]
  refine ⟨135002279453355115931552147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90001519635570077287701431 135002279453355115931552147)
  ·
    refine ⟨202503419180032673897328221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135002279453355115931552147 202503419180032673897328221)
    ·
      refine ⟨75938782192512252711498083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 202503419180032673897328221 75938782192512252711498083)
      ·
        refine ⟨113908173288768379067247125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75938782192512252711498083 113908173288768379067247125)
        ·
          refine ⟨5339445622911017768777209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 113908173288768379067247125 5339445622911017768777209)
          ·
            refine ⟨4004584217183263326582907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5339445622911017768777209 4004584217183263326582907)
            ·
              refine ⟨6006876325774894989874361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4004584217183263326582907 6006876325774894989874361)
              ·
                refine ⟨4505157244331171242405771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6006876325774894989874361 4505157244331171242405771)
                ·
                  refine ⟨6757735866496756863608657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4505157244331171242405771 6757735866496756863608657)
                  ·
                    refine ⟨5068301899872567647706493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6757735866496756863608657 5068301899872567647706493)
                    ·
                      refine ⟨1900613212452212867889935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5068301899872567647706493 1900613212452212867889935)
                      ·
                        rfl

theorem cell23_3701431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 2, 1, 2, 1, 2, 3].length) (baseStart_3701431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3701431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3701431 prefixEnd_3701431 := by exact prefixLift 3701431
  have htrace : WordTrace (prefixWord ++ tailWord_3701431) baseStart_3701431 baseEnd_3701431 := by
    simpa [prefixWord, tailWord_3701431, baseEnd_3701431] using wordTrace_append hprefix tailTrace_3701431
  have hstable : (prefixWord ++ tailWord_3701431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3701431).length < 2 ^ (prefixWord ++ tailWord_3701431).sum := by decide
  have hdescent : baseEnd_3701431 < baseStart_3701431 := by decide
  rcases family_descends (prefixWord ++ tailWord_3701431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3701441 : List Nat := [1, 2, 6, 2, 1, 1, 1, 2, 1, 2, 4]
def baseStart_3701441 : Nat := 118140960795 + 3701441 * 2 ^ 59
def prefixEnd_3701441 : Nat := 4983230072969 + 3 ^ 40 * 3701441 * 2
def baseEnd_3701441 : Nat := 1900618347258757828764889

theorem tailTrace_3701441 : CollatzResearch.WordTrace tailWord_3701441 prefixEnd_3701441 1900618347258757828764889 := by
  unfold tailWord_3701441
  simp only [CollatzResearch.WordTrace]
  refine ⟨135002644183318887639416177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90001762788879258426277451 135002644183318887639416177)
  ·
    refine ⟨101251983137489165729562133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135002644183318887639416177 101251983137489165729562133)
    ·
      refine ⟨4746186709569804643573225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 101251983137489165729562133 4746186709569804643573225)
      ·
        refine ⟨3559640032177353482679919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4746186709569804643573225 3559640032177353482679919)
        ·
          refine ⟨5339460048266030224019879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3559640032177353482679919 5339460048266030224019879)
          ·
            refine ⟨8009190072399045336029819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5339460048266030224019879 8009190072399045336029819)
            ·
              refine ⟨12013785108598568004044729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8009190072399045336029819 12013785108598568004044729)
              ·
                refine ⟨9010338831448926003033547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12013785108598568004044729 9010338831448926003033547)
                ·
                  refine ⟨13515508247173389004550321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9010338831448926003033547 13515508247173389004550321)
                  ·
                    refine ⟨10136631185380041753412741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13515508247173389004550321 10136631185380041753412741)
                    ·
                      refine ⟨1900618347258757828764889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10136631185380041753412741 1900618347258757828764889)
                      ·
                        rfl

theorem cell23_3701441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 1, 1, 2, 1, 2, 4].length) (baseStart_3701441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3701441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3701441 prefixEnd_3701441 := by exact prefixLift 3701441
  have htrace : WordTrace (prefixWord ++ tailWord_3701441) baseStart_3701441 baseEnd_3701441 := by
    simpa [prefixWord, tailWord_3701441, baseEnd_3701441] using wordTrace_append hprefix tailTrace_3701441
  have hstable : (prefixWord ++ tailWord_3701441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3701441).length < 2 ^ (prefixWord ++ tailWord_3701441).sum := by decide
  have hdescent : baseEnd_3701441 < baseStart_3701441 := by decide
  rcases family_descends (prefixWord ++ tailWord_3701441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3701444 : List Nat := [2, 3, 3, 1, 1, 3, 1, 2, 1, 3, 3]
def baseStart_3701444 : Nat := 118140960795 + 3701444 * 2 ^ 59
def prefixEnd_3701444 : Nat := 4983230072969 + 3 ^ 40 * 3701444 * 2
def baseEnd_3701444 : Nat := 1900619887700721317027375

theorem tailTrace_3701444 : CollatzResearch.WordTrace tailWord_3701444 prefixEnd_3701444 1900619887700721317027375 := by
  unfold tailWord_3701444
  simp only [CollatzResearch.WordTrace]
  refine ⟨67501376801154009575887693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90001835734872012767850257 67501376801154009575887693)
  ·
    refine ⟨25313016300432753590957885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67501376801154009575887693 25313016300432753590957885)
    ·
      refine ⟨9492381112662282596609207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25313016300432753590957885 9492381112662282596609207)
      ·
        refine ⟨14238571668993423894913811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9492381112662282596609207 14238571668993423894913811)
        ·
          refine ⟨21357857503490135842370717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14238571668993423894913811 21357857503490135842370717)
          ·
            refine ⟨8009196563808800940889019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21357857503490135842370717 8009196563808800940889019)
            ·
              refine ⟨12013794845713201411333529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8009196563808800940889019 12013794845713201411333529)
              ·
                refine ⟨9010346134284901058500147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12013794845713201411333529 9010346134284901058500147)
                ·
                  refine ⟨13515519201427351587750221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9010346134284901058500147 13515519201427351587750221)
                  ·
                    refine ⟨5068319700535256845406333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13515519201427351587750221 5068319700535256845406333)
                    ·
                      refine ⟨1900619887700721317027375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5068319700535256845406333 1900619887700721317027375)
                      ·
                        rfl

theorem cell23_3701444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 3, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 3, 1, 2, 1, 3, 3].length) (baseStart_3701444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3701444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3701444 prefixEnd_3701444 := by exact prefixLift 3701444
  have htrace : WordTrace (prefixWord ++ tailWord_3701444) baseStart_3701444 baseEnd_3701444 := by
    simpa [prefixWord, tailWord_3701444, baseEnd_3701444] using wordTrace_append hprefix tailTrace_3701444
  have hstable : (prefixWord ++ tailWord_3701444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3701444).length < 2 ^ (prefixWord ++ tailWord_3701444).sum := by decide
  have hdescent : baseEnd_3701444 < baseStart_3701444 := by decide
  rcases family_descends (prefixWord ++ tailWord_3701444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3701477 : List Nat := [1, 3, 1, 4, 1, 3, 1, 1, 2, 6]
def baseStart_3701477 : Nat := 118140960795 + 3701477 * 2 ^ 59
def prefixEnd_3701477 : Nat := 4983230072969 + 3 ^ 40 * 3701477 * 2
def baseEnd_3701477 : Nat := 633545610854106562638241

theorem tailTrace_3701477 : CollatzResearch.WordTrace tailWord_3701477 prefixEnd_3701477 633545610854106562638241 := by
  unfold tailWord_3701477
  simp only [CollatzResearch.WordTrace]
  refine ⟨135003957211188465787726685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90002638140792310525151123 135003957211188465787726685)
  ·
    refine ⟨50626483954195674670397507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 135003957211188465787726685 50626483954195674670397507)
    ·
      refine ⟨75939725931293512005596261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50626483954195674670397507 75939725931293512005596261)
      ·
        refine ⟨14238698612117533501049299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 75939725931293512005596261 14238698612117533501049299)
        ·
          refine ⟨21358047918176300251573949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14238698612117533501049299 21358047918176300251573949)
          ·
            refine ⟨8009267969316112594340231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21358047918176300251573949 8009267969316112594340231)
            ·
              refine ⟨12013901953974168891510347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8009267969316112594340231 12013901953974168891510347)
              ·
                refine ⟨18020852930961253337265521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12013901953974168891510347 18020852930961253337265521)
                ·
                  refine ⟨13515639698220940002949141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18020852930961253337265521 13515639698220940002949141)
                  ·
                    refine ⟨633545610854106562638241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13515639698220940002949141 633545610854106562638241)
                    ·
                      rfl

theorem cell23_3701477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 3, 1, 1, 2, 6].length) (baseStart_3701477 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3701477 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3701477 prefixEnd_3701477 := by exact prefixLift 3701477
  have htrace : WordTrace (prefixWord ++ tailWord_3701477) baseStart_3701477 baseEnd_3701477 := by
    simpa [prefixWord, tailWord_3701477, baseEnd_3701477] using wordTrace_append hprefix tailTrace_3701477
  have hstable : (prefixWord ++ tailWord_3701477).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3701477).length < 2 ^ (prefixWord ++ tailWord_3701477).sum := by decide
  have hdescent : baseEnd_3701477 < baseStart_3701477 := by decide
  rcases family_descends (prefixWord ++ tailWord_3701477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3701484 : List Nat := [2, 2, 1, 1, 2, 2, 1, 2, 6, 2, 2]
def baseStart_3701484 : Nat := 118140960795 + 3701484 * 2 ^ 59
def prefixEnd_3701484 : Nat := 4983230072969 + 3 ^ 40 * 3701484 * 2
def baseEnd_3701484 : Nat := 1900640426926901160527191

theorem tailTrace_3701484 : CollatzResearch.WordTrace tailWord_3701484 prefixEnd_3701484 1900640426926901160527191 := by
  unfold tailWord_3701484
  simp only [CollatzResearch.WordTrace]
  refine ⟨67502106261081552991615753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90002808348108737322154337 67502106261081552991615753)
  ·
    refine ⟨50626579695811164743711815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67502106261081552991615753 50626579695811164743711815)
    ·
      refine ⟨75939869543716747115567723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50626579695811164743711815 75939869543716747115567723)
      ·
        refine ⟨113909804315575120673351585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75939869543716747115567723 113909804315575120673351585)
        ·
          refine ⟨85432353236681340505013689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 113909804315575120673351585 85432353236681340505013689)
          ·
            refine ⟨64074264927511005378760267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85432353236681340505013689 64074264927511005378760267)
            ·
              refine ⟨96111397391266508068140401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64074264927511005378760267 96111397391266508068140401)
              ·
                refine ⟨72083548043449881051105301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 96111397391266508068140401 72083548043449881051105301)
                ·
                  refine ⟨3378916314536713174270561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 72083548043449881051105301 3378916314536713174270561)
                  ·
                    refine ⟨2534187235902534880702921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3378916314536713174270561 2534187235902534880702921)
                    ·
                      refine ⟨1900640426926901160527191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2534187235902534880702921 1900640426926901160527191)
                      ·
                        rfl

theorem cell23_3701484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 6, 2, 2].length) (baseStart_3701484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3701484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3701484 prefixEnd_3701484 := by exact prefixLift 3701484
  have htrace : WordTrace (prefixWord ++ tailWord_3701484) baseStart_3701484 baseEnd_3701484 := by
    simpa [prefixWord, tailWord_3701484, baseEnd_3701484] using wordTrace_append hprefix tailTrace_3701484
  have hstable : (prefixWord ++ tailWord_3701484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3701484).length < 2 ^ (prefixWord ++ tailWord_3701484).sum := by decide
  have hdescent : baseEnd_3701484 < baseStart_3701484 := by decide
  rcases family_descends (prefixWord ++ tailWord_3701484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3701581 : List Nat := [1, 6, 1, 2, 2, 1, 1, 1, 1, 2, 5]
def baseStart_3701581 : Nat := 118140960795 + 3701581 * 2 ^ 59
def prefixEnd_3701581 : Nat := 4983230072969 + 3 ^ 40 * 3701581 * 2
def baseEnd_3701581 : Nat := 1900690234550387281014245

theorem tailTrace_3701581 : CollatzResearch.WordTrace tailWord_3701581 prefixEnd_3701581 1900690234550387281014245 := by
  unfold tailWord_3701581
  simp only [CollatzResearch.WordTrace]
  refine ⟨135007750402811691549512597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90005166935207794366341731 135007750402811691549512597)
  ·
    refine ⟨6328488300131798041383403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 135007750402811691549512597 6328488300131798041383403)
    ·
      refine ⟨9492732450197697062075105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6328488300131798041383403 9492732450197697062075105)
      ·
        refine ⟨7119549337648272796556329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9492732450197697062075105 7119549337648272796556329)
        ·
          refine ⟨5339662003236204597417247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7119549337648272796556329 5339662003236204597417247)
          ·
            refine ⟨8009493004854306896125871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5339662003236204597417247 8009493004854306896125871)
            ·
              refine ⟨12014239507281460344188807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8009493004854306896125871 12014239507281460344188807)
              ·
                refine ⟨18021359260922190516283211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12014239507281460344188807 18021359260922190516283211)
                ·
                  refine ⟨27032038891383285774424817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18021359260922190516283211 27032038891383285774424817)
                  ·
                    refine ⟨20274029168537464330818613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27032038891383285774424817 20274029168537464330818613)
                    ·
                      refine ⟨1900690234550387281014245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20274029168537464330818613 1900690234550387281014245)
                      ·
                        rfl

theorem cell23_3701581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 1, 1, 1, 1, 2, 5].length) (baseStart_3701581 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3701581 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3701581 prefixEnd_3701581 := by exact prefixLift 3701581
  have htrace : WordTrace (prefixWord ++ tailWord_3701581) baseStart_3701581 baseEnd_3701581 := by
    simpa [prefixWord, tailWord_3701581, baseEnd_3701581] using wordTrace_append hprefix tailTrace_3701581
  have hstable : (prefixWord ++ tailWord_3701581).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3701581).length < 2 ^ (prefixWord ++ tailWord_3701581).sum := by decide
  have hdescent : baseEnd_3701581 < baseStart_3701581 := by decide
  rcases family_descends (prefixWord ++ tailWord_3701581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3701584 : List Nat := [2, 1, 1, 1, 1, 4, 5, 1, 3, 4]
def baseStart_3701584 : Nat := 118140960795 + 3701584 * 2 ^ 59
def prefixEnd_3701584 : Nat := 4983230072969 + 3 ^ 40 * 3701584 * 2
def baseEnd_3701584 : Nat := 633563924997450256425577

theorem tailTrace_3701584 : CollatzResearch.WordTrace tailWord_3701584 prefixEnd_3701584 633563924997450256425577 := by
  unfold tailWord_3701584
  simp only [CollatzResearch.WordTrace]
  refine ⟨67503929910900411530935903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90005239881200548707914537 67503929910900411530935903)
  ·
    refine ⟨101255894866350617296403855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67503929910900411530935903 101255894866350617296403855)
    ·
      refine ⟨151883842299525925944605783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101255894866350617296403855 151883842299525925944605783)
      ·
        refine ⟨227825763449288888916908675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151883842299525925944605783 227825763449288888916908675)
        ·
          refine ⟨341738645173933333375363013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 227825763449288888916908675 341738645173933333375363013)
          ·
            refine ⟨64075995970112500007880565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 341738645173933333375363013 64075995970112500007880565)
            ·
              refine ⟨6007124622198046875738803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 64075995970112500007880565 6007124622198046875738803)
              ·
                refine ⟨9010686933297070313608205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6007124622198046875738803 9010686933297070313608205)
                ·
                  refine ⟨3379007599986401367603077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9010686933297070313608205 3379007599986401367603077)
                  ·
                    refine ⟨633563924997450256425577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3379007599986401367603077 633563924997450256425577)
                    ·
                      rfl

theorem cell23_3701584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 5, 1, 3, 4].length) (baseStart_3701584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3701584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3701584 prefixEnd_3701584 := by exact prefixLift 3701584
  have htrace : WordTrace (prefixWord ++ tailWord_3701584) baseStart_3701584 baseEnd_3701584 := by
    simpa [prefixWord, tailWord_3701584, baseEnd_3701584] using wordTrace_append hprefix tailTrace_3701584
  have hstable : (prefixWord ++ tailWord_3701584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3701584).length < 2 ^ (prefixWord ++ tailWord_3701584).sum := by decide
  have hdescent : baseEnd_3701584 < baseStart_3701584 := by decide
  rcases family_descends (prefixWord ++ tailWord_3701584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3701624 : List Nat := [2, 1, 2, 1, 1, 1, 1, 3, 7, 1, 3]
def baseStart_3701624 : Nat := 118140960795 + 3701624 * 2 ^ 59
def prefixEnd_3701624 : Nat := 4983230072969 + 3 ^ 40 * 3701624 * 2
def baseEnd_3701624 : Nat := 1900712314218530612776547

theorem tailTrace_3701624 : CollatzResearch.WordTrace tailWord_3701624 prefixEnd_3701624 1900712314218530612776547 := by
  unfold tailWord_3701624
  simp only [CollatzResearch.WordTrace]
  refine ⟨67504659370827954946663963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90006212494437273262218617 67504659370827954946663963)
  ·
    refine ⟨101256989056241932419995945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67504659370827954946663963 101256989056241932419995945)
    ·
      refine ⟨75942741792181449314996959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101256989056241932419995945 75942741792181449314996959)
      ·
        refine ⟨113914112688272173972495439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75942741792181449314996959 113914112688272173972495439)
        ·
          refine ⟨170871169032408260958743159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113914112688272173972495439 170871169032408260958743159)
          ·
            refine ⟨256306753548612391438114739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 170871169032408260958743159 256306753548612391438114739)
            ·
              refine ⟨384460130322918587157172109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 256306753548612391438114739 384460130322918587157172109)
              ·
                refine ⟨144172548871094470183939541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 384460130322918587157172109 144172548871094470183939541)
                ·
                  refine ⟨3379044114166276644936083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 144172548871094470183939541 3379044114166276644936083)
                  ·
                    refine ⟨5068566171249414967404125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3379044114166276644936083 5068566171249414967404125)
                    ·
                      refine ⟨1900712314218530612776547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5068566171249414967404125 1900712314218530612776547)
                      ·
                        rfl

theorem cell23_3701624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 3, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 3, 7, 1, 3].length) (baseStart_3701624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3701624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3701624 prefixEnd_3701624 := by exact prefixLift 3701624
  have htrace : WordTrace (prefixWord ++ tailWord_3701624) baseStart_3701624 baseEnd_3701624 := by
    simpa [prefixWord, tailWord_3701624, baseEnd_3701624] using wordTrace_append hprefix tailTrace_3701624
  have hstable : (prefixWord ++ tailWord_3701624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3701624).length < 2 ^ (prefixWord ++ tailWord_3701624).sum := by decide
  have hdescent : baseEnd_3701624 < baseStart_3701624 := by decide
  rcases family_descends (prefixWord ++ tailWord_3701624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3701658 : List Nat := [3, 1, 1, 4, 3, 1, 1, 2, 3, 1, 3]
def baseStart_3701658 : Nat := 118140960795 + 3701658 * 2 ^ 59
def prefixEnd_3701658 : Nat := 4983230072969 + 3 ^ 40 * 3701658 * 2
def baseEnd_3701658 : Nat := 1900729772560783479751391

theorem tailTrace_3701658 : CollatzResearch.WordTrace tailWord_3701658 prefixEnd_3701658 1900729772560783479751391 := by
  unfold tailWord_3701658
  simp only [CollatzResearch.WordTrace]
  refine ⟨33752639705883183425016407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90007039215688489133377085 33752639705883183425016407)
  ·
    refine ⟨50628959558824775137524611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33752639705883183425016407 50628959558824775137524611)
    ·
      refine ⟨75943439338237162706286917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50628959558824775137524611 75943439338237162706286917)
      ·
        refine ⟨14239394875919468007428797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 75943439338237162706286917 14239394875919468007428797)
        ·
          refine ⟨5339773078469800502785799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14239394875919468007428797 5339773078469800502785799)
          ·
            refine ⟨8009659617704700754178699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5339773078469800502785799 8009659617704700754178699)
            ·
              refine ⟨12014489426557051131268049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8009659617704700754178699 12014489426557051131268049)
              ·
                refine ⟨9010867069917788348451037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12014489426557051131268049 9010867069917788348451037)
                ·
                  refine ⟨3379075151219170630669139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9010867069917788348451037 3379075151219170630669139)
                  ·
                    refine ⟨5068612726828755946003709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3379075151219170630669139 5068612726828755946003709)
                    ·
                      refine ⟨1900729772560783479751391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5068612726828755946003709 1900729772560783479751391)
                      ·
                        rfl

theorem cell23_3701658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 1, 1, 2, 3, 1, 3].length) (baseStart_3701658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3701658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3701658 prefixEnd_3701658 := by exact prefixLift 3701658
  have htrace : WordTrace (prefixWord ++ tailWord_3701658) baseStart_3701658 baseEnd_3701658 := by
    simpa [prefixWord, tailWord_3701658, baseEnd_3701658] using wordTrace_append hprefix tailTrace_3701658
  have hstable : (prefixWord ++ tailWord_3701658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3701658).length < 2 ^ (prefixWord ++ tailWord_3701658).sum := by decide
  have hdescent : baseEnd_3701658 < baseStart_3701658 := by decide
  rcases family_descends (prefixWord ++ tailWord_3701658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3701664 : List Nat := [2, 1, 1, 4, 1, 1, 4, 1, 3, 1, 4]
def baseStart_3701664 : Nat := 118140960795 + 3701664 * 2 ^ 59
def prefixEnd_3701664 : Nat := 4983230072969 + 3 ^ 40 * 3701664 * 2
def baseEnd_3701664 : Nat := 1900732853444710456276363

theorem tailTrace_3701664 : CollatzResearch.WordTrace tailWord_3701664 prefixEnd_3701664 1900732853444710456276363 := by
  unfold tailWord_3701664
  simp only [CollatzResearch.WordTrace]
  refine ⟨67505388830755498362392023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90007185107673997816522697 67505388830755498362392023)
  ·
    refine ⟨101258083246133247543588035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67505388830755498362392023 101258083246133247543588035)
    ·
      refine ⟨151887124869199871315382053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101258083246133247543588035 151887124869199871315382053)
      ·
        refine ⟨28478835912974975871634135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 151887124869199871315382053 28478835912974975871634135)
        ·
          refine ⟨42718253869462463807451203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28478835912974975871634135 42718253869462463807451203)
          ·
            refine ⟨64077380804193695711176805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42718253869462463807451203 64077380804193695711176805)
            ·
              refine ⟨12014508900786317945845651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 64077380804193695711176805 12014508900786317945845651)
              ·
                refine ⟨18021763351179476918768477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12014508900786317945845651 18021763351179476918768477)
                ·
                  refine ⟨6758161256692303844538179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18021763351179476918768477 6758161256692303844538179)
                  ·
                    refine ⟨10137241885038455766807269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6758161256692303844538179 10137241885038455766807269)
                    ·
                      refine ⟨1900732853444710456276363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10137241885038455766807269 1900732853444710456276363)
                      ·
                        rfl

theorem cell23_3701664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 4, 1, 3, 1, 4].length) (baseStart_3701664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3701664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3701664 prefixEnd_3701664 := by exact prefixLift 3701664
  have htrace : WordTrace (prefixWord ++ tailWord_3701664) baseStart_3701664 baseEnd_3701664 := by
    simpa [prefixWord, tailWord_3701664, baseEnd_3701664] using wordTrace_append hprefix tailTrace_3701664
  have hstable : (prefixWord ++ tailWord_3701664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3701664).length < 2 ^ (prefixWord ++ tailWord_3701664).sum := by decide
  have hdescent : baseEnd_3701664 < baseStart_3701664 := by decide
  rcases family_descends (prefixWord ++ tailWord_3701664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3701694 : List Nat := [4, 2, 1, 1, 1, 2, 2, 2, 1, 1, 6]
def baseStart_3701694 : Nat := 118140960795 + 3701694 * 2 ^ 59
def prefixEnd_3701694 : Nat := 4983230072969 + 3 ^ 40 * 3701694 * 2
def baseEnd_3701694 : Nat := 1900748257864345338901225

theorem tailTrace_3701694 : CollatzResearch.WordTrace tailWord_3701694 prefixEnd_3701694 1900748257864345338901225 := by
  unfold tailWord_3701694
  simp only [CollatzResearch.WordTrace]
  refine ⟨16876483981425288981047017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 90007914567601541232250757 16876483981425288981047017)
  ·
    refine ⟨12657362986068966735785263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16876483981425288981047017 12657362986068966735785263)
    ·
      refine ⟨18986044479103450103677895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12657362986068966735785263 18986044479103450103677895)
      ·
        refine ⟨28479066718655175155516843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18986044479103450103677895 28479066718655175155516843)
        ·
          refine ⟨42718600077982762733275265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28479066718655175155516843 42718600077982762733275265)
          ·
            refine ⟨32038950058487072049956449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42718600077982762733275265 32038950058487072049956449)
            ·
              refine ⟨24029212543865304037467337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32038950058487072049956449 24029212543865304037467337)
              ·
                refine ⟨18021909407898978028100503, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24029212543865304037467337 18021909407898978028100503)
                ·
                  refine ⟨27032864111848467042150755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18021909407898978028100503 27032864111848467042150755)
                  ·
                    refine ⟨40549296167772700563226133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27032864111848467042150755 40549296167772700563226133)
                    ·
                      refine ⟨1900748257864345338901225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 40549296167772700563226133 1900748257864345338901225)
                      ·
                        rfl

theorem cell23_3701694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 2, 2, 1, 1, 6].length) (baseStart_3701694 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3701694 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3701694 prefixEnd_3701694 := by exact prefixLift 3701694
  have htrace : WordTrace (prefixWord ++ tailWord_3701694) baseStart_3701694 baseEnd_3701694 := by
    simpa [prefixWord, tailWord_3701694, baseEnd_3701694] using wordTrace_append hprefix tailTrace_3701694
  have hstable : (prefixWord ++ tailWord_3701694).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3701694).length < 2 ^ (prefixWord ++ tailWord_3701694).sum := by decide
  have hdescent : baseEnd_3701694 < baseStart_3701694 := by decide
  rcases family_descends (prefixWord ++ tailWord_3701694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3701708 : List Nat := [2, 2, 1, 4, 1, 1, 5, 1, 2, 4]
def baseStart_3701708 : Nat := 118140960795 + 3701708 * 2 ^ 59
def prefixEnd_3701708 : Nat := 4983230072969 + 3 ^ 40 * 3701708 * 2
def baseEnd_3701708 : Nat := 633585148864502761375387

theorem tailTrace_3701708 : CollatzResearch.WordTrace tailWord_3701708 prefixEnd_3701708 633585148864502761375387 := by
  unfold tailWord_3701708
  simp only [CollatzResearch.WordTrace]
  refine ⟨67506191236675796119692889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90008254982234394826257185 67506191236675796119692889)
  ·
    refine ⟨50629643427506847089769667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67506191236675796119692889 50629643427506847089769667)
    ·
      refine ⟨75944465141260270634654501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50629643427506847089769667 75944465141260270634654501)
      ·
        refine ⟨14239587213986300743997719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 75944465141260270634654501 14239587213986300743997719)
        ·
          refine ⟨21359380820979451115996579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14239587213986300743997719 21359380820979451115996579)
          ·
            refine ⟨32039071231469176673994869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21359380820979451115996579 32039071231469176673994869)
            ·
              refine ⟨3003662927950235313187019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 32039071231469176673994869 3003662927950235313187019)
              ·
                refine ⟨4505494391925352969780529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3003662927950235313187019 4505494391925352969780529)
                ·
                  refine ⟨3379120793944014727335397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4505494391925352969780529 3379120793944014727335397)
                  ·
                    refine ⟨633585148864502761375387, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3379120793944014727335397 633585148864502761375387)
                    ·
                      rfl

theorem cell23_3701708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 5, 1, 2, 4].length) (baseStart_3701708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3701708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3701708 prefixEnd_3701708 := by exact prefixLift 3701708
  have htrace : WordTrace (prefixWord ++ tailWord_3701708) baseStart_3701708 baseEnd_3701708 := by
    simpa [prefixWord, tailWord_3701708, baseEnd_3701708] using wordTrace_append hprefix tailTrace_3701708
  have hstable : (prefixWord ++ tailWord_3701708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3701708).length < 2 ^ (prefixWord ++ tailWord_3701708).sum := by decide
  have hdescent : baseEnd_3701708 < baseStart_3701708 := by decide
  rcases family_descends (prefixWord ++ tailWord_3701708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3701711 : List Nat := [1, 1, 2, 1, 1, 8, 1, 1, 1, 2, 4]
def baseStart_3701711 : Nat := 118140960795 + 3701711 * 2 ^ 59
def prefixEnd_3701711 : Nat := 4983230072969 + 3 ^ 40 * 3701711 * 2
def baseEnd_3701711 : Nat := 1900756987035471772388647

theorem tailTrace_3701711 : CollatzResearch.WordTrace tailWord_3701711 prefixEnd_3701711 1900756987035471772388647 := by
  unfold tailWord_3701711
  simp only [CollatzResearch.WordTrace]
  refine ⟨135012491892340723751744987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90008327928227149167829991 135012491892340723751744987)
  ·
    refine ⟨202518737838511085627617481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135012491892340723751744987 202518737838511085627617481)
    ·
      refine ⟨151889053378883314220713111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 202518737838511085627617481 151889053378883314220713111)
      ·
        refine ⟨227833580068324971331069667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151889053378883314220713111 227833580068324971331069667)
        ·
          refine ⟨341750370102487456996604501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 227833580068324971331069667 341750370102487456996604501)
          ·
            refine ⟨4004887149638524886678959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 341750370102487456996604501 4004887149638524886678959)
            ·
              refine ⟨6007330724457787330018439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4004887149638524886678959 6007330724457787330018439)
              ·
                refine ⟨9010996086686680995027659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6007330724457787330018439 9010996086686680995027659)
                ·
                  refine ⟨13516494130030021492541489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9010996086686680995027659 13516494130030021492541489)
                  ·
                    refine ⟨10137370597522516119406117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13516494130030021492541489 10137370597522516119406117)
                    ·
                      refine ⟨1900756987035471772388647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10137370597522516119406117 1900756987035471772388647)
                      ·
                        rfl

theorem cell23_3701711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 8, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 8, 1, 1, 1, 2, 4].length) (baseStart_3701711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3701711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3701711 prefixEnd_3701711 := by exact prefixLift 3701711
  have htrace : WordTrace (prefixWord ++ tailWord_3701711) baseStart_3701711 baseEnd_3701711 := by
    simpa [prefixWord, tailWord_3701711, baseEnd_3701711] using wordTrace_append hprefix tailTrace_3701711
  have hstable : (prefixWord ++ tailWord_3701711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3701711).length < 2 ^ (prefixWord ++ tailWord_3701711).sum := by decide
  have hdescent : baseEnd_3701711 < baseStart_3701711 := by decide
  rcases family_descends (prefixWord ++ tailWord_3701711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3701721 : List Nat := [1, 2, 1, 2, 5, 3, 2, 7]
def baseStart_3701721 : Nat := 118140960795 + 3701721 * 2 ^ 59
def prefixEnd_3701721 : Nat := 4983230072969 + 3 ^ 40 * 3701721 * 2
def baseEnd_3701721 : Nat := 70398597105259879009763

theorem tailTrace_3701721 : CollatzResearch.WordTrace tailWord_3701721 prefixEnd_3701721 70398597105259879009763 := by
  unfold tailWord_3701721
  simp only [CollatzResearch.WordTrace]
  refine ⟨135012856622304495459609017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90008571081536330306406011 135012856622304495459609017)
  ·
    refine ⟨101259642466728371594706763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135012856622304495459609017 101259642466728371594706763)
    ·
      refine ⟨151889463700092557392060145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101259642466728371594706763 151889463700092557392060145)
      ·
        refine ⟨113917097775069418044045109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 151889463700092557392060145 113917097775069418044045109)
        ·
          refine ⟨10679727916412757941629229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 113917097775069418044045109 10679727916412757941629229)
          ·
            refine ⟨4004897968654784228110961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10679727916412757941629229 4004897968654784228110961)
            ·
              refine ⟨3003673476491088171083221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4004897968654784228110961 3003673476491088171083221)
              ·
                refine ⟨70398597105259879009763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3003673476491088171083221 70398597105259879009763)
                ·
                  rfl

theorem cell23_3701721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 3, 2, 7].length) (baseStart_3701721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3701721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3701721 prefixEnd_3701721 := by exact prefixLift 3701721
  have htrace : WordTrace (prefixWord ++ tailWord_3701721) baseStart_3701721 baseEnd_3701721 := by
    simpa [prefixWord, tailWord_3701721, baseEnd_3701721] using wordTrace_append hprefix tailTrace_3701721
  have hstable : (prefixWord ++ tailWord_3701721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3701721).length < 2 ^ (prefixWord ++ tailWord_3701721).sum := by decide
  have hdescent : baseEnd_3701721 < baseStart_3701721 := by decide
  rcases family_descends (prefixWord ++ tailWord_3701721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3701731 : List Nat := [1, 1, 1, 6, 1, 1, 1, 1, 6, 1, 3]
def baseStart_3701731 : Nat := 118140960795 + 3701731 * 2 ^ 59
def prefixEnd_3701731 : Nat := 4983230072969 + 3 ^ 40 * 3701731 * 2
def baseEnd_3701731 : Nat := 1900767256648561694138555

theorem tailTrace_3701731 : CollatzResearch.WordTrace tailWord_3701731 prefixEnd_3701731 1900767256648561694138555 := by
  unfold tailWord_3701731
  simp only [CollatzResearch.WordTrace]
  refine ⟨135013221352268267167473047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90008814234845511444982031 135013221352268267167473047)
  ·
    refine ⟨202519832028402400751209571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135013221352268267167473047 202519832028402400751209571)
    ·
      refine ⟨303779748042603601126814357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 202519832028402400751209571 303779748042603601126814357)
      ·
        refine ⟨14239675689497043802819423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 303779748042603601126814357 14239675689497043802819423)
        ·
          refine ⟨21359513534245565704229135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14239675689497043802819423 21359513534245565704229135)
          ·
            refine ⟨32039270301368348556343703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21359513534245565704229135 32039270301368348556343703)
            ·
              refine ⟨48058905452052522834515555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32039270301368348556343703 48058905452052522834515555)
              ·
                refine ⟨72088358178078784251773333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48058905452052522834515555 72088358178078784251773333)
                ·
                  refine ⟨3379141789597443011801875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 72088358178078784251773333 3379141789597443011801875)
                  ·
                    refine ⟨5068712684396164517702813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3379141789597443011801875 5068712684396164517702813)
                    ·
                      refine ⟨1900767256648561694138555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5068712684396164517702813 1900767256648561694138555)
                      ·
                        rfl

theorem cell23_3701731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 1, 1, 6, 1, 3].length) (baseStart_3701731 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3701731 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3701731 prefixEnd_3701731 := by exact prefixLift 3701731
  have htrace : WordTrace (prefixWord ++ tailWord_3701731) baseStart_3701731 baseEnd_3701731 := by
    simpa [prefixWord, tailWord_3701731, baseEnd_3701731] using wordTrace_append hprefix tailTrace_3701731
  have hstable : (prefixWord ++ tailWord_3701731).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3701731).length < 2 ^ (prefixWord ++ tailWord_3701731).sum := by decide
  have hdescent : baseEnd_3701731 < baseStart_3701731 := by decide
  rcases family_descends (prefixWord ++ tailWord_3701731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3701737 : List Nat := [1, 2, 1, 1, 1, 2, 1, 1, 3, 2, 8]
def baseStart_3701737 : Nat := 118140960795 + 3701737 * 2 ^ 59
def prefixEnd_3701737 : Nat := 4983230072969 + 3 ^ 40 * 3701737 * 2
def baseEnd_3701737 : Nat := 1900770337532488670663527

theorem tailTrace_3701737 : CollatzResearch.WordTrace tailWord_3701737 prefixEnd_3701737 1900770337532488670663527 := by
  unfold tailWord_3701737
  simp only [CollatzResearch.WordTrace]
  refine ⟨135013440190246530192191465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90008960126831020128127643 135013440190246530192191465)
  ·
    refine ⟨101260080142684897644143599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135013440190246530192191465 101260080142684897644143599)
    ·
      refine ⟨151890120214027346466215399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101260080142684897644143599 151890120214027346466215399)
      ·
        refine ⟨227835180321041019699323099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151890120214027346466215399 227835180321041019699323099)
        ·
          refine ⟨341752770481561529548984649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 227835180321041019699323099 341752770481561529548984649)
          ·
            refine ⟨256314577861171147161738487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 341752770481561529548984649 256314577861171147161738487)
            ·
              refine ⟨384471866791756720742607731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 256314577861171147161738487 384471866791756720742607731)
              ·
                refine ⟨576707800187635081113911597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 384471866791756720742607731 576707800187635081113911597)
                ·
                  refine ⟨216265425070363155417716849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 576707800187635081113911597 216265425070363155417716849)
                  ·
                    refine ⟨162199068802772366563287637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 216265425070363155417716849 162199068802772366563287637)
                    ·
                      refine ⟨1900770337532488670663527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 162199068802772366563287637 1900770337532488670663527)
                      ·
                        rfl

theorem cell23_3701737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 1, 3, 2, 8].length) (baseStart_3701737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3701737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3701737 prefixEnd_3701737 := by exact prefixLift 3701737
  have htrace : WordTrace (prefixWord ++ tailWord_3701737) baseStart_3701737 baseEnd_3701737 := by
    simpa [prefixWord, tailWord_3701737, baseEnd_3701737] using wordTrace_append hprefix tailTrace_3701737
  have hstable : (prefixWord ++ tailWord_3701737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3701737).length < 2 ^ (prefixWord ++ tailWord_3701737).sum := by decide
  have hdescent : baseEnd_3701737 < baseStart_3701737 := by decide
  rcases family_descends (prefixWord ++ tailWord_3701737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3701749 : List Nat := [1, 3, 5, 2, 1, 2, 1, 1, 3, 2, 2]
def baseStart_3701749 : Nat := 118140960795 + 3701749 * 2 ^ 59
def prefixEnd_3701749 : Nat := 4983230072969 + 3 ^ 40 * 3701749 * 2
def baseEnd_3701749 : Nat := 1900776499300342623713473

theorem tailTrace_3701749 : CollatzResearch.WordTrace tailWord_3701749 prefixEnd_3701749 1900776499300342623713473 := by
  unfold tailWord_3701749
  simp only [CollatzResearch.WordTrace]
  refine ⟨135013877866203056241628301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90009251910802037494418867 135013877866203056241628301)
  ·
    refine ⟨50630204199826146090610613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 135013877866203056241628301 50630204199826146090610613)
    ·
      refine ⟨4746581643733701195994745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 50630204199826146090610613 4746581643733701195994745)
      ·
        refine ⟨3559936232800275896996059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4746581643733701195994745 3559936232800275896996059)
        ·
          refine ⟨5339904349200413845494089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3559936232800275896996059 5339904349200413845494089)
          ·
            refine ⟨4004928261900310384120567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5339904349200413845494089 4004928261900310384120567)
            ·
              refine ⟨6007392392850465576180851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4004928261900310384120567 6007392392850465576180851)
              ·
                refine ⟨9011088589275698364271277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6007392392850465576180851 9011088589275698364271277)
                ·
                  refine ⟨3379158220978386886601729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9011088589275698364271277 3379158220978386886601729)
                  ·
                    refine ⟨2534368665733790164951297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3379158220978386886601729 2534368665733790164951297)
                    ·
                      refine ⟨1900776499300342623713473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2534368665733790164951297 1900776499300342623713473)
                      ·
                        rfl

theorem cell23_3701749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 2, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 2, 1, 1, 3, 2, 2].length) (baseStart_3701749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3701749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3701749 prefixEnd_3701749 := by exact prefixLift 3701749
  have htrace : WordTrace (prefixWord ++ tailWord_3701749) baseStart_3701749 baseEnd_3701749 := by
    simpa [prefixWord, tailWord_3701749, baseEnd_3701749] using wordTrace_append hprefix tailTrace_3701749
  have hstable : (prefixWord ++ tailWord_3701749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3701749).length < 2 ^ (prefixWord ++ tailWord_3701749).sum := by decide
  have hdescent : baseEnd_3701749 < baseStart_3701749 := by decide
  rcases family_descends (prefixWord ++ tailWord_3701749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3701821 : List Nat := [1, 4, 1, 3, 1, 2, 1, 1, 1, 5, 3]
def baseStart_3701821 : Nat := 118140960795 + 3701821 * 2 ^ 59
def prefixEnd_3701821 : Nat := 4983230072969 + 3 ^ 40 * 3701821 * 2
def baseEnd_3701821 : Nat := 1900813469907466342013141

theorem tailTrace_3701821 : CollatzResearch.WordTrace tailWord_3701821 prefixEnd_3701821 1900813469907466342013141 := by
  unfold tailWord_3701821
  simp only [CollatzResearch.WordTrace]
  refine ⟨135016503921942212538249317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90011002614628141692166211 135016503921942212538249317)
  ·
    refine ⟨25315594485364164850921747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 135016503921942212538249317 25315594485364164850921747)
    ·
      refine ⟨37973391728046247276382621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25315594485364164850921747 37973391728046247276382621)
      ·
        refine ⟨14240021898017342728643483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37973391728046247276382621 14240021898017342728643483)
        ·
          refine ⟨21360032847026014092965225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14240021898017342728643483 21360032847026014092965225)
          ·
            refine ⟨16020024635269510569723919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21360032847026014092965225 16020024635269510569723919)
            ·
              refine ⟨24030036952904265854585879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16020024635269510569723919 24030036952904265854585879)
              ·
                refine ⟨36045055429356398781878819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24030036952904265854585879 36045055429356398781878819)
                ·
                  refine ⟨54067583144034598172818229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36045055429356398781878819 54067583144034598172818229)
                  ·
                    refine ⟨5068835919753243578701709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 54067583144034598172818229 5068835919753243578701709)
                    ·
                      refine ⟨1900813469907466342013141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5068835919753243578701709 1900813469907466342013141)
                      ·
                        rfl

theorem cell23_3701821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 1, 1, 1, 5, 3].length) (baseStart_3701821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3701821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3701821 prefixEnd_3701821 := by exact prefixLift 3701821
  have htrace : WordTrace (prefixWord ++ tailWord_3701821) baseStart_3701821 baseEnd_3701821 := by
    simpa [prefixWord, tailWord_3701821, baseEnd_3701821] using wordTrace_append hprefix tailTrace_3701821
  have hstable : (prefixWord ++ tailWord_3701821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3701821).length < 2 ^ (prefixWord ++ tailWord_3701821).sum := by decide
  have hdescent : baseEnd_3701821 < baseStart_3701821 := by decide
  rcases family_descends (prefixWord ++ tailWord_3701821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3701822 : List Nat := [4, 2, 1, 3, 1, 1, 2, 3, 2, 2, 2]
def baseStart_3701822 : Nat := 118140960795 + 3701822 * 2 ^ 59
def prefixEnd_3701822 : Nat := 4983230072969 + 3 ^ 40 * 3701822 * 2
def baseEnd_3701822 : Nat := 1900813983388120838100637

theorem tailTrace_3701822 : CollatzResearch.WordTrace tailWord_3701822 prefixEnd_3701822 1900813983388120838100637 := by
  unfold tailWord_3701822
  simp only [CollatzResearch.WordTrace]
  refine ⟨16877067549367323713629465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 90011026929959059806023813 16877067549367323713629465)
  ·
    refine ⟨12657800662025492785222099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16877067549367323713629465 12657800662025492785222099)
    ·
      refine ⟨18986700993038239177833149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12657800662025492785222099 18986700993038239177833149)
      ·
        refine ⟨7120012872389339691687431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18986700993038239177833149 7120012872389339691687431)
        ·
          refine ⟨10680019308584009537531147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7120012872389339691687431 10680019308584009537531147)
          ·
            refine ⟨16020028962876014306296721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10680019308584009537531147 16020028962876014306296721)
            ·
              refine ⟨12015021722157010729722541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16020028962876014306296721 12015021722157010729722541)
              ·
                refine ⟨4505633145808879023645953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12015021722157010729722541 4505633145808879023645953)
                ·
                  refine ⟨3379224859356659267734465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4505633145808879023645953 3379224859356659267734465)
                  ·
                    refine ⟨2534418644517494450800849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3379224859356659267734465 2534418644517494450800849)
                    ·
                      refine ⟨1900813983388120838100637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2534418644517494450800849 1900813983388120838100637)
                      ·
                        rfl

theorem cell23_3701822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 2, 3, 2, 2, 2].length) (baseStart_3701822 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3701822 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3701822 prefixEnd_3701822 := by exact prefixLift 3701822
  have htrace : WordTrace (prefixWord ++ tailWord_3701822) baseStart_3701822 baseEnd_3701822 := by
    simpa [prefixWord, tailWord_3701822, baseEnd_3701822] using wordTrace_append hprefix tailTrace_3701822
  have hstable : (prefixWord ++ tailWord_3701822).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3701822).length < 2 ^ (prefixWord ++ tailWord_3701822).sum := by decide
  have hdescent : baseEnd_3701822 < baseStart_3701822 := by decide
  rcases family_descends (prefixWord ++ tailWord_3701822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3701824 : List Nat := [2, 1, 1, 2, 2, 3, 2, 2, 1, 7]
def baseStart_3701824 : Nat := 118140960795 + 3701824 * 2 ^ 59
def prefixEnd_3701824 : Nat := 4983230072969 + 3 ^ 40 * 3701824 * 2
def baseEnd_3701824 : Nat := 633605003449809943425209

theorem tailTrace_3701824 : CollatzResearch.WordTrace tailWord_3701824 prefixEnd_3701824 633605003449809943425209 := by
  unfold tailWord_3701824
  simp only [CollatzResearch.WordTrace]
  refine ⟨67508306670465672025304263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90011075560620896033739017 67508306670465672025304263)
  ·
    refine ⟨101262460005698508037956395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67508306670465672025304263 101262460005698508037956395)
    ·
      refine ⟨151893690008547762056934593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101262460005698508037956395 151893690008547762056934593)
      ·
        refine ⟨113920267506410821542700945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 151893690008547762056934593 113920267506410821542700945)
        ·
          refine ⟨85440200629808116157025709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 113920267506410821542700945 85440200629808116157025709)
          ·
            refine ⟨32040075236178043558884641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 85440200629808116157025709 32040075236178043558884641)
            ·
              refine ⟨24030056427133532669163481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32040075236178043558884641 24030056427133532669163481)
              ·
                refine ⟨18022542320350149501872611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24030056427133532669163481 18022542320350149501872611)
                ·
                  refine ⟨27033813480525224252808917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18022542320350149501872611 27033813480525224252808917)
                  ·
                    refine ⟨633605003449809943425209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 27033813480525224252808917 633605003449809943425209)
                    ·
                      rfl

theorem cell23_3701824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 2, 2, 1, 7].length) (baseStart_3701824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3701824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3701824 prefixEnd_3701824 := by exact prefixLift 3701824
  have htrace : WordTrace (prefixWord ++ tailWord_3701824) baseStart_3701824 baseEnd_3701824 := by
    simpa [prefixWord, tailWord_3701824, baseEnd_3701824] using wordTrace_append hprefix tailTrace_3701824
  have hstable : (prefixWord ++ tailWord_3701824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3701824).length < 2 ^ (prefixWord ++ tailWord_3701824).sum := by decide
  have hdescent : baseEnd_3701824 < baseStart_3701824 := by decide
  rcases family_descends (prefixWord ++ tailWord_3701824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3701834 : List Nat := [3, 1, 2, 1, 1, 2, 2, 2, 1, 1, 7]
def baseStart_3701834 : Nat := 118140960795 + 3701834 * 2 ^ 59
def prefixEnd_3701834 : Nat := 4983230072969 + 3 ^ 40 * 3701834 * 2
def baseEnd_3701834 : Nat := 1900820145155974791150581

theorem tailTrace_3701834 : CollatzResearch.WordTrace tailWord_3701834 prefixEnd_3701834 1900820145155974791150581 := by
  unfold tailWord_3701834
  simp only [CollatzResearch.WordTrace]
  refine ⟨33754244517723778939618139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90011318713930077172315037 33754244517723778939618139)
  ·
    refine ⟨50631366776585668409427209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33754244517723778939618139 50631366776585668409427209)
    ·
      refine ⟨37973525082439251307070407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50631366776585668409427209 37973525082439251307070407)
      ·
        refine ⟨56960287623658876960605611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37973525082439251307070407 56960287623658876960605611)
        ·
          refine ⟨85440431435488315440908417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56960287623658876960605611 85440431435488315440908417)
          ·
            refine ⟨64080323576616236580681313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85440431435488315440908417 64080323576616236580681313)
            ·
              refine ⟨48060242682462177435510985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64080323576616236580681313 48060242682462177435510985)
              ·
                refine ⟨36045182011846633076633239, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48060242682462177435510985 36045182011846633076633239)
                ·
                  refine ⟨54067773017769949614949859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36045182011846633076633239 54067773017769949614949859)
                  ·
                    refine ⟨81101659526654924422424789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 54067773017769949614949859 81101659526654924422424789)
                    ·
                      refine ⟨1900820145155974791150581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 81101659526654924422424789 1900820145155974791150581)
                      ·
                        rfl

theorem cell23_3701834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 2, 2, 1, 1, 7].length) (baseStart_3701834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3701834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3701834 prefixEnd_3701834 := by exact prefixLift 3701834
  have htrace : WordTrace (prefixWord ++ tailWord_3701834) baseStart_3701834 baseEnd_3701834 := by
    simpa [prefixWord, tailWord_3701834, baseEnd_3701834] using wordTrace_append hprefix tailTrace_3701834
  have hstable : (prefixWord ++ tailWord_3701834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3701834).length < 2 ^ (prefixWord ++ tailWord_3701834).sum := by decide
  have hdescent : baseEnd_3701834 < baseStart_3701834 := by decide
  rcases family_descends (prefixWord ++ tailWord_3701834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3701841 : List Nat := [1, 2, 2, 1, 3, 1, 5, 1, 2, 5]
def baseStart_3701841 : Nat := 118140960795 + 3701841 * 2 ^ 59
def prefixEnd_3701841 : Nat := 4983230072969 + 3 ^ 40 * 3701841 * 2
def baseEnd_3701841 : Nat := 633607913173518754587683

theorem tailTrace_3701841 : CollatzResearch.WordTrace tailWord_3701841 prefixEnd_3701841 633607913173518754587683 := by
  unfold tailWord_3701841
  simp only [CollatzResearch.WordTrace]
  refine ⟨135017233381869755953977377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90011488921246503969318251 135017233381869755953977377)
  ·
    refine ⟨101262925036402316965483033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135017233381869755953977377 101262925036402316965483033)
    ·
      refine ⟨75947193777301737724112275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101262925036402316965483033 75947193777301737724112275)
      ·
        refine ⟨113920790665952606586168413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75947193777301737724112275 113920790665952606586168413)
        ·
          refine ⟨42720296499732227469813155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 113920790665952606586168413 42720296499732227469813155)
          ·
            refine ⟨64080444749598341204719733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42720296499732227469813155 64080444749598341204719733)
            ·
              refine ⟨6007541695274844487942475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 64080444749598341204719733 6007541695274844487942475)
              ·
                refine ⟨9011312542912266731913713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6007541695274844487942475 9011312542912266731913713)
                ·
                  refine ⟨6758484407184200048935285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9011312542912266731913713 6758484407184200048935285)
                  ·
                    refine ⟨633607913173518754587683, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6758484407184200048935285 633607913173518754587683)
                    ·
                      rfl

theorem cell23_3701841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 5, 1, 2, 5].length) (baseStart_3701841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3701841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3701841 prefixEnd_3701841 := by exact prefixLift 3701841
  have htrace : WordTrace (prefixWord ++ tailWord_3701841) baseStart_3701841 baseEnd_3701841 := by
    simpa [prefixWord, tailWord_3701841, baseEnd_3701841] using wordTrace_append hprefix tailTrace_3701841
  have hstable : (prefixWord ++ tailWord_3701841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3701841).length < 2 ^ (prefixWord ++ tailWord_3701841).sum := by decide
  have hdescent : baseEnd_3701841 < baseStart_3701841 := by decide
  rcases family_descends (prefixWord ++ tailWord_3701841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3701861 : List Nat := [1, 3, 1, 3, 2, 1, 2, 1, 4, 1, 4]
def baseStart_3701861 : Nat := 118140960795 + 3701861 * 2 ^ 59
def prefixEnd_3701861 : Nat := 4983230072969 + 3 ^ 40 * 3701861 * 2
def baseEnd_3701861 : Nat := 1900834009133646185512957

theorem tailTrace_3701861 : CollatzResearch.WordTrace tailWord_3701861 prefixEnd_3701861 1900834009133646185512957 := by
  unfold tailWord_3701861
  simp only [CollatzResearch.WordTrace]
  refine ⟨135017962841797299369705437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90011975227864866246470291 135017962841797299369705437)
  ·
    refine ⟨50631736065673987263639539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 135017962841797299369705437 50631736065673987263639539)
    ·
      refine ⟨75947604098510980895459309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50631736065673987263639539 75947604098510980895459309)
      ·
        refine ⟨28480351536941617835797241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 75947604098510980895459309 28480351536941617835797241)
        ·
          refine ⟨21360263652706213376847931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28480351536941617835797241 21360263652706213376847931)
          ·
            refine ⟨32040395479059320065271897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21360263652706213376847931 32040395479059320065271897)
            ·
              refine ⟨24030296609294490048953923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32040395479059320065271897 24030296609294490048953923)
              ·
                refine ⟨36045444913941735073430885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24030296609294490048953923 36045444913941735073430885)
                ·
                  refine ⟨6758520921364075326268291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36045444913941735073430885 6758520921364075326268291)
                  ·
                    refine ⟨10137781382046112989402437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6758520921364075326268291 10137781382046112989402437)
                    ·
                      refine ⟨1900834009133646185512957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10137781382046112989402437 1900834009133646185512957)
                      ·
                        rfl

theorem cell23_3701861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 2, 1, 4, 1, 4].length) (baseStart_3701861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3701861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3701861 prefixEnd_3701861 := by exact prefixLift 3701861
  have htrace : WordTrace (prefixWord ++ tailWord_3701861) baseStart_3701861 baseEnd_3701861 := by
    simpa [prefixWord, tailWord_3701861, baseEnd_3701861] using wordTrace_append hprefix tailTrace_3701861
  have hstable : (prefixWord ++ tailWord_3701861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3701861).length < 2 ^ (prefixWord ++ tailWord_3701861).sum := by decide
  have hdescent : baseEnd_3701861 < baseStart_3701861 := by decide
  rcases family_descends (prefixWord ++ tailWord_3701861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3701898 : List Nat := [3, 1, 2, 3, 1, 1, 2, 3, 2, 2, 3]
def baseStart_3701898 : Nat := 118140960795 + 3701898 * 2 ^ 59
def prefixEnd_3701898 : Nat := 4983230072969 + 3 ^ 40 * 3701898 * 2
def baseEnd_3701898 : Nat := 1900853007917862540750287

theorem tailTrace_3701898 : CollatzResearch.WordTrace tailWord_3701898 prefixEnd_3701898 1900853007917862540750287 := by
  unfold tailWord_3701898
  simp only [CollatzResearch.WordTrace]
  refine ⟨33754828085665813672200587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90012874895108836459201565 33754828085665813672200587)
  ·
    refine ⟨50632242128498720508300881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33754828085665813672200587 50632242128498720508300881)
    ·
      refine ⟨37974181596374040381225661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50632242128498720508300881 37974181596374040381225661)
      ·
        refine ⟨14240318098640265142959623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37974181596374040381225661 14240318098640265142959623)
        ·
          refine ⟨21360477147960397714439435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14240318098640265142959623 21360477147960397714439435)
          ·
            refine ⟨32040715721940596571659153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21360477147960397714439435 32040715721940596571659153)
            ·
              refine ⟨24030536791455447428744365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32040715721940596571659153 24030536791455447428744365)
              ·
                refine ⟨9011451296795792785779137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24030536791455447428744365 9011451296795792785779137)
                ·
                  refine ⟨6758588472596844589334353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9011451296795792785779137 6758588472596844589334353)
                  ·
                    refine ⟨5068941354447633442000765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6758588472596844589334353 5068941354447633442000765)
                    ·
                      refine ⟨1900853007917862540750287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5068941354447633442000765 1900853007917862540750287)
                      ·
                        rfl

theorem cell23_3701898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 2, 3, 2, 2, 3].length) (baseStart_3701898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3701898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3701898 prefixEnd_3701898 := by exact prefixLift 3701898
  have htrace : WordTrace (prefixWord ++ tailWord_3701898) baseStart_3701898 baseEnd_3701898 := by
    simpa [prefixWord, tailWord_3701898, baseEnd_3701898] using wordTrace_append hprefix tailTrace_3701898
  have hstable : (prefixWord ++ tailWord_3701898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3701898).length < 2 ^ (prefixWord ++ tailWord_3701898).sum := by decide
  have hdescent : baseEnd_3701898 < baseStart_3701898 := by decide
  rcases family_descends (prefixWord ++ tailWord_3701898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3701904 : List Nat := [2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 8]
def baseStart_3701904 : Nat := 118140960795 + 3701904 * 2 ^ 59
def prefixEnd_3701904 : Nat := 4983230072969 + 3 ^ 40 * 3701904 * 2
def baseEnd_3701904 : Nat := 1900856088801789517275259

theorem tailTrace_3701904 : CollatzResearch.WordTrace tailWord_3701904 prefixEnd_3701904 1900856088801789517275259 := by
  unfold tailWord_3701904
  simp only [CollatzResearch.WordTrace]
  refine ⟨67509765590320758856760383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90013020787094345142347177 67509765590320758856760383)
  ·
    refine ⟨101264648385481138285140575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67509765590320758856760383 101264648385481138285140575)
    ·
      refine ⟨151896972578221707427710863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101264648385481138285140575 151896972578221707427710863)
      ·
        refine ⟨227845458867332561141566295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151896972578221707427710863 227845458867332561141566295)
        ·
          refine ⟨341768188300998841712349443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 227845458867332561141566295 341768188300998841712349443)
          ·
            refine ⟨512652282451498262568524165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 341768188300998841712349443 512652282451498262568524165)
            ·
              refine ⟨96122302959655924231598281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 512652282451498262568524165 96122302959655924231598281)
              ·
                refine ⟨72091727219741943173698711, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 96122302959655924231598281 72091727219741943173698711)
                ·
                  refine ⟨108137590829612914760548067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 72091727219741943173698711 108137590829612914760548067)
                  ·
                    refine ⟨162206386244419372140822101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 108137590829612914760548067 162206386244419372140822101)
                    ·
                      refine ⟨1900856088801789517275259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 162206386244419372140822101 1900856088801789517275259)
                      ·
                        rfl

theorem cell23_3701904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 8].length) (baseStart_3701904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3701904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3701904 prefixEnd_3701904 := by exact prefixLift 3701904
  have htrace : WordTrace (prefixWord ++ tailWord_3701904) baseStart_3701904 baseEnd_3701904 := by
    simpa [prefixWord, tailWord_3701904, baseEnd_3701904] using wordTrace_append hprefix tailTrace_3701904
  have hstable : (prefixWord ++ tailWord_3701904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3701904).length < 2 ^ (prefixWord ++ tailWord_3701904).sum := by decide
  have hdescent : baseEnd_3701904 < baseStart_3701904 := by decide
  rcases family_descends (prefixWord ++ tailWord_3701904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3701918 : List Nat := [4, 3, 1, 1, 2, 1, 2, 1, 8]
def baseStart_3701918 : Nat := 118140960795 + 3701918 * 2 ^ 59
def prefixEnd_3701918 : Nat := 4983230072969 + 3 ^ 40 * 3701918 * 2
def baseEnd_3701918 : Nat := 211207030836772495833355

theorem tailTrace_3701918 : CollatzResearch.WordTrace tailWord_3701918 prefixEnd_3701918 211207030836772495833355 := by
  unfold tailWord_3701918
  simp only [CollatzResearch.WordTrace]
  refine ⟨16877505225323849763066301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 90013361201727198736353605 16877505225323849763066301)
  ·
    refine ⟨6329064459496443661149863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16877505225323849763066301 6329064459496443661149863)
    ·
      refine ⟨9493596689244665491724795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6329064459496443661149863 9493596689244665491724795)
      ·
        refine ⟨14240395033866998237587193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9493596689244665491724795 14240395033866998237587193)
        ·
          refine ⟨10680296275400248678190395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14240395033866998237587193 10680296275400248678190395)
          ·
            refine ⟨16020444413100373017285593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10680296275400248678190395 16020444413100373017285593)
            ·
              refine ⟨12015333309825279762964195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16020444413100373017285593 12015333309825279762964195)
              ·
                refine ⟨18022999964737919644446293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12015333309825279762964195 18022999964737919644446293)
                ·
                  refine ⟨211207030836772495833355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 18022999964737919644446293 211207030836772495833355)
                  ·
                    rfl

theorem cell23_3701918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 2, 1, 8].length) (baseStart_3701918 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3701918 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3701918 prefixEnd_3701918 := by exact prefixLift 3701918
  have htrace : WordTrace (prefixWord ++ tailWord_3701918) baseStart_3701918 baseEnd_3701918 := by
    simpa [prefixWord, tailWord_3701918, baseEnd_3701918] using wordTrace_append hprefix tailTrace_3701918
  have hstable : (prefixWord ++ tailWord_3701918).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3701918).length < 2 ^ (prefixWord ++ tailWord_3701918).sum := by decide
  have hdescent : baseEnd_3701918 < baseStart_3701918 := by decide
  rcases family_descends (prefixWord ++ tailWord_3701918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3701922 : List Nat := [3, 3, 1, 3, 2, 2, 1, 1, 3, 4]
def baseStart_3701922 : Nat := 118140960795 + 3701922 * 2 ^ 59
def prefixEnd_3701922 : Nat := 4983230072969 + 3 ^ 40 * 3701922 * 2
def baseEnd_3701922 : Nat := 633621777151190148950059

theorem tailTrace_3701922 : CollatzResearch.WordTrace tailWord_3701922 prefixEnd_3701922 633621777151190148950059 := by
  unfold tailWord_3701922
  simp only [CollatzResearch.WordTrace]
  refine ⟨33755046923644076696919005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90013458463050871191784013 33755046923644076696919005)
  ·
    refine ⟨12658142596366528761344627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33755046923644076696919005 12658142596366528761344627)
    ·
      refine ⟨18987213894549793142016941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12658142596366528761344627 18987213894549793142016941)
      ·
        refine ⟨7120205210456172428256353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18987213894549793142016941 7120205210456172428256353)
        ·
          refine ⟨5340153907842129321192265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7120205210456172428256353 5340153907842129321192265)
          ·
            refine ⟨4005115430881596990894199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5340153907842129321192265 4005115430881596990894199)
            ·
              refine ⟨6007673146322395486341299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4005115430881596990894199 6007673146322395486341299)
              ·
                refine ⟨9011509719483593229511949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6007673146322395486341299 9011509719483593229511949)
                ·
                  refine ⟨3379316144806347461066981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9011509719483593229511949 3379316144806347461066981)
                  ·
                    refine ⟨633621777151190148950059, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3379316144806347461066981 633621777151190148950059)
                    ·
                      rfl

theorem cell23_3701922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 2, 1, 1, 3, 4].length) (baseStart_3701922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3701922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3701922 prefixEnd_3701922 := by exact prefixLift 3701922
  have htrace : WordTrace (prefixWord ++ tailWord_3701922) baseStart_3701922 baseEnd_3701922 := by
    simpa [prefixWord, tailWord_3701922, baseEnd_3701922] using wordTrace_append hprefix tailTrace_3701922
  have hstable : (prefixWord ++ tailWord_3701922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3701922).length < 2 ^ (prefixWord ++ tailWord_3701922).sum := by decide
  have hdescent : baseEnd_3701922 < baseStart_3701922 := by decide
  rcases family_descends (prefixWord ++ tailWord_3701922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3701948 : List Nat := [2, 2, 2, 3, 2, 2, 1, 1, 3, 5]
def baseStart_3701948 : Nat := 118140960795 + 3701948 * 2 ^ 59
def prefixEnd_3701948 : Nat := 4983230072969 + 3 ^ 40 * 3701948 * 2
def baseEnd_3701948 : Nat := 633626227316862448375019

theorem tailTrace_3701948 : CollatzResearch.WordTrace tailWord_3701948 prefixEnd_3701948 633626227316862448375019 := by
  unfold tailWord_3701948
  simp only [CollatzResearch.WordTrace]
  refine ⟨67510567996241056614061249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90014090661654742152081665 67510567996241056614061249)
  ·
    refine ⟨50632925997180792460545937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67510567996241056614061249 50632925997180792460545937)
    ·
      refine ⟨37974694497885594345409453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50632925997180792460545937 37974694497885594345409453)
      ·
        refine ⟨14240510436707097879528545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37974694497885594345409453 14240510436707097879528545)
        ·
          refine ⟨10680382827530323409646409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14240510436707097879528545 10680382827530323409646409)
          ·
            refine ⟨8010287120647742557234807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10680382827530323409646409 8010287120647742557234807)
            ·
              refine ⟨12015430680971613835852211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8010287120647742557234807 12015430680971613835852211)
              ·
                refine ⟨18023146021457420753778317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12015430680971613835852211 18023146021457420753778317)
                ·
                  refine ⟨6758679758046532782666869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18023146021457420753778317 6758679758046532782666869)
                  ·
                    refine ⟨633626227316862448375019, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6758679758046532782666869 633626227316862448375019)
                    ·
                      rfl

theorem cell23_3701948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 2, 1, 1, 3, 5].length) (baseStart_3701948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3701948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3701948 prefixEnd_3701948 := by exact prefixLift 3701948
  have htrace : WordTrace (prefixWord ++ tailWord_3701948) baseStart_3701948 baseEnd_3701948 := by
    simpa [prefixWord, tailWord_3701948, baseEnd_3701948] using wordTrace_append hprefix tailTrace_3701948
  have hstable : (prefixWord ++ tailWord_3701948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3701948).length < 2 ^ (prefixWord ++ tailWord_3701948).sum := by decide
  have hdescent : baseEnd_3701948 < baseStart_3701948 := by decide
  rcases family_descends (prefixWord ++ tailWord_3701948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3701988 : List Nat := [2, 3, 1, 1, 1, 2, 3, 2, 3, 2, 3]
def baseStart_3701988 : Nat := 118140960795 + 3701988 * 2 ^ 59
def prefixEnd_3701988 : Nat := 4983230072969 + 3 ^ 40 * 3701988 * 2
def baseEnd_3701988 : Nat := 1900899221176767188624873

theorem tailTrace_3701988 : CollatzResearch.WordTrace tailWord_3701988 prefixEnd_3701988 1900899221176767188624873 := by
  unfold tailWord_3701988
  simp only [CollatzResearch.WordTrace]
  refine ⟨67511297456168600029789309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90015063274891466706385745 67511297456168600029789309)
  ·
    refine ⟨25316736546063225011170991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67511297456168600029789309 25316736546063225011170991)
    ·
      refine ⟨37975104819094837516756487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25316736546063225011170991 37975104819094837516756487)
      ·
        refine ⟨56962657228642256275134731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37975104819094837516756487 56962657228642256275134731)
        ·
          refine ⟨85443985842963384412702097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56962657228642256275134731 85443985842963384412702097)
          ·
            refine ⟨64082989382222538309526573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85443985842963384412702097 64082989382222538309526573)
            ·
              refine ⟨24031121018333451866072465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 64082989382222538309526573 24031121018333451866072465)
              ·
                refine ⟨18023340763750088899554349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24031121018333451866072465 18023340763750088899554349)
                ·
                  refine ⟨6758752786406283337332881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18023340763750088899554349 6758752786406283337332881)
                  ·
                    refine ⟨5069064589804712502999661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6758752786406283337332881 5069064589804712502999661)
                    ·
                      refine ⟨1900899221176767188624873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5069064589804712502999661 1900899221176767188624873)
                      ·
                        rfl

theorem cell23_3701988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 3, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 3, 2, 3, 2, 3].length) (baseStart_3701988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3701988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3701988 prefixEnd_3701988 := by exact prefixLift 3701988
  have htrace : WordTrace (prefixWord ++ tailWord_3701988) baseStart_3701988 baseEnd_3701988 := by
    simpa [prefixWord, tailWord_3701988, baseEnd_3701988] using wordTrace_append hprefix tailTrace_3701988
  have hstable : (prefixWord ++ tailWord_3701988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3701988).length < 2 ^ (prefixWord ++ tailWord_3701988).sum := by decide
  have hdescent : baseEnd_3701988 < baseStart_3701988 := by decide
  rcases family_descends (prefixWord ++ tailWord_3701988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3701998 : List Nat := [4, 1, 2, 1, 1, 1, 3, 3, 1, 2, 4]
def baseStart_3701998 : Nat := 118140960795 + 3701998 * 2 ^ 59
def prefixEnd_3701998 : Nat := 4983230072969 + 3 ^ 40 * 3701998 * 2
def baseEnd_3701998 : Nat := 1900904355983312149499827

theorem tailTrace_3701998 : CollatzResearch.WordTrace tailWord_3701998 prefixEnd_3701998 1900904355983312149499827 := by
  unfold tailWord_3701998
  simp only [CollatzResearch.WordTrace]
  refine ⟨16877869955287621470930331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 90015306428200647844961765 16877869955287621470930331)
  ·
    refine ⟨25316804932931432206395497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16877869955287621470930331 25316804932931432206395497)
    ·
      refine ⟨18987603699698574154796623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25316804932931432206395497 18987603699698574154796623)
      ·
        refine ⟨28481405549547861232194935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18987603699698574154796623 28481405549547861232194935)
        ·
          refine ⟨42722108324321791848292403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28481405549547861232194935 42722108324321791848292403)
          ·
            refine ⟨64083162486482687772438605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42722108324321791848292403 64083162486482687772438605)
            ·
              refine ⟨24031185932431007914664477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 64083162486482687772438605 24031185932431007914664477)
              ·
                refine ⟨9011694724661627967999179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24031185932431007914664477 9011694724661627967999179)
                ·
                  refine ⟨13517542086992441951998769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9011694724661627967999179 13517542086992441951998769)
                  ·
                    refine ⟨10138156565244331463999077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13517542086992441951998769 10138156565244331463999077)
                    ·
                      refine ⟨1900904355983312149499827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10138156565244331463999077 1900904355983312149499827)
                      ·
                        rfl

theorem cell23_3701998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 3, 3, 1, 2, 4].length) (baseStart_3701998 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3701998 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3701998 prefixEnd_3701998 := by exact prefixLift 3701998
  have htrace : WordTrace (prefixWord ++ tailWord_3701998) baseStart_3701998 baseEnd_3701998 := by
    simpa [prefixWord, tailWord_3701998, baseEnd_3701998] using wordTrace_append hprefix tailTrace_3701998
  have hstable : (prefixWord ++ tailWord_3701998).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3701998).length < 2 ^ (prefixWord ++ tailWord_3701998).sum := by decide
  have hdescent : baseEnd_3701998 < baseStart_3701998 := by decide
  rcases family_descends (prefixWord ++ tailWord_3701998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3702019 : List Nat := [1, 1, 1, 3, 2, 5, 2, 3, 1, 2, 2]
def baseStart_3702019 : Nat := 118140960795 + 3702019 * 2 ^ 59
def prefixEnd_3702019 : Nat := 4983230072969 + 3 ^ 40 * 3702019 * 2
def baseEnd_3702019 : Nat := 1900915139077056567337231

theorem tailTrace_3702019 : CollatzResearch.WordTrace tailWord_3702019 prefixEnd_3702019 1900915139077056567337231 := by
  unfold tailWord_3702019
  simp only [CollatzResearch.WordTrace]
  refine ⟨135023725575224892353957111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90015817050149928235971407 135023725575224892353957111)
  ·
    refine ⟨202535588362837338530935667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135023725575224892353957111 202535588362837338530935667)
    ·
      refine ⟨303803382544256007796403501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 202535588362837338530935667 303803382544256007796403501)
      ·
        refine ⟨113926268454096002923651313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 303803382544256007796403501 113926268454096002923651313)
        ·
          refine ⟨85444701340572002192738485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 113926268454096002923651313 85444701340572002192738485)
          ·
            refine ⟨8010440750678625205569233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 85444701340572002192738485 8010440750678625205569233)
            ·
              refine ⟨6007830563008968904176925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8010440750678625205569233 6007830563008968904176925)
              ·
                refine ⟨2252936461128363339066347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6007830563008968904176925 2252936461128363339066347)
                ·
                  refine ⟨3379404691692545008599521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2252936461128363339066347 3379404691692545008599521)
                  ·
                    refine ⟨2534553518769408756449641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3379404691692545008599521 2534553518769408756449641)
                    ·
                      refine ⟨1900915139077056567337231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2534553518769408756449641 1900915139077056567337231)
                      ·
                        rfl

theorem cell23_3702019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 5, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 5, 2, 3, 1, 2, 2].length) (baseStart_3702019 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3702019 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3702019 prefixEnd_3702019 := by exact prefixLift 3702019
  have htrace : WordTrace (prefixWord ++ tailWord_3702019) baseStart_3702019 baseEnd_3702019 := by
    simpa [prefixWord, tailWord_3702019, baseEnd_3702019] using wordTrace_append hprefix tailTrace_3702019
  have hstable : (prefixWord ++ tailWord_3702019).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3702019).length < 2 ^ (prefixWord ++ tailWord_3702019).sum := by decide
  have hdescent : baseEnd_3702019 < baseStart_3702019 := by decide
  rcases family_descends (prefixWord ++ tailWord_3702019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3702046 : List Nat := [4, 3, 2, 1, 2, 1, 3, 1, 2, 4]
def baseStart_3702046 : Nat := 118140960795 + 3702046 * 2 ^ 59
def prefixEnd_3702046 : Nat := 4983230072969 + 3 ^ 40 * 3702046 * 2
def baseEnd_3702046 : Nat := 633643001018242653899869

theorem tailTrace_3702046 : CollatzResearch.WordTrace tailWord_3702046 prefixEnd_3702046 633643001018242653899869 := by
  unfold tailWord_3702046
  simp only [CollatzResearch.WordTrace]
  refine ⟨16878088793265884495648749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 90016473564084717310126661 16878088793265884495648749)
  ·
    refine ⟨6329283297474706685868281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16878088793265884495648749 6329283297474706685868281)
    ·
      refine ⟨4746962473106030014401211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6329283297474706685868281 4746962473106030014401211)
      ·
        refine ⟨7120443709659045021601817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4746962473106030014401211 7120443709659045021601817)
        ·
          refine ⟨5340332782244283766201363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7120443709659045021601817 5340332782244283766201363)
          ·
            refine ⟨8010499173366425649302045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5340332782244283766201363 8010499173366425649302045)
            ·
              refine ⟨3003937190012409618488267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8010499173366425649302045 3003937190012409618488267)
              ·
                refine ⟨4505905785018614427732401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3003937190012409618488267 4505905785018614427732401)
                ·
                  refine ⟨3379429338763960820799301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4505905785018614427732401 3379429338763960820799301)
                  ·
                    refine ⟨633643001018242653899869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3379429338763960820799301 633643001018242653899869)
                    ·
                      rfl

theorem cell23_3702046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 1, 3, 1, 2, 4].length) (baseStart_3702046 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3702046 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3702046 prefixEnd_3702046 := by exact prefixLift 3702046
  have htrace : WordTrace (prefixWord ++ tailWord_3702046) baseStart_3702046 baseEnd_3702046 := by
    simpa [prefixWord, tailWord_3702046, baseEnd_3702046] using wordTrace_append hprefix tailTrace_3702046
  have hstable : (prefixWord ++ tailWord_3702046).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3702046).length < 2 ^ (prefixWord ++ tailWord_3702046).sum := by decide
  have hdescent : baseEnd_3702046 < baseStart_3702046 := by decide
  rcases family_descends (prefixWord ++ tailWord_3702046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3702070 : List Nat := [5, 1, 2, 3, 1, 2, 1, 3, 1, 2, 2]
def baseStart_3702070 : Nat := 118140960795 + 3702070 * 2 ^ 59
def prefixEnd_3702070 : Nat := 4983230072969 + 3 ^ 40 * 3702070 * 2
def baseEnd_3702070 : Nat := 1900941326590435867799497

theorem tailTrace_3702070 : CollatzResearch.WordTrace tailWord_3702070 prefixEnd_3702070 1900941326590435867799497 := by
  unfold tailWord_3702070
  simp only [CollatzResearch.WordTrace]
  refine ⟨8439099106127508004003979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 90017057132026752042709109 8439099106127508004003979)
  ·
    refine ⟨12658648659191262006005969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8439099106127508004003979 12658648659191262006005969)
    ·
      refine ⟨9493986494393446504504477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12658648659191262006005969 9493986494393446504504477)
      ·
        refine ⟨3560244935397542439189179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9493986494393446504504477 3560244935397542439189179)
        ·
          refine ⟨5340367403096313658783769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3560244935397542439189179 5340367403096313658783769)
          ·
            refine ⟨4005275552322235244087827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5340367403096313658783769 4005275552322235244087827)
            ·
              refine ⟨6007913328483352866131741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4005275552322235244087827 6007913328483352866131741)
              ·
                refine ⟨2252967498181257324799403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6007913328483352866131741 2252967498181257324799403)
                ·
                  refine ⟨3379451247271885987199105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2252967498181257324799403 3379451247271885987199105)
                  ·
                    refine ⟨2534588435453914490399329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3379451247271885987199105 2534588435453914490399329)
                    ·
                      refine ⟨1900941326590435867799497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2534588435453914490399329 1900941326590435867799497)
                      ·
                        rfl

theorem cell23_3702070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 2, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 2, 1, 3, 1, 2, 2].length) (baseStart_3702070 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3702070 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3702070 prefixEnd_3702070 := by exact prefixLift 3702070
  have htrace : WordTrace (prefixWord ++ tailWord_3702070) baseStart_3702070 baseEnd_3702070 := by
    simpa [prefixWord, tailWord_3702070, baseEnd_3702070] using wordTrace_append hprefix tailTrace_3702070
  have hstable : (prefixWord ++ tailWord_3702070).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3702070).length < 2 ^ (prefixWord ++ tailWord_3702070).sum := by decide
  have hdescent : baseEnd_3702070 < baseStart_3702070 := by decide
  rcases family_descends (prefixWord ++ tailWord_3702070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3702092 : List Nat := [2, 2, 1, 3, 2, 2, 2, 1, 4, 2, 2]
def baseStart_3702092 : Nat := 118140960795 + 3702092 * 2 ^ 59
def prefixEnd_3702092 : Nat := 4983230072969 + 3 ^ 40 * 3702092 * 2
def baseEnd_3702092 : Nat := 1900952623164834781724395

theorem tailTrace_3702092 : CollatzResearch.WordTrace tailWord_3702092 prefixEnd_3702092 1900952623164834781724395 := by
  unfold tailWord_3702092
  simp only [CollatzResearch.WordTrace]
  refine ⟨67513194051980212910682265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90017592069306950547576353 67513194051980212910682265)
  ·
    refine ⟨50634895538985159683011699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67513194051980212910682265 50634895538985159683011699)
    ·
      refine ⟨75952343308477739524517549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50634895538985159683011699 75952343308477739524517549)
      ·
        refine ⟨28482128740679152321694081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 75952343308477739524517549 28482128740679152321694081)
        ·
          refine ⟨21361596555509364241270561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28482128740679152321694081 21361596555509364241270561)
          ·
            refine ⟨16021197416632023180952921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21361596555509364241270561 16021197416632023180952921)
            ·
              refine ⟨12015898062474017385714691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16021197416632023180952921 12015898062474017385714691)
              ·
                refine ⟨18023847093711026078572037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12015898062474017385714691 18023847093711026078572037)
                ·
                  refine ⟨3379471330070817389732257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18023847093711026078572037 3379471330070817389732257)
                  ·
                    refine ⟨2534603497553113042299193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3379471330070817389732257 2534603497553113042299193)
                    ·
                      refine ⟨1900952623164834781724395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2534603497553113042299193 1900952623164834781724395)
                      ·
                        rfl

theorem cell23_3702092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 2, 1, 4, 2, 2].length) (baseStart_3702092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3702092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3702092 prefixEnd_3702092 := by exact prefixLift 3702092
  have htrace : WordTrace (prefixWord ++ tailWord_3702092) baseStart_3702092 baseEnd_3702092 := by
    simpa [prefixWord, tailWord_3702092, baseEnd_3702092] using wordTrace_append hprefix tailTrace_3702092
  have hstable : (prefixWord ++ tailWord_3702092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3702092).length < 2 ^ (prefixWord ++ tailWord_3702092).sum := by decide
  have hdescent : baseEnd_3702092 < baseStart_3702092 := by decide
  rcases family_descends (prefixWord ++ tailWord_3702092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3702165 : List Nat := [1, 3, 2, 1, 1, 2, 3, 1, 1, 6, 2]
def baseStart_3702165 : Nat := 118140960795 + 3702165 * 2 ^ 59
def prefixEnd_3702165 : Nat := 4983230072969 + 3 ^ 40 * 3702165 * 2
def baseEnd_3702165 : Nat := 1900990107252612996111559

theorem tailTrace_3702165 : CollatzResearch.WordTrace tailWord_3702165 prefixEnd_3702165 1900990107252612996111559 := by
  unfold tailWord_3702165
  simp only [CollatzResearch.WordTrace]
  refine ⟨135029050632695959288771949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90019367088463972859181299 135029050632695959288771949)
  ·
    refine ⟨50635893987260984733289481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 135029050632695959288771949 50635893987260984733289481)
    ·
      refine ⟨37976920490445738549967111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50635893987260984733289481 37976920490445738549967111)
      ·
        refine ⟨56965380735668607824950667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37976920490445738549967111 56965380735668607824950667)
        ·
          refine ⟨85448071103502911737426001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56965380735668607824950667 85448071103502911737426001)
          ·
            refine ⟨64086053327627183803069501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85448071103502911737426001 64086053327627183803069501)
            ·
              refine ⟨24032269997860193926151063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 64086053327627183803069501 24032269997860193926151063)
              ·
                refine ⟨36048404996790290889226595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24032269997860193926151063 36048404996790290889226595)
                ·
                  refine ⟨54072607495185436333839893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36048404996790290889226595 54072607495185436333839893)
                  ·
                    refine ⟨2534653476336817328148745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 54072607495185436333839893 2534653476336817328148745)
                    ·
                      refine ⟨1900990107252612996111559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2534653476336817328148745 1900990107252612996111559)
                      ·
                        rfl

theorem cell23_3702165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 3, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 3, 1, 1, 6, 2].length) (baseStart_3702165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3702165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3702165 prefixEnd_3702165 := by exact prefixLift 3702165
  have htrace : WordTrace (prefixWord ++ tailWord_3702165) baseStart_3702165 baseEnd_3702165 := by
    simpa [prefixWord, tailWord_3702165, baseEnd_3702165] using wordTrace_append hprefix tailTrace_3702165
  have hstable : (prefixWord ++ tailWord_3702165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3702165).length < 2 ^ (prefixWord ++ tailWord_3702165).sum := by decide
  have hdescent : baseEnd_3702165 < baseStart_3702165 := by decide
  rcases family_descends (prefixWord ++ tailWord_3702165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3702175 : List Nat := [1, 1, 2, 5, 1, 2, 1, 1, 5, 4]
def baseStart_3702175 : Nat := 118140960795 + 3702175 * 2 ^ 59
def prefixEnd_3702175 : Nat := 4983230072969 + 3 ^ 40 * 3702175 * 2
def baseEnd_3702175 : Nat := 633665080686385985662171

theorem tailTrace_3702175 : CollatzResearch.WordTrace tailWord_3702175 prefixEnd_3702175 633665080686385985662171 := by
  unfold tailWord_3702175
  simp only [CollatzResearch.WordTrace]
  refine ⟨135029415362659730996635979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90019610241773153997757319 135029415362659730996635979)
  ·
    refine ⟨202544123043989596494953969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135029415362659730996635979 202544123043989596494953969)
    ·
      refine ⟨151908092282992197371215477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 202544123043989596494953969 151908092282992197371215477)
      ·
        refine ⟨14241383651530518503551451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 151908092282992197371215477 14241383651530518503551451)
        ·
          refine ⟨21362075477295777755327177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14241383651530518503551451 21362075477295777755327177)
          ·
            refine ⟨16021556607971833316495383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21362075477295777755327177 16021556607971833316495383)
            ·
              refine ⟨24032334911957749974743075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16021556607971833316495383 24032334911957749974743075)
              ·
                refine ⟨36048502367936624962114613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24032334911957749974743075 36048502367936624962114613)
                ·
                  refine ⟨3379547096994058590198245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 36048502367936624962114613 3379547096994058590198245)
                  ·
                    refine ⟨633665080686385985662171, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3379547096994058590198245 633665080686385985662171)
                    ·
                      rfl

theorem cell23_3702175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 1, 1, 5, 4].length) (baseStart_3702175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3702175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3702175 prefixEnd_3702175 := by exact prefixLift 3702175
  have htrace : WordTrace (prefixWord ++ tailWord_3702175) baseStart_3702175 baseEnd_3702175 := by
    simpa [prefixWord, tailWord_3702175, baseEnd_3702175] using wordTrace_append hprefix tailTrace_3702175
  have hstable : (prefixWord ++ tailWord_3702175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3702175).length < 2 ^ (prefixWord ++ tailWord_3702175).sum := by decide
  have hdescent : baseEnd_3702175 < baseStart_3702175 := by decide
  rcases family_descends (prefixWord ++ tailWord_3702175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3702208 : List Nat := [2, 1, 1, 2, 3, 1, 3, 1, 1, 2, 6]
def baseStart_3702208 : Nat := 118140960795 + 3702208 * 2 ^ 59
def prefixEnd_3702208 : Nat := 4983230072969 + 3 ^ 40 * 3702208 * 2
def baseEnd_3702208 : Nat := 1901012186920756327873861

theorem tailTrace_3702208 : CollatzResearch.WordTrace tailWord_3702208 prefixEnd_3702208 1901012186920756327873861 := by
  unfold tailWord_3702208
  simp only [CollatzResearch.WordTrace]
  refine ⟨67515309485770088816293639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90020412647693451755058185 67515309485770088816293639)
  ·
    refine ⟨101272964228655133224440459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67515309485770088816293639 101272964228655133224440459)
    ·
      refine ⟨151909446342982699836660689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101272964228655133224440459 151909446342982699836660689)
      ·
        refine ⟨113932084757237024877495517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 151909446342982699836660689 113932084757237024877495517)
        ·
          refine ⟨42724531783963884329060819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 113932084757237024877495517 42724531783963884329060819)
          ·
            refine ⟨64086797675945826493591229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42724531783963884329060819 64086797675945826493591229)
            ·
              refine ⟨24032549128479684935096711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 64086797675945826493591229 24032549128479684935096711)
              ·
                refine ⟨36048823692719527402645067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24032549128479684935096711 36048823692719527402645067)
                ·
                  refine ⟨54073235539079291103967601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36048823692719527402645067 54073235539079291103967601)
                  ·
                    refine ⟨40554926654309468327975701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 54073235539079291103967601 40554926654309468327975701)
                    ·
                      refine ⟨1901012186920756327873861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 40554926654309468327975701 1901012186920756327873861)
                      ·
                        rfl

theorem cell23_3702208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 3, 1, 1, 2, 6].length) (baseStart_3702208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3702208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3702208 prefixEnd_3702208 := by exact prefixLift 3702208
  have htrace : WordTrace (prefixWord ++ tailWord_3702208) baseStart_3702208 baseEnd_3702208 := by
    simpa [prefixWord, tailWord_3702208, baseEnd_3702208] using wordTrace_append hprefix tailTrace_3702208
  have hstable : (prefixWord ++ tailWord_3702208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3702208).length < 2 ^ (prefixWord ++ tailWord_3702208).sum := by decide
  have hdescent : baseEnd_3702208 < baseStart_3702208 := by decide
  rcases family_descends (prefixWord ++ tailWord_3702208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3702232 : List Nat := [2, 1, 2, 2, 2, 1, 4, 2, 3, 1, 3]
def baseStart_3702232 : Nat := 118140960795 + 3702232 * 2 ^ 59
def prefixEnd_3702232 : Nat := 4983230072969 + 3 ^ 40 * 3702232 * 2
def baseEnd_3702232 : Nat := 1901024510456464233973751

theorem tailTrace_3702232 : CollatzResearch.WordTrace tailWord_3702232 prefixEnd_3702232 1901024510456464233973751 := by
  unfold tailWord_3702232
  simp only [CollatzResearch.WordTrace]
  refine ⟨67515747161726614865730475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90020996215635486487640633 67515747161726614865730475)
  ·
    refine ⟨101273620742589922298595713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67515747161726614865730475 101273620742589922298595713)
    ·
      refine ⟨75955215556942441723946785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101273620742589922298595713 75955215556942441723946785)
      ·
        refine ⟨56966411667706831292960089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75955215556942441723946785 56966411667706831292960089)
        ·
          refine ⟨42724808750780123469720067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56966411667706831292960089 42724808750780123469720067)
          ·
            refine ⟨64087213126170185204580101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42724808750780123469720067 64087213126170185204580101)
            ·
              refine ⟨12016352461156909725858769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 64087213126170185204580101 12016352461156909725858769)
              ·
                refine ⟨9012264345867682294394077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12016352461156909725858769 9012264345867682294394077)
                ·
                  refine ⟨3379599129700380860397779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9012264345867682294394077 3379599129700380860397779)
                  ·
                    refine ⟨5069398694550571290596669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3379599129700380860397779 5069398694550571290596669)
                    ·
                      refine ⟨1901024510456464233973751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5069398694550571290596669 1901024510456464233973751)
                      ·
                        rfl

theorem cell23_3702232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 4, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 4, 2, 3, 1, 3].length) (baseStart_3702232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3702232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3702232 prefixEnd_3702232 := by exact prefixLift 3702232
  have htrace : WordTrace (prefixWord ++ tailWord_3702232) baseStart_3702232 baseEnd_3702232 := by
    simpa [prefixWord, tailWord_3702232, baseEnd_3702232] using wordTrace_append hprefix tailTrace_3702232
  have hstable : (prefixWord ++ tailWord_3702232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3702232).length < 2 ^ (prefixWord ++ tailWord_3702232).sum := by decide
  have hdescent : baseEnd_3702232 < baseStart_3702232 := by decide
  rcases family_descends (prefixWord ++ tailWord_3702232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3702266 : List Nat := [3, 1, 1, 1, 1, 2, 7, 2, 1, 1, 3]
def baseStart_3702266 : Nat := 118140960795 + 3702266 * 2 ^ 59
def prefixEnd_3702266 : Nat := 4983230072969 + 3 ^ 40 * 3702266 * 2
def baseEnd_3702266 : Nat := 1901041968798717100948595

theorem tailTrace_3702266 : CollatzResearch.WordTrace tailWord_3702266 prefixEnd_3702266 1901041968798717100948595 := by
  unfold tailWord_3702266
  simp only [CollatzResearch.WordTrace]
  refine ⟨33758183601332513384549663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90021822936886702358799101 33758183601332513384549663)
  ·
    refine ⟨50637275401998770076824495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33758183601332513384549663 50637275401998770076824495)
    ·
      refine ⟨75955913102998155115236743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50637275401998770076824495 75955913102998155115236743)
      ·
        refine ⟨113933869654497232672855115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75955913102998155115236743 113933869654497232672855115)
        ·
          refine ⟨170900804481745849009282673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113933869654497232672855115 170900804481745849009282673)
          ·
            refine ⟨128175603361309386756962005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 170900804481745849009282673 128175603361309386756962005)
            ·
              refine ⟨3004115703780688752116297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 128175603361309386756962005 3004115703780688752116297)
              ·
                refine ⟨2253086777835516564087223, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3004115703780688752116297 2253086777835516564087223)
                ·
                  refine ⟨3379630166753274846130835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2253086777835516564087223 3379630166753274846130835)
                  ·
                    refine ⟨5069445250129912269196253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3379630166753274846130835 5069445250129912269196253)
                    ·
                      refine ⟨1901041968798717100948595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5069445250129912269196253 1901041968798717100948595)
                      ·
                        rfl

theorem cell23_3702266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 7, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 7, 2, 1, 1, 3].length) (baseStart_3702266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3702266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3702266 prefixEnd_3702266 := by exact prefixLift 3702266
  have htrace : WordTrace (prefixWord ++ tailWord_3702266) baseStart_3702266 baseEnd_3702266 := by
    simpa [prefixWord, tailWord_3702266, baseEnd_3702266] using wordTrace_append hprefix tailTrace_3702266
  have hstable : (prefixWord ++ tailWord_3702266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3702266).length < 2 ^ (prefixWord ++ tailWord_3702266).sum := by decide
  have hdescent : baseEnd_3702266 < baseStart_3702266 := by decide
  rcases family_descends (prefixWord ++ tailWord_3702266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3702286 : List Nat := [4, 1, 1, 2, 5, 1, 1, 2, 1, 5]
def baseStart_3702286 : Nat := 118140960795 + 3702286 * 2 ^ 59
def prefixEnd_3702286 : Nat := 4983230072969 + 3 ^ 40 * 3702286 * 2
def baseEnd_3702286 : Nat := 633684079470602340899501

theorem tailTrace_3702286 : CollatzResearch.WordTrace tailWord_3702286 prefixEnd_3702286 633684079470602340899501 := by
  unfold tailWord_3702286
  simp only [CollatzResearch.WordTrace]
  refine ⟨16879182983157199619240839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 90022309243505064635951141 16879182983157199619240839)
  ·
    refine ⟨25318774474735799428861259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16879182983157199619240839 25318774474735799428861259)
    ·
      refine ⟨37978161712103699143291889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25318774474735799428861259 37978161712103699143291889)
      ·
        refine ⟨28483621284077774357468917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37978161712103699143291889 28483621284077774357468917)
        ·
          refine ⟨2670339495382291346012711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 28483621284077774357468917 2670339495382291346012711)
          ·
            refine ⟨4005509243073437019019067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2670339495382291346012711 4005509243073437019019067)
            ·
              refine ⟨6008263864610155528528601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4005509243073437019019067 6008263864610155528528601)
              ·
                refine ⟨4506197898457616646396451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6008263864610155528528601 4506197898457616646396451)
                ·
                  refine ⟨6759296847686424969594677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4506197898457616646396451 6759296847686424969594677)
                  ·
                    refine ⟨633684079470602340899501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6759296847686424969594677 633684079470602340899501)
                    ·
                      rfl

theorem cell23_3702286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 5, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 5, 1, 1, 2, 1, 5].length) (baseStart_3702286 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3702286 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3702286 prefixEnd_3702286 := by exact prefixLift 3702286
  have htrace : WordTrace (prefixWord ++ tailWord_3702286) baseStart_3702286 baseEnd_3702286 := by
    simpa [prefixWord, tailWord_3702286, baseEnd_3702286] using wordTrace_append hprefix tailTrace_3702286
  have hstable : (prefixWord ++ tailWord_3702286).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3702286).length < 2 ^ (prefixWord ++ tailWord_3702286).sum := by decide
  have hdescent : baseEnd_3702286 < baseStart_3702286 := by decide
  rcases family_descends (prefixWord ++ tailWord_3702286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3702312 : List Nat := [2, 1, 5, 2, 3, 10]
def baseStart_3702312 : Nat := 118140960795 + 3702312 * 2 ^ 59
def prefixEnd_3702312 : Nat := 4983230072969 + 3 ^ 40 * 3702312 * 2
def baseEnd_3702312 : Nat := 7823315180694748645981

theorem tailTrace_3702312 : CollatzResearch.WordTrace tailWord_3702312 prefixEnd_3702312 7823315180694748645981 := by
  unfold tailWord_3702312
  simp only [CollatzResearch.WordTrace]
  refine ⟨67517206081581701697186595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90022941442108935596248793 67517206081581701697186595)
  ·
    refine ⟨101275809122372552545779893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67517206081581701697186595 101275809122372552545779893)
    ·
      refine ⟨9494607105222426801166865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 101275809122372552545779893 9494607105222426801166865)
      ·
        refine ⟨7120955328916820100875149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9494607105222426801166865 7120955328916820100875149)
        ·
          refine ⟨2670358248343807537828181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7120955328916820100875149 2670358248343807537828181)
          ·
            refine ⟨7823315180694748645981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 2670358248343807537828181 7823315180694748645981)
            ·
              rfl

theorem cell23_3702312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 3, 10].length) (baseStart_3702312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3702312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3702312 prefixEnd_3702312 := by exact prefixLift 3702312
  have htrace : WordTrace (prefixWord ++ tailWord_3702312) baseStart_3702312 baseEnd_3702312 := by
    simpa [prefixWord, tailWord_3702312, baseEnd_3702312] using wordTrace_append hprefix tailTrace_3702312
  have hstable : (prefixWord ++ tailWord_3702312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3702312).length < 2 ^ (prefixWord ++ tailWord_3702312).sum := by decide
  have hdescent : baseEnd_3702312 < baseStart_3702312 := by decide
  rcases family_descends (prefixWord ++ tailWord_3702312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
