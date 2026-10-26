import V185TrunkScan23Chunk1366

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_8096562 : List Nat := [3, 2, 1, 1, 3, 1, 1, 3, 3, 1, 4]
def baseStart_8096562 : Nat := 118140960795 + 8096562 * 2 ^ 59
def prefixEnd_8096562 : Nat := 4983230072969 + 3 ^ 40 * 8096562 * 2
def baseEnd_8096562 : Nat := 4157427954928256397639595

theorem tailTrace_8096562 : CollatzResearch.WordTrace tailWord_8096562 prefixEnd_8096562 4157427954928256397639595 := by
  unfold tailWord_8096562
  simp only [CollatzResearch.WordTrace]
  refine ⟨73826469123386532886438985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 196870584329030754363837293 73826469123386532886438985)
  ·
    refine ⟨55369851842539899664829239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73826469123386532886438985 55369851842539899664829239)
    ·
      refine ⟨83054777763809849497243859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55369851842539899664829239 83054777763809849497243859)
      ·
        refine ⟨124582166645714774245865789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83054777763809849497243859 124582166645714774245865789)
        ·
          refine ⟨46718312492143040342199671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 124582166645714774245865789 46718312492143040342199671)
          ·
            refine ⟨70077468738214560513299507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46718312492143040342199671 70077468738214560513299507)
            ·
              refine ⟨105116203107321840769949261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70077468738214560513299507 105116203107321840769949261)
              ·
                refine ⟨39418576165245690288730973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 105116203107321840769949261 39418576165245690288730973)
                ·
                  refine ⟨14781966061967133858274115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39418576165245690288730973 14781966061967133858274115)
                  ·
                    refine ⟨22172949092950700787411173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14781966061967133858274115 22172949092950700787411173)
                    ·
                      refine ⟨4157427954928256397639595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22172949092950700787411173 4157427954928256397639595)
                      ·
                        rfl

theorem cell23_8096562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 1, 3, 3, 1, 4].length) (baseStart_8096562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8096562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8096562 prefixEnd_8096562 := by exact prefixLift 8096562
  have htrace : WordTrace (prefixWord ++ tailWord_8096562) baseStart_8096562 baseEnd_8096562 := by
    simpa [prefixWord, tailWord_8096562, baseEnd_8096562] using wordTrace_append hprefix tailTrace_8096562
  have hstable : (prefixWord ++ tailWord_8096562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8096562).length < 2 ^ (prefixWord ++ tailWord_8096562).sum := by decide
  have hdescent : baseEnd_8096562 < baseStart_8096562 := by decide
  rcases family_descends (prefixWord ++ tailWord_8096562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8096572 : List Nat := [2, 2, 2, 2, 1, 1, 1, 4, 4, 4]
def baseStart_8096572 : Nat := 118140960795 + 8096572 * 2 ^ 59
def prefixEnd_8096572 : Nat := 4983230072969 + 3 ^ 40 * 8096572 * 2
def baseEnd_8096572 : Nat := 1385811029911600452838183

theorem tailTrace_8096572 : CollatzResearch.WordTrace tailWord_8096572 prefixEnd_8096572 1385811029911600452838183 := by
  unfold tailWord_8096572
  simp only [CollatzResearch.WordTrace]
  refine ⟨147653120611754951626809985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196870827482339935502413313 147653120611754951626809985)
  ·
    refine ⟨110739840458816213720107489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147653120611754951626809985 110739840458816213720107489)
    ·
      refine ⟨83054880344112160290080617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110739840458816213720107489 83054880344112160290080617)
      ·
        refine ⟨62291160258084120217560463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83054880344112160290080617 62291160258084120217560463)
        ·
          refine ⟨93436740387126180326340695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62291160258084120217560463 93436740387126180326340695)
          ·
            refine ⟨140155110580689270489511043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93436740387126180326340695 140155110580689270489511043)
            ·
              refine ⟨210232665871033905734266565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 140155110580689270489511043 210232665871033905734266565)
              ·
                refine ⟨39418624850818857325174981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 210232665871033905734266565 39418624850818857325174981)
                ·
                  refine ⟨7390992159528535748470309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39418624850818857325174981 7390992159528535748470309)
                  ·
                    refine ⟨1385811029911600452838183, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7390992159528535748470309 1385811029911600452838183)
                    ·
                      rfl

theorem cell23_8096572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 4, 4, 4].length) (baseStart_8096572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8096572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8096572 prefixEnd_8096572 := by exact prefixLift 8096572
  have htrace : WordTrace (prefixWord ++ tailWord_8096572) baseStart_8096572 baseEnd_8096572 := by
    simpa [prefixWord, tailWord_8096572, baseEnd_8096572] using wordTrace_append hprefix tailTrace_8096572
  have hstable : (prefixWord ++ tailWord_8096572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8096572).length < 2 ^ (prefixWord ++ tailWord_8096572).sum := by decide
  have hdescent : baseEnd_8096572 < baseStart_8096572 := by decide
  rcases family_descends (prefixWord ++ tailWord_8096572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8096579 : List Nat := [1, 1, 1, 3, 1, 4, 1, 2, 5, 2, 2]
def baseStart_8096579 : Nat := 118140960795 + 8096579 * 2 ^ 59
def prefixEnd_8096579 : Nat := 4983230072969 + 3 ^ 40 * 8096579 * 2
def baseEnd_8096579 : Nat := 4157436684099382831127017

theorem tailTrace_8096579 : CollatzResearch.WordTrace tailWord_8096579 prefixEnd_8096579 4157436684099382831127017 := by
  unfold tailWord_8096579
  simp only [CollatzResearch.WordTrace]
  refine ⟨295306496534484543449124791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196870997689656362299416527 295306496534484543449124791)
  ·
    refine ⟨442959744801726815173687187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 295306496534484543449124791 442959744801726815173687187)
    ·
      refine ⟨664439617202590222760530781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 442959744801726815173687187 664439617202590222760530781)
      ·
        refine ⟨249164856450971333535199043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 664439617202590222760530781 249164856450971333535199043)
        ·
          refine ⟨373747284676457000302798565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 249164856450971333535199043 373747284676457000302798565)
          ·
            refine ⟨70077615876835687556774731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 373747284676457000302798565 70077615876835687556774731)
            ·
              refine ⟨105116423815253531335162097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70077615876835687556774731 105116423815253531335162097)
              ·
                refine ⟨78837317861440148501371573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 105116423815253531335162097 78837317861440148501371573)
                ·
                  refine ⟨7390998549510013922003585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 78837317861440148501371573 7390998549510013922003585)
                  ·
                    refine ⟨5543248912132510441502689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7390998549510013922003585 5543248912132510441502689)
                    ·
                      refine ⟨4157436684099382831127017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5543248912132510441502689 4157436684099382831127017)
                      ·
                        rfl

theorem cell23_8096579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 1, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 1, 2, 5, 2, 2].length) (baseStart_8096579 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8096579 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8096579 prefixEnd_8096579 := by exact prefixLift 8096579
  have htrace : WordTrace (prefixWord ++ tailWord_8096579) baseStart_8096579 baseEnd_8096579 := by
    simpa [prefixWord, tailWord_8096579, baseEnd_8096579] using wordTrace_append hprefix tailTrace_8096579
  have hstable : (prefixWord ++ tailWord_8096579).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8096579).length < 2 ^ (prefixWord ++ tailWord_8096579).sum := by decide
  have hdescent : baseEnd_8096579 < baseStart_8096579 := by decide
  rcases family_descends (prefixWord ++ tailWord_8096579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8096585 : List Nat := [1, 2, 1, 1, 2, 6, 10]
def baseStart_8096585 : Nat := 118140960795 + 8096585 * 2 ^ 59
def prefixEnd_8096585 : Nat := 4983230072969 + 3 ^ 40 * 8096585 * 2
def baseEnd_8096585 : Nat := 51326416851645800094469

theorem tailTrace_8096585 : CollatzResearch.WordTrace tailWord_8096585 prefixEnd_8096585 51326416851645800094469 := by
  unfold tailWord_8096585
  simp only [CollatzResearch.WordTrace]
  refine ⟨295306715372462806473843209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196871143581641870982562139 295306715372462806473843209)
  ·
    refine ⟨221480036529347104855382407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 295306715372462806473843209 221480036529347104855382407)
    ·
      refine ⟨332220054794020657283073611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 221480036529347104855382407 332220054794020657283073611)
      ·
        refine ⟨498330082191030985924610417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 332220054794020657283073611 498330082191030985924610417)
        ·
          refine ⟨373747561643273239443457813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 498330082191030985924610417 373747561643273239443457813)
          ·
            refine ⟨17519416952028433098912085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 373747561643273239443457813 17519416952028433098912085)
            ·
              refine ⟨51326416851645800094469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 17519416952028433098912085 51326416851645800094469)
              ·
                rfl

theorem cell23_8096585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 6, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 6, 10].length) (baseStart_8096585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8096585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8096585 prefixEnd_8096585 := by exact prefixLift 8096585
  have htrace : WordTrace (prefixWord ++ tailWord_8096585) baseStart_8096585 baseEnd_8096585 := by
    simpa [prefixWord, tailWord_8096585, baseEnd_8096585] using wordTrace_append hprefix tailTrace_8096585
  have hstable : (prefixWord ++ tailWord_8096585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8096585).length < 2 ^ (prefixWord ++ tailWord_8096585).sum := by decide
  have hdescent : baseEnd_8096585 < baseStart_8096585 := by decide
  rcases family_descends (prefixWord ++ tailWord_8096585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8096616 : List Nat := [2, 1, 4, 2, 1, 3, 2, 2, 1, 2, 3]
def baseStart_8096616 : Nat := 118140960795 + 8096616 * 2 ^ 59
def prefixEnd_8096616 : Nat := 4983230072969 + 3 ^ 40 * 8096616 * 2
def baseEnd_8096616 : Nat := 4157455682883599186364347

theorem tailTrace_8096616 : CollatzResearch.WordTrace tailWord_8096616 prefixEnd_8096616 4157455682883599186364347 := by
  unfold tailWord_8096616
  simp only [CollatzResearch.WordTrace]
  refine ⟨147653923017675249384110851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196871897356900332512147801 147653923017675249384110851)
  ·
    refine ⟨221480884526512874076166277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147653923017675249384110851 221480884526512874076166277)
    ·
      refine ⟨41527665848721163889281177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 221480884526512874076166277 41527665848721163889281177)
      ·
        refine ⟨31145749386540872916960883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41527665848721163889281177 31145749386540872916960883)
        ·
          refine ⟨46718624079811309375441325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31145749386540872916960883 46718624079811309375441325)
          ·
            refine ⟨17519484029929241015790497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46718624079811309375441325 17519484029929241015790497)
            ·
              refine ⟨13139613022446930761842873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17519484029929241015790497 13139613022446930761842873)
              ·
                refine ⟨9854709766835198071382155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13139613022446930761842873 9854709766835198071382155)
                ·
                  refine ⟨14782064650252797107073233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9854709766835198071382155 14782064650252797107073233)
                  ·
                    refine ⟨11086548487689597830304925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14782064650252797107073233 11086548487689597830304925)
                    ·
                      refine ⟨4157455682883599186364347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11086548487689597830304925 4157455682883599186364347)
                      ·
                        rfl

theorem cell23_8096616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 3, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 3, 2, 2, 1, 2, 3].length) (baseStart_8096616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8096616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8096616 prefixEnd_8096616 := by exact prefixLift 8096616
  have htrace : WordTrace (prefixWord ++ tailWord_8096616) baseStart_8096616 baseEnd_8096616 := by
    simpa [prefixWord, tailWord_8096616, baseEnd_8096616] using wordTrace_append hprefix tailTrace_8096616
  have hstable : (prefixWord ++ tailWord_8096616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8096616).length < 2 ^ (prefixWord ++ tailWord_8096616).sum := by decide
  have hdescent : baseEnd_8096616 < baseStart_8096616 := by decide
  rcases family_descends (prefixWord ++ tailWord_8096616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8096672 : List Nat := [2, 1, 1, 4, 1, 1, 3, 2, 2, 1, 5]
def baseStart_8096672 : Nat := 118140960795 + 8096672 * 2 ^ 59
def prefixEnd_8096672 : Nat := 4983230072969 + 3 ^ 40 * 8096672 * 2
def baseEnd_8096672 : Nat := 4157484437800250967264089

theorem tailTrace_8096672 : CollatzResearch.WordTrace tailWord_8096672 prefixEnd_8096672 4157484437800250967264089 := by
  unfold tailWord_8096672
  simp only [CollatzResearch.WordTrace]
  refine ⟨147654944261573810166130135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196873259015431746888173513 147654944261573810166130135)
  ·
    refine ⟨221482416392360715249195203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147654944261573810166130135 221482416392360715249195203)
    ·
      refine ⟨332223624588541072873792805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 221482416392360715249195203 332223624588541072873792805)
      ·
        refine ⟨62291929610351451163836151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 332223624588541072873792805 62291929610351451163836151)
        ·
          refine ⟨93437894415527176745754227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62291929610351451163836151 93437894415527176745754227)
          ·
            refine ⟨140156841623290765118631341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93437894415527176745754227 140156841623290765118631341)
            ·
              refine ⟨52558815608734036919486753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 140156841623290765118631341 52558815608734036919486753)
              ·
                refine ⟨39419111706550527689615065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52558815608734036919486753 39419111706550527689615065)
                ·
                  refine ⟨29564333779912895767211299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39419111706550527689615065 29564333779912895767211299)
                  ·
                    refine ⟨44346500669869343650816949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29564333779912895767211299 44346500669869343650816949)
                    ·
                      refine ⟨4157484437800250967264089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44346500669869343650816949 4157484437800250967264089)
                      ·
                        rfl

theorem cell23_8096672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 3, 2, 2, 1, 5].length) (baseStart_8096672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8096672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8096672 prefixEnd_8096672 := by exact prefixLift 8096672
  have htrace : WordTrace (prefixWord ++ tailWord_8096672) baseStart_8096672 baseEnd_8096672 := by
    simpa [prefixWord, tailWord_8096672, baseEnd_8096672] using wordTrace_append hprefix tailTrace_8096672
  have hstable : (prefixWord ++ tailWord_8096672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8096672).length < 2 ^ (prefixWord ++ tailWord_8096672).sum := by decide
  have hdescent : baseEnd_8096672 < baseStart_8096672 := by decide
  rcases family_descends (prefixWord ++ tailWord_8096672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8096673 : List Nat := [1, 2, 3, 4, 1, 1, 3, 2, 1, 3, 2]
def baseStart_8096673 : Nat := 118140960795 + 8096673 * 2 ^ 59
def prefixEnd_8096673 : Nat := 4983230072969 + 3 ^ 40 * 8096673 * 2
def baseEnd_8096673 : Nat := 4157484951280905463351585

theorem tailTrace_8096673 : CollatzResearch.WordTrace tailWord_8096673 prefixEnd_8096673 4157484951280905463351585 := by
  unfold tailWord_8096673
  simp only [CollatzResearch.WordTrace]
  refine ⟨295309924996143997503046673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196873283330762665002031115 295309924996143997503046673)
  ·
    refine ⟨221482443747107998127285005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 295309924996143997503046673 221482443747107998127285005)
    ·
      refine ⟨83055916405165499297731877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 221482443747107998127285005 83055916405165499297731877)
      ·
        refine ⟨15572984325968531118324727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 83055916405165499297731877 15572984325968531118324727)
        ·
          refine ⟨23359476488952796677487091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15572984325968531118324727 23359476488952796677487091)
          ·
            refine ⟨35039214733429195016230637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23359476488952796677487091 35039214733429195016230637)
            ·
              refine ⟨13139705525035948131086489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35039214733429195016230637 13139705525035948131086489)
              ·
                refine ⟨9854779143776961098314867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13139705525035948131086489 9854779143776961098314867)
                ·
                  refine ⟨14782168715665441647472301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9854779143776961098314867 14782168715665441647472301)
                  ·
                    refine ⟨5543313268374540617802113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14782168715665441647472301 5543313268374540617802113)
                    ·
                      refine ⟨4157484951280905463351585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5543313268374540617802113 4157484951280905463351585)
                      ·
                        rfl

theorem cell23_8096673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 3, 2, 1, 3, 2].length) (baseStart_8096673 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8096673 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8096673 prefixEnd_8096673 := by exact prefixLift 8096673
  have htrace : WordTrace (prefixWord ++ tailWord_8096673) baseStart_8096673 baseEnd_8096673 := by
    simpa [prefixWord, tailWord_8096673, baseEnd_8096673] using wordTrace_append hprefix tailTrace_8096673
  have hstable : (prefixWord ++ tailWord_8096673).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8096673).length < 2 ^ (prefixWord ++ tailWord_8096673).sum := by decide
  have hdescent : baseEnd_8096673 < baseStart_8096673 := by decide
  rcases family_descends (prefixWord ++ tailWord_8096673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8096719 : List Nat := [1, 1, 2, 1, 1, 7, 1, 1, 2, 3, 3]
def baseStart_8096719 : Nat := 118140960795 + 8096719 * 2 ^ 59
def prefixEnd_8096719 : Nat := 4983230072969 + 3 ^ 40 * 8096719 * 2
def baseEnd_8096719 : Nat := 4157508571391012283376373

theorem tailTrace_8096719 : CollatzResearch.WordTrace tailWord_8096719 prefixEnd_8096719 4157508571391012283376373 := by
  unfold tailWord_8096719
  simp only [CollatzResearch.WordTrace]
  refine ⟨295311602753977347359221211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196874401835984898239480807 295311602753977347359221211)
  ·
    refine ⟨442967404130966021038831817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 295311602753977347359221211 442967404130966021038831817)
    ·
      refine ⟨332225553098224515779123863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 442967404130966021038831817 332225553098224515779123863)
      ·
        refine ⟨498338329647336773668685795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 332225553098224515779123863 498338329647336773668685795)
        ·
          refine ⟨747507494471005160503028693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 498338329647336773668685795 747507494471005160503028693)
          ·
            refine ⟨17519706901664183449289735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 747507494471005160503028693 17519706901664183449289735)
            ·
              refine ⟨26279560352496275173934603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17519706901664183449289735 26279560352496275173934603)
              ·
                refine ⟨39419340528744412760901905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26279560352496275173934603 39419340528744412760901905)
                ·
                  refine ⟨29564505396558309570676429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39419340528744412760901905 29564505396558309570676429)
                  ·
                    refine ⟨11086689523709366089003661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29564505396558309570676429 11086689523709366089003661)
                    ·
                      refine ⟨4157508571391012283376373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11086689523709366089003661 4157508571391012283376373)
                      ·
                        rfl

theorem cell23_8096719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 7, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 7, 1, 1, 2, 3, 3].length) (baseStart_8096719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8096719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8096719 prefixEnd_8096719 := by exact prefixLift 8096719
  have htrace : WordTrace (prefixWord ++ tailWord_8096719) baseStart_8096719 baseEnd_8096719 := by
    simpa [prefixWord, tailWord_8096719, baseEnd_8096719] using wordTrace_append hprefix tailTrace_8096719
  have hstable : (prefixWord ++ tailWord_8096719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8096719).length < 2 ^ (prefixWord ++ tailWord_8096719).sum := by decide
  have hdescent : baseEnd_8096719 < baseStart_8096719 := by decide
  rcases family_descends (prefixWord ++ tailWord_8096719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8096726 : List Nat := [5, 2, 1, 1, 2, 2, 1, 2, 7]
def baseStart_8096726 : Nat := 118140960795 + 8096726 * 2 ^ 59
def prefixEnd_8096726 : Nat := 4983230072969 + 3 ^ 40 * 8096726 * 2
def baseEnd_8096726 : Nat := 461945796195065972887649

theorem tailTrace_8096726 : CollatzResearch.WordTrace tailWord_8096726 prefixEnd_8096726 461945796195065972887649 := by
  unfold tailWord_8096726
  simp only [CollatzResearch.WordTrace]
  refine ⟨18456991129059499222170377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 196874572043301325036484021 18456991129059499222170377)
  ·
    refine ⟨13842743346794624416627783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18456991129059499222170377 13842743346794624416627783)
    ·
      refine ⟨20764115020191936624941675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13842743346794624416627783 20764115020191936624941675)
      ·
        refine ⟨31146172530287904937412513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20764115020191936624941675 31146172530287904937412513)
        ·
          refine ⟨23359629397715928703059385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31146172530287904937412513 23359629397715928703059385)
          ·
            refine ⟨17519722048286946527294539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23359629397715928703059385 17519722048286946527294539)
            ·
              refine ⟨26279583072430419790941809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17519722048286946527294539 26279583072430419790941809)
              ·
                refine ⟨19709687304322814843206357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26279583072430419790941809 19709687304322814843206357)
                ·
                  refine ⟨461945796195065972887649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19709687304322814843206357 461945796195065972887649)
                  ·
                    rfl

theorem cell23_8096726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 2, 1, 2, 7].length) (baseStart_8096726 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8096726 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8096726 prefixEnd_8096726 := by exact prefixLift 8096726
  have htrace : WordTrace (prefixWord ++ tailWord_8096726) baseStart_8096726 baseEnd_8096726 := by
    simpa [prefixWord, tailWord_8096726, baseEnd_8096726] using wordTrace_append hprefix tailTrace_8096726
  have hstable : (prefixWord ++ tailWord_8096726).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8096726).length < 2 ^ (prefixWord ++ tailWord_8096726).sum := by decide
  have hdescent : baseEnd_8096726 < baseStart_8096726 := by decide
  rcases family_descends (prefixWord ++ tailWord_8096726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8096754 : List Nat := [3, 2, 1, 5, 2, 1, 1, 2, 2, 2, 2]
def baseStart_8096754 : Nat := 118140960795 + 8096754 * 2 ^ 59
def prefixEnd_8096754 : Nat := 4983230072969 + 3 ^ 40 * 8096754 * 2
def baseEnd_8096754 : Nat := 4157526543213919646438713

theorem tailTrace_8096754 : CollatzResearch.WordTrace tailWord_8096754 prefixEnd_8096754 4157526543213919646438713 := by
  unfold tailWord_8096754
  simp only [CollatzResearch.WordTrace]
  refine ⟨73828219827212637084186329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 196875252872567032224496877 73828219827212637084186329)
  ·
    refine ⟨55371164870409477813139747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73828219827212637084186329 55371164870409477813139747)
    ·
      refine ⟨83056747305614216719709621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55371164870409477813139747 83056747305614216719709621)
      ·
        refine ⟨7786570059901332817472777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 83056747305614216719709621 7786570059901332817472777)
        ·
          refine ⟨5839927544925999613104583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7786570059901332817472777 5839927544925999613104583)
          ·
            refine ⟨8759891317388999419656875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5839927544925999613104583 8759891317388999419656875)
            ·
              refine ⟨13139836976083499129485313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8759891317388999419656875 13139836976083499129485313)
              ·
                refine ⟨9854877732062624347113985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13139836976083499129485313 9854877732062624347113985)
                ·
                  refine ⟨7391158299046968260335489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9854877732062624347113985 7391158299046968260335489)
                  ·
                    refine ⟨5543368724285226195251617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7391158299046968260335489 5543368724285226195251617)
                    ·
                      refine ⟨4157526543213919646438713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5543368724285226195251617 4157526543213919646438713)
                      ·
                        rfl

theorem cell23_8096754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 2, 1, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 2, 1, 1, 2, 2, 2, 2].length) (baseStart_8096754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8096754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8096754 prefixEnd_8096754 := by exact prefixLift 8096754
  have htrace : WordTrace (prefixWord ++ tailWord_8096754) baseStart_8096754 baseEnd_8096754 := by
    simpa [prefixWord, tailWord_8096754, baseEnd_8096754] using wordTrace_append hprefix tailTrace_8096754
  have hstable : (prefixWord ++ tailWord_8096754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8096754).length < 2 ^ (prefixWord ++ tailWord_8096754).sum := by decide
  have hdescent : baseEnd_8096754 < baseStart_8096754 := by decide
  rcases family_descends (prefixWord ++ tailWord_8096754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8096762 : List Nat := [3, 1, 1, 1, 1, 2, 1, 3, 2, 3, 5]
def baseStart_8096762 : Nat := 118140960795 + 8096762 * 2 ^ 59
def prefixEnd_8096762 : Nat := 4983230072969 + 3 ^ 40 * 8096762 * 2
def baseEnd_8096762 : Nat := 4157530651059155615138675

theorem tailTrace_8096762 : CollatzResearch.WordTrace tailWord_8096762 prefixEnd_8096762 4157530651059155615138675 := by
  unfold tailWord_8096762
  simp only [CollatzResearch.WordTrace]
  refine ⟨73828292773205391425759135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 196875447395214377135357693 73828292773205391425759135)
  ·
    refine ⟨110742439159808087138638703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73828292773205391425759135 110742439159808087138638703)
    ·
      refine ⟨166113658739712130707958055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110742439159808087138638703 166113658739712130707958055)
      ·
        refine ⟨249170488109568196061937083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166113658739712130707958055 249170488109568196061937083)
        ·
          refine ⟨373755732164352294092905625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 249170488109568196061937083 373755732164352294092905625)
          ·
            refine ⟨280316799123264220569679219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 373755732164352294092905625 280316799123264220569679219)
            ·
              refine ⟨420475198684896330854518829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 280316799123264220569679219 420475198684896330854518829)
              ·
                refine ⟨157678199506836124070444561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 420475198684896330854518829 157678199506836124070444561)
                ·
                  refine ⟨118258649630127093052833421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 157678199506836124070444561 118258649630127093052833421)
                  ·
                    refine ⟨44346993611297659894812533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 118258649630127093052833421 44346993611297659894812533)
                    ·
                      refine ⟨4157530651059155615138675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44346993611297659894812533 4157530651059155615138675)
                      ·
                        rfl

theorem cell23_8096762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 3, 2, 3, 5].length) (baseStart_8096762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8096762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8096762 prefixEnd_8096762 := by exact prefixLift 8096762
  have htrace : WordTrace (prefixWord ++ tailWord_8096762) baseStart_8096762 baseEnd_8096762 := by
    simpa [prefixWord, tailWord_8096762, baseEnd_8096762] using wordTrace_append hprefix tailTrace_8096762
  have hstable : (prefixWord ++ tailWord_8096762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8096762).length < 2 ^ (prefixWord ++ tailWord_8096762).sum := by decide
  have hdescent : baseEnd_8096762 < baseStart_8096762 := by decide
  rcases family_descends (prefixWord ++ tailWord_8096762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8096776 : List Nat := [2, 1, 3, 2, 1, 3, 2, 1, 2, 4, 2]
def baseStart_8096776 : Nat := 118140960795 + 8096776 * 2 ^ 59
def prefixEnd_8096776 : Nat := 4983230072969 + 3 ^ 40 * 8096776 * 2
def baseEnd_8096776 : Nat := 4157537839788318560363611

theorem tailTrace_8096776 : CollatzResearch.WordTrace tailWord_8096776 prefixEnd_8096776 4157537839788318560363611 := by
  unfold tailWord_8096776
  simp only [CollatzResearch.WordTrace]
  refine ⟨147656840857385423047023091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196875787809847230729364121 147656840857385423047023091)
  ·
    refine ⟨221485261286078134570534637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147656840857385423047023091 221485261286078134570534637)
    ·
      refine ⟨83056972982279300463950489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 221485261286078134570534637 83056972982279300463950489)
      ·
        refine ⟨62292729736709475347962867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83056972982279300463950489 62292729736709475347962867)
        ·
          refine ⟨93439094605064213021944301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62292729736709475347962867 93439094605064213021944301)
          ·
            refine ⟨35039660476899079883229113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 93439094605064213021944301 35039660476899079883229113)
            ·
              refine ⟨26279745357674309912421835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35039660476899079883229113 26279745357674309912421835)
              ·
                refine ⟨39419618036511464868632753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26279745357674309912421835 39419618036511464868632753)
                ·
                  refine ⟨29564713527383598651474565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39419618036511464868632753 29564713527383598651474565)
                  ·
                    refine ⟨5543383786384424747151481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29564713527383598651474565 5543383786384424747151481)
                    ·
                      refine ⟨4157537839788318560363611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5543383786384424747151481 4157537839788318560363611)
                      ·
                        rfl

theorem cell23_8096776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 2, 1, 2, 4, 2].length) (baseStart_8096776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8096776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8096776 prefixEnd_8096776 := by exact prefixLift 8096776
  have htrace : WordTrace (prefixWord ++ tailWord_8096776) baseStart_8096776 baseEnd_8096776 := by
    simpa [prefixWord, tailWord_8096776, baseEnd_8096776] using wordTrace_append hprefix tailTrace_8096776
  have hstable : (prefixWord ++ tailWord_8096776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8096776).length < 2 ^ (prefixWord ++ tailWord_8096776).sum := by decide
  have hdescent : baseEnd_8096776 < baseStart_8096776 := by decide
  rcases family_descends (prefixWord ++ tailWord_8096776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8096779 : List Nat := [1, 1, 1, 1, 6, 2, 1, 2, 1, 4, 3]
def baseStart_8096779 : Nat := 118140960795 + 8096779 * 2 ^ 59
def prefixEnd_8096779 : Nat := 4983230072969 + 3 ^ 40 * 8096779 * 2
def baseEnd_8096779 : Nat := 4157539380230282048626097

theorem tailTrace_8096779 : CollatzResearch.WordTrace tailWord_8096779 prefixEnd_8096779 4157539380230282048626097 := by
  unfold tailWord_8096779
  simp only [CollatzResearch.WordTrace]
  refine ⟨295313791133759977606405391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196875860755839985070936927 295313791133759977606405391)
  ·
    refine ⟨442970686700639966409608087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 295313791133759977606405391 442970686700639966409608087)
    ·
      refine ⟨664456030050959949614412131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 442970686700639966409608087 664456030050959949614412131)
      ·
        refine ⟨996684045076439924421618197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 664456030050959949614412131 996684045076439924421618197)
        ·
          refine ⟨46719564612958121457263353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 996684045076439924421618197 46719564612958121457263353)
          ·
            refine ⟨35039673459718591092947515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46719564612958121457263353 35039673459718591092947515)
            ·
              refine ⟨52559510189577886639421273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35039673459718591092947515 52559510189577886639421273)
              ·
                refine ⟨39419632642183414979565955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52559510189577886639421273 39419632642183414979565955)
                ·
                  refine ⟨59129448963275122469348933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39419632642183414979565955 59129448963275122469348933)
                  ·
                    refine ⟨11086771680614085463002925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 59129448963275122469348933 11086771680614085463002925)
                    ·
                      refine ⟨4157539380230282048626097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11086771680614085463002925 4157539380230282048626097)
                      ·
                        rfl

theorem cell23_8096779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 1, 2, 1, 4, 3].length) (baseStart_8096779 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8096779 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8096779 prefixEnd_8096779 := by exact prefixLift 8096779
  have htrace : WordTrace (prefixWord ++ tailWord_8096779) baseStart_8096779 baseEnd_8096779 := by
    simpa [prefixWord, tailWord_8096779, baseEnd_8096779] using wordTrace_append hprefix tailTrace_8096779
  have hstable : (prefixWord ++ tailWord_8096779).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8096779).length < 2 ^ (prefixWord ++ tailWord_8096779).sum := by decide
  have hdescent : baseEnd_8096779 < baseStart_8096779 := by decide
  rcases family_descends (prefixWord ++ tailWord_8096779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8096803 : List Nat := [1, 1, 1, 4, 3, 2, 3, 3, 1, 4]
def baseStart_8096803 : Nat := 118140960795 + 8096803 * 2 ^ 59
def prefixEnd_8096803 : Nat := 4983230072969 + 3 ^ 40 * 8096803 * 2
def baseEnd_8096803 : Nat := 1385850567921996651575329

theorem tailTrace_8096803 : CollatzResearch.WordTrace tailWord_8096803 prefixEnd_8096803 1385850567921996651575329 := by
  unfold tailWord_8096803
  simp only [CollatzResearch.WordTrace]
  refine ⟨295314666485673029705279063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196876444323782019803519375 295314666485673029705279063)
  ·
    refine ⟨442971999728509544557918595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 295314666485673029705279063 442971999728509544557918595)
    ·
      refine ⟨664457999592764316836877893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 442971999728509544557918595 664457999592764316836877893)
      ·
        refine ⟨124585874923643309406914605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 664457999592764316836877893 124585874923643309406914605)
        ·
          refine ⟨46719703096366241027592977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 124585874923643309406914605 46719703096366241027592977)
          ·
            refine ⟨35039777322274680770694733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46719703096366241027592977 35039777322274680770694733)
            ·
              refine ⟨13139916495853005289010525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35039777322274680770694733 13139916495853005289010525)
              ·
                refine ⟨4927468685944876983378947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13139916495853005289010525 4927468685944876983378947)
                ·
                  refine ⟨7391203028917315475068421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4927468685944876983378947 7391203028917315475068421)
                  ·
                    refine ⟨1385850567921996651575329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7391203028917315475068421 1385850567921996651575329)
                    ·
                      rfl

theorem cell23_8096803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 3, 3, 1, 4].length) (baseStart_8096803 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8096803 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8096803 prefixEnd_8096803 := by exact prefixLift 8096803
  have htrace : WordTrace (prefixWord ++ tailWord_8096803) baseStart_8096803 baseEnd_8096803 := by
    simpa [prefixWord, tailWord_8096803, baseEnd_8096803] using wordTrace_append hprefix tailTrace_8096803
  have hstable : (prefixWord ++ tailWord_8096803).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8096803).length < 2 ^ (prefixWord ++ tailWord_8096803).sum := by decide
  have hdescent : baseEnd_8096803 < baseStart_8096803 := by decide
  rcases family_descends (prefixWord ++ tailWord_8096803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8096820 : List Nat := [2, 5, 1, 2, 1, 3, 1, 1, 3, 4]
def baseStart_8096820 : Nat := 118140960795 + 8096820 * 2 ^ 59
def prefixEnd_8096820 : Nat := 4983230072969 + 3 ^ 40 * 8096820 * 2
def baseEnd_8096820 : Nat := 1385853477645705462737803

theorem tailTrace_8096820 : CollatzResearch.WordTrace tailWord_8096820 prefixEnd_8096820 1385853477645705462737803 := by
  unfold tailWord_8096820
  simp only [CollatzResearch.WordTrace]
  refine ⟨147657643263305720804323957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196876857684407627739098609 147657643263305720804323957)
  ·
    refine ⟨13842904055934911325405371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 147657643263305720804323957 13842904055934911325405371)
    ·
      refine ⟨20764356083902366988108057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13842904055934911325405371 20764356083902366988108057)
      ·
        refine ⟨15573267062926775241081043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20764356083902366988108057 15573267062926775241081043)
        ·
          refine ⟨23359900594390162861621565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15573267062926775241081043 23359900594390162861621565)
          ·
            refine ⟨8759962722896311073108087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23359900594390162861621565 8759962722896311073108087)
            ·
              refine ⟨13139944084344466609662131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8759962722896311073108087 13139944084344466609662131)
              ·
                refine ⟨19709916126516699914493197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13139944084344466609662131 19709916126516699914493197)
                ·
                  refine ⟨7391218547443762467934949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19709916126516699914493197 7391218547443762467934949)
                  ·
                    refine ⟨1385853477645705462737803, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7391218547443762467934949 1385853477645705462737803)
                    ·
                      rfl

theorem cell23_8096820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 3, 1, 1, 3, 4].length) (baseStart_8096820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8096820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8096820 prefixEnd_8096820 := by exact prefixLift 8096820
  have htrace : WordTrace (prefixWord ++ tailWord_8096820) baseStart_8096820 baseEnd_8096820 := by
    simpa [prefixWord, tailWord_8096820, baseEnd_8096820] using wordTrace_append hprefix tailTrace_8096820
  have hstable : (prefixWord ++ tailWord_8096820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8096820).length < 2 ^ (prefixWord ++ tailWord_8096820).sum := by decide
  have hdescent : baseEnd_8096820 < baseStart_8096820 := by decide
  rcases family_descends (prefixWord ++ tailWord_8096820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8096853 : List Nat := [1, 3, 2, 2, 1, 2, 4, 1, 2, 3, 2]
def baseStart_8096853 : Nat := 118140960795 + 8096853 * 2 ^ 59
def prefixEnd_8096853 : Nat := 4983230072969 + 3 ^ 40 * 8096853 * 2
def baseEnd_8096853 : Nat := 4157577377798714759100757

theorem tailTrace_8096853 : CollatzResearch.WordTrace tailWord_8096853 prefixEnd_8096853 4157577377798714759100757 := by
  unfold tailWord_8096853
  simp only [CollatzResearch.WordTrace]
  refine ⟨295316490135491888244599213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196877660090327925496399475 295316490135491888244599213)
  ·
    refine ⟨110743683800809458091724705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 295316490135491888244599213 110743683800809458091724705)
    ·
      refine ⟨83057762850607093568793529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110743683800809458091724705 83057762850607093568793529)
      ·
        refine ⟨62293322137955320176595147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83057762850607093568793529 62293322137955320176595147)
        ·
          refine ⟨93439983206932980264892721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62293322137955320176595147 93439983206932980264892721)
          ·
            refine ⟨70079987405199735198669541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 93439983206932980264892721 70079987405199735198669541)
            ·
              refine ⟨13139997638474950349750539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 70079987405199735198669541 13139997638474950349750539)
              ·
                refine ⟨19709996457712425524625809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13139997638474950349750539 19709996457712425524625809)
                ·
                  refine ⟨14782497343284319143469357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19709996457712425524625809 14782497343284319143469357)
                  ·
                    refine ⟨5543436503731619678801009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14782497343284319143469357 5543436503731619678801009)
                    ·
                      refine ⟨4157577377798714759100757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5543436503731619678801009 4157577377798714759100757)
                      ·
                        rfl

theorem cell23_8096853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 4, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 4, 1, 2, 3, 2].length) (baseStart_8096853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8096853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8096853 prefixEnd_8096853 := by exact prefixLift 8096853
  have htrace : WordTrace (prefixWord ++ tailWord_8096853) baseStart_8096853 baseEnd_8096853 := by
    simpa [prefixWord, tailWord_8096853, baseEnd_8096853] using wordTrace_append hprefix tailTrace_8096853
  have hstable : (prefixWord ++ tailWord_8096853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8096853).length < 2 ^ (prefixWord ++ tailWord_8096853).sum := by decide
  have hdescent : baseEnd_8096853 < baseStart_8096853 := by decide
  rcases family_descends (prefixWord ++ tailWord_8096853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8096860 : List Nat := [2, 2, 4, 1, 1, 1, 2, 5, 1, 1, 3]
def baseStart_8096860 : Nat := 118140960795 + 8096860 * 2 ^ 59
def prefixEnd_8096860 : Nat := 4983230072969 + 3 ^ 40 * 8096860 * 2
def baseEnd_8096860 : Nat := 4157580972163296231713225

theorem tailTrace_8096860 : CollatzResearch.WordTrace tailWord_8096860 prefixEnd_8096860 4157580972163296231713225 := by
  unfold tailWord_8096860
  simp only [CollatzResearch.WordTrace]
  refine ⟨147658372723233264220052017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196877830297644352293402689 147658372723233264220052017)
  ·
    refine ⟨110743779542424948165039013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147658372723233264220052017 110743779542424948165039013)
    ·
      refine ⟨20764458664204677780944815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 110743779542424948165039013 20764458664204677780944815)
      ·
        refine ⟨31146687996307016671417223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20764458664204677780944815 31146687996307016671417223)
        ·
          refine ⟨46720031994460525007125835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31146687996307016671417223 46720031994460525007125835)
          ·
            refine ⟨70080047991690787510688753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46720031994460525007125835 70080047991690787510688753)
            ·
              refine ⟨52560035993768090633016565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70080047991690787510688753 52560035993768090633016565)
              ·
                refine ⟨4927503374415758496845303, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 52560035993768090633016565 4927503374415758496845303)
                ·
                  refine ⟨7391255061623637745267955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4927503374415758496845303 7391255061623637745267955)
                  ·
                    refine ⟨11086882592435456617901933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7391255061623637745267955 11086882592435456617901933)
                    ·
                      refine ⟨4157580972163296231713225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11086882592435456617901933 4157580972163296231713225)
                      ·
                        rfl

theorem cell23_8096860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 2, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 2, 5, 1, 1, 3].length) (baseStart_8096860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8096860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8096860 prefixEnd_8096860 := by exact prefixLift 8096860
  have htrace : WordTrace (prefixWord ++ tailWord_8096860) baseStart_8096860 baseEnd_8096860 := by
    simpa [prefixWord, tailWord_8096860, baseEnd_8096860] using wordTrace_append hprefix tailTrace_8096860
  have hstable : (prefixWord ++ tailWord_8096860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8096860).length < 2 ^ (prefixWord ++ tailWord_8096860).sum := by decide
  have hdescent : baseEnd_8096860 < baseStart_8096860 := by decide
  rcases family_descends (prefixWord ++ tailWord_8096860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8096877 : List Nat := [1, 5, 1, 1, 2, 2, 4, 2, 1, 1, 3]
def baseStart_8096877 : Nat := 118140960795 + 8096877 * 2 ^ 59
def prefixEnd_8096877 : Nat := 4983230072969 + 3 ^ 40 * 8096877 * 2
def baseEnd_8096877 : Nat := 4157589701334422665200647

theorem tailTrace_8096877 : CollatzResearch.WordTrace tailWord_8096877 prefixEnd_8096877 4157589701334422665200647 := by
  unfold tailWord_8096877
  simp only [CollatzResearch.WordTrace]
  refine ⟨295317365487404940343472885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196878243658269960228981923 295317365487404940343472885)
  ·
    refine ⟨27686003014444213157200583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 295317365487404940343472885 27686003014444213157200583)
    ·
      refine ⟨41529004521666319735800875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27686003014444213157200583 41529004521666319735800875)
      ·
        refine ⟨62293506782499479603701313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41529004521666319735800875 62293506782499479603701313)
        ·
          refine ⟨46720130086874609702775985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62293506782499479603701313 46720130086874609702775985)
          ·
            refine ⟨35040097565155957277081989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46720130086874609702775985 35040097565155957277081989)
            ·
              refine ⟨6570018293466741989452873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35040097565155957277081989 6570018293466741989452873)
              ·
                refine ⟨4927513720100056492089655, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6570018293466741989452873 4927513720100056492089655)
                ·
                  refine ⟨7391270580150084738134483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4927513720100056492089655 7391270580150084738134483)
                  ·
                    refine ⟨11086905870225127107201725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7391270580150084738134483 11086905870225127107201725)
                    ·
                      refine ⟨4157589701334422665200647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11086905870225127107201725 4157589701334422665200647)
                      ·
                        rfl

theorem cell23_8096877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 4, 2, 1, 1, 3].length) (baseStart_8096877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8096877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8096877 prefixEnd_8096877 := by exact prefixLift 8096877
  have htrace : WordTrace (prefixWord ++ tailWord_8096877) baseStart_8096877 baseEnd_8096877 := by
    simpa [prefixWord, tailWord_8096877, baseEnd_8096877] using wordTrace_append hprefix tailTrace_8096877
  have hstable : (prefixWord ++ tailWord_8096877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8096877).length < 2 ^ (prefixWord ++ tailWord_8096877).sum := by decide
  have hdescent : baseEnd_8096877 < baseStart_8096877 := by decide
  rcases family_descends (prefixWord ++ tailWord_8096877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8096879 : List Nat := [1, 1, 2, 1, 3, 3, 1, 2, 3, 2, 4]
def baseStart_8096879 : Nat := 118140960795 + 8096879 * 2 ^ 59
def prefixEnd_8096879 : Nat := 4983230072969 + 3 ^ 40 * 8096879 * 2
def baseEnd_8096879 : Nat := 4157590728295731657375637

theorem tailTrace_8096879 : CollatzResearch.WordTrace tailWord_8096879 prefixEnd_8096879 4157590728295731657375637 := by
  unfold tailWord_8096879
  simp only [CollatzResearch.WordTrace]
  refine ⟨295317438433397694685045691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196878292288931796456697127 295317438433397694685045691)
  ·
    refine ⟨442976157650096542027568537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 295317438433397694685045691 442976157650096542027568537)
    ·
      refine ⟨332232118237572406520676403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 442976157650096542027568537 332232118237572406520676403)
      ·
        refine ⟨498348177356358609781014605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 332232118237572406520676403 498348177356358609781014605)
        ·
          refine ⟨186880566508634478667880477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 498348177356358609781014605 186880566508634478667880477)
          ·
            refine ⟨70080212440737929500455179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 186880566508634478667880477 70080212440737929500455179)
            ·
              refine ⟨105120318661106894250682769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70080212440737929500455179 105120318661106894250682769)
              ·
                refine ⟨78840238995830170688012077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 105120318661106894250682769 78840238995830170688012077)
                ·
                  refine ⟨29565089623436314008004529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 78840238995830170688012077 29565089623436314008004529)
                  ·
                    refine ⟨22173817217577235506003397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29565089623436314008004529 22173817217577235506003397)
                    ·
                      refine ⟨4157590728295731657375637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22173817217577235506003397 4157590728295731657375637)
                      ·
                        rfl

theorem cell23_8096879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 1, 2, 3, 2, 4].length) (baseStart_8096879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8096879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8096879 prefixEnd_8096879 := by exact prefixLift 8096879
  have htrace : WordTrace (prefixWord ++ tailWord_8096879) baseStart_8096879 baseEnd_8096879 := by
    simpa [prefixWord, tailWord_8096879, baseEnd_8096879] using wordTrace_append hprefix tailTrace_8096879
  have hstable : (prefixWord ++ tailWord_8096879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8096879).length < 2 ^ (prefixWord ++ tailWord_8096879).sum := by decide
  have hdescent : baseEnd_8096879 < baseStart_8096879 := by decide
  rcases family_descends (prefixWord ++ tailWord_8096879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8096886 : List Nat := [5, 1, 1, 2, 1, 1, 2, 1, 3, 1, 5]
def baseStart_8096886 : Nat := 118140960795 + 8096886 * 2 ^ 59
def prefixEnd_8096886 : Nat := 4983230072969 + 3 ^ 40 * 8096886 * 2
def baseEnd_8096886 : Nat := 4157594322660313129988105

theorem tailTrace_8096886 : CollatzResearch.WordTrace tailWord_8096886 prefixEnd_8096886 4157594322660313129988105 := by
  unfold tailWord_8096886
  simp only [CollatzResearch.WordTrace]
  refine ⟨18457355859023270930034407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 196878462496248223253700341 18457355859023270930034407)
  ·
    refine ⟨27686033788534906395051611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18457355859023270930034407 27686033788534906395051611)
    ·
      refine ⟨41529050682802359592577417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27686033788534906395051611 41529050682802359592577417)
      ·
        refine ⟨31146788012101769694433063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41529050682802359592577417 31146788012101769694433063)
        ·
          refine ⟨46720182018152654541649595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31146788012101769694433063 46720182018152654541649595)
          ·
            refine ⟨70080273027228981812474393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46720182018152654541649595 70080273027228981812474393)
            ·
              refine ⟨52560204770421736359355795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70080273027228981812474393 52560204770421736359355795)
              ·
                refine ⟨78840307155632604539033693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52560204770421736359355795 78840307155632604539033693)
                ·
                  refine ⟨29565115183362226702137635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 78840307155632604539033693 29565115183362226702137635)
                  ·
                    refine ⟨44347672775043340053206453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29565115183362226702137635 44347672775043340053206453)
                    ·
                      refine ⟨4157594322660313129988105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44347672775043340053206453 4157594322660313129988105)
                      ·
                        rfl

theorem cell23_8096886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 2, 1, 3, 1, 5].length) (baseStart_8096886 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8096886 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8096886 prefixEnd_8096886 := by exact prefixLift 8096886
  have htrace : WordTrace (prefixWord ++ tailWord_8096886) baseStart_8096886 baseEnd_8096886 := by
    simpa [prefixWord, tailWord_8096886, baseEnd_8096886] using wordTrace_append hprefix tailTrace_8096886
  have hstable : (prefixWord ++ tailWord_8096886).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8096886).length < 2 ^ (prefixWord ++ tailWord_8096886).sum := by decide
  have hdescent : baseEnd_8096886 < baseStart_8096886 := by decide
  rcases family_descends (prefixWord ++ tailWord_8096886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8096894 : List Nat := [4, 2, 4, 1, 1, 1, 1, 2, 3, 1, 3]
def baseStart_8096894 : Nat := 118140960795 + 8096894 * 2 ^ 59
def prefixEnd_8096894 : Nat := 4983230072969 + 3 ^ 40 * 8096894 * 2
def baseEnd_8096894 : Nat := 4157598430505549098688069

theorem tailTrace_8096894 : CollatzResearch.WordTrace tailWord_8096894 prefixEnd_8096894 4157598430505549098688069 := by
  unfold tailWord_8096894
  simp only [CollatzResearch.WordTrace]
  refine ⟨36914748191042919030855217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 196878657018895568164561157 36914748191042919030855217)
  ·
    refine ⟨27686061143282189273141413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36914748191042919030855217 27686061143282189273141413)
    ·
      refine ⟨5191136464365410488714015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 27686061143282189273141413 5191136464365410488714015)
      ·
        refine ⟨7786704696548115733071023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5191136464365410488714015 7786704696548115733071023)
        ·
          refine ⟨11680057044822173599606535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7786704696548115733071023 11680057044822173599606535)
          ·
            refine ⟨17520085567233260399409803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11680057044822173599606535 17520085567233260399409803)
            ·
              refine ⟨26280128350849890599114705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17520085567233260399409803 26280128350849890599114705)
              ·
                refine ⟨19710096263137417949336029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26280128350849890599114705 19710096263137417949336029)
                ·
                  refine ⟨7391286098676531731001011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19710096263137417949336029 7391286098676531731001011)
                  ·
                    refine ⟨11086929148014797596501517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7391286098676531731001011 11086929148014797596501517)
                    ·
                      refine ⟨4157598430505549098688069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11086929148014797596501517 4157598430505549098688069)
                      ·
                        rfl

theorem cell23_8096894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 1, 1, 2, 3, 1, 3].length) (baseStart_8096894 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8096894 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8096894 prefixEnd_8096894 := by exact prefixLift 8096894
  have htrace : WordTrace (prefixWord ++ tailWord_8096894) baseStart_8096894 baseEnd_8096894 := by
    simpa [prefixWord, tailWord_8096894, baseEnd_8096894] using wordTrace_append hprefix tailTrace_8096894
  have hstable : (prefixWord ++ tailWord_8096894).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8096894).length < 2 ^ (prefixWord ++ tailWord_8096894).sum := by decide
  have hdescent : baseEnd_8096894 < baseStart_8096894 := by decide
  rcases family_descends (prefixWord ++ tailWord_8096894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8096900 : List Nat := [2, 3, 2, 1, 2, 3, 1, 2, 3, 2, 2]
def baseStart_8096900 : Nat := 118140960795 + 8096900 * 2 ^ 59
def prefixEnd_8096900 : Nat := 4983230072969 + 3 ^ 40 * 8096900 * 2
def baseEnd_8096900 : Nat := 4157601511389476075213041

theorem tailTrace_8096900 : CollatzResearch.WordTrace tailWord_8096900 prefixEnd_8096900 4157601511389476075213041 := by
  unfold tailWord_8096900
  simp only [CollatzResearch.WordTrace]
  refine ⟨147659102183160807635780077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196878802910881076847706769 147659102183160807635780077)
  ·
    refine ⟨55372163318685302863417529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 147659102183160807635780077 55372163318685302863417529)
    ·
      refine ⟨41529122489013977147563147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55372163318685302863417529 41529122489013977147563147)
      ·
        refine ⟨62293683733520965721344721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41529122489013977147563147 62293683733520965721344721)
        ·
          refine ⟨46720262800140724291008541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62293683733520965721344721 46720262800140724291008541)
          ·
            refine ⟨17520098550052771609128203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46720262800140724291008541 17520098550052771609128203)
            ·
              refine ⟨26280147825079157413692305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17520098550052771609128203 26280147825079157413692305)
              ·
                refine ⟨19710110868809368060269229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26280147825079157413692305 19710110868809368060269229)
                ·
                  refine ⟨7391291575803513022600961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19710110868809368060269229 7391291575803513022600961)
                  ·
                    refine ⟨5543468681852634766950721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7391291575803513022600961 5543468681852634766950721)
                    ·
                      refine ⟨4157601511389476075213041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5543468681852634766950721 4157601511389476075213041)
                      ·
                        rfl

theorem cell23_8096900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 3, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 3, 1, 2, 3, 2, 2].length) (baseStart_8096900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8096900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8096900 prefixEnd_8096900 := by exact prefixLift 8096900
  have htrace : WordTrace (prefixWord ++ tailWord_8096900) baseStart_8096900 baseEnd_8096900 := by
    simpa [prefixWord, tailWord_8096900, baseEnd_8096900] using wordTrace_append hprefix tailTrace_8096900
  have hstable : (prefixWord ++ tailWord_8096900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8096900).length < 2 ^ (prefixWord ++ tailWord_8096900).sum := by decide
  have hdescent : baseEnd_8096900 < baseStart_8096900 := by decide
  rcases family_descends (prefixWord ++ tailWord_8096900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8096906 : List Nat := [3, 1, 2, 3, 1, 1, 5, 7]
def baseStart_8096906 : Nat := 118140960795 + 8096906 * 2 ^ 59
def prefixEnd_8096906 : Nat := 4983230072969 + 3 ^ 40 * 8096906 * 2
def baseEnd_8096906 : Nat := 153985355269385298212519

theorem tailTrace_8096906 : CollatzResearch.WordTrace tailWord_8096906 prefixEnd_8096906 153985355269385298212519 := by
  unfold tailWord_8096906
  simp only [CollatzResearch.WordTrace]
  refine ⟨73829605801074969574069643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 196878948802866585530852381 73829605801074969574069643)
  ·
    refine ⟨110744408701612454361104465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73829605801074969574069643 110744408701612454361104465)
    ·
      refine ⟨83058306526209340770828349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110744408701612454361104465 83058306526209340770828349)
      ·
        refine ⟨31146864947328502789060631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 83058306526209340770828349 31146864947328502789060631)
        ·
          refine ⟨46720297420992754183590947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31146864947328502789060631 46720297420992754183590947)
          ·
            refine ⟨70080446131489131275386421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46720297420992754183590947 70080446131489131275386421)
            ·
              refine ⟨6570041824827106057067477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 70080446131489131275386421 6570041824827106057067477)
              ·
                refine ⟨153985355269385298212519, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6570041824827106057067477 153985355269385298212519)
                ·
                  rfl

theorem cell23_8096906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 5, 7].length) (baseStart_8096906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8096906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8096906 prefixEnd_8096906 := by exact prefixLift 8096906
  have htrace : WordTrace (prefixWord ++ tailWord_8096906) baseStart_8096906 baseEnd_8096906 := by
    simpa [prefixWord, tailWord_8096906, baseEnd_8096906] using wordTrace_append hprefix tailTrace_8096906
  have hstable : (prefixWord ++ tailWord_8096906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8096906).length < 2 ^ (prefixWord ++ tailWord_8096906).sum := by decide
  have hdescent : baseEnd_8096906 < baseStart_8096906 := by decide
  rcases family_descends (prefixWord ++ tailWord_8096906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8096920 : List Nat := [2, 1, 2, 4, 2, 1, 4, 1, 1, 2, 3]
def baseStart_8096920 : Nat := 118140960795 + 8096920 * 2 ^ 59
def prefixEnd_8096920 : Nat := 4983230072969 + 3 ^ 40 * 8096920 * 2
def baseEnd_8096920 : Nat := 4157611781002565996962949

theorem tailTrace_8096920 : CollatzResearch.WordTrace tailWord_8096920 prefixEnd_8096920 4157611781002565996962949 := by
  unfold tailWord_8096920
  simp only [CollatzResearch.WordTrace]
  refine ⟨147659466913124579343644107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196879289217499439124858809 147659466913124579343644107)
  ·
    refine ⟨221489200369686869015466161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147659466913124579343644107 221489200369686869015466161)
    ·
      refine ⟨166116900277265151761599621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 221489200369686869015466161 166116900277265151761599621)
      ·
        refine ⟨31146918801987215955299929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 166116900277265151761599621 31146918801987215955299929)
        ·
          refine ⟨23360189101490411966474947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31146918801987215955299929 23360189101490411966474947)
          ·
            refine ⟨35040283652235617949712421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23360189101490411966474947 35040283652235617949712421)
            ·
              refine ⟨6570053184794178365571079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35040283652235617949712421 6570053184794178365571079)
              ·
                refine ⟨9855079777191267548356619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6570053184794178365571079 9855079777191267548356619)
                ·
                  refine ⟨14782619665786901322534929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9855079777191267548356619 14782619665786901322534929)
                  ·
                    refine ⟨11086964749340175991901197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14782619665786901322534929 11086964749340175991901197)
                    ·
                      refine ⟨4157611781002565996962949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11086964749340175991901197 4157611781002565996962949)
                      ·
                        rfl

theorem cell23_8096920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 4, 1, 1, 2, 3].length) (baseStart_8096920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8096920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8096920 prefixEnd_8096920 := by exact prefixLift 8096920
  have htrace : WordTrace (prefixWord ++ tailWord_8096920) baseStart_8096920 baseEnd_8096920 := by
    simpa [prefixWord, tailWord_8096920, baseEnd_8096920] using wordTrace_append hprefix tailTrace_8096920
  have hstable : (prefixWord ++ tailWord_8096920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8096920).length < 2 ^ (prefixWord ++ tailWord_8096920).sum := by decide
  have hdescent : baseEnd_8096920 < baseStart_8096920 := by decide
  rcases family_descends (prefixWord ++ tailWord_8096920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8096927 : List Nat := [1, 1, 2, 6, 3, 1, 1, 2, 2, 4]
def baseStart_8096927 : Nat := 118140960795 + 8096927 * 2 ^ 59
def prefixEnd_8096927 : Nat := 4983230072969 + 3 ^ 40 * 8096927 * 2
def baseEnd_8096927 : Nat := 1385871791789049156525139

theorem tailTrace_8096927 : CollatzResearch.WordTrace tailWord_8096927 prefixEnd_8096927 1385871791789049156525139 := by
  unfold tailWord_8096927
  simp only [CollatzResearch.WordTrace]
  refine ⟨295319189137223798882793035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196879459424815865921862023 295319189137223798882793035)
  ·
    refine ⟨442978783705835698324189553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 295319189137223798882793035 442978783705835698324189553)
    ·
      refine ⟨332234087779376773743142165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 442978783705835698324189553 332234087779376773743142165)
      ·
        refine ⟨15573472864658286269209789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 332234087779376773743142165 15573472864658286269209789)
        ·
          refine ⟨5840052324246857350953671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15573472864658286269209789 5840052324246857350953671)
          ·
            refine ⟨8760078486370286026430507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5840052324246857350953671 8760078486370286026430507)
            ·
              refine ⟨13140117729555429039645761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8760078486370286026430507 13140117729555429039645761)
              ·
                refine ⟨9855088297166571779734321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13140117729555429039645761 9855088297166571779734321)
                ·
                  refine ⟨7391316222874928834800741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9855088297166571779734321 7391316222874928834800741)
                  ·
                    refine ⟨1385871791789049156525139, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7391316222874928834800741 1385871791789049156525139)
                    ·
                      rfl

theorem cell23_8096927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 3, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 3, 1, 1, 2, 2, 4].length) (baseStart_8096927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8096927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8096927 prefixEnd_8096927 := by exact prefixLift 8096927
  have htrace : WordTrace (prefixWord ++ tailWord_8096927) baseStart_8096927 baseEnd_8096927 := by
    simpa [prefixWord, tailWord_8096927, baseEnd_8096927] using wordTrace_append hprefix tailTrace_8096927
  have hstable : (prefixWord ++ tailWord_8096927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8096927).length < 2 ^ (prefixWord ++ tailWord_8096927).sum := by decide
  have hdescent : baseEnd_8096927 < baseStart_8096927 := by decide
  rcases family_descends (prefixWord ++ tailWord_8096927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8096933 : List Nat := [1, 3, 1, 2, 1, 5, 1, 1, 4, 1, 3]
def baseStart_8096933 : Nat := 118140960795 + 8096933 * 2 ^ 59
def prefixEnd_8096933 : Nat := 4983230072969 + 3 ^ 40 * 8096933 * 2
def baseEnd_8096933 : Nat := 4157618456251074446100389

theorem tailTrace_8096933 : CollatzResearch.WordTrace tailWord_8096933 prefixEnd_8096933 4157618456251074446100389 := by
  unfold tailWord_8096933
  simp only [CollatzResearch.WordTrace]
  refine ⟨295319407975202061907511453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196879605316801374605007635 295319407975202061907511453)
  ·
    refine ⟨110744777990700773215316795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 295319407975202061907511453 110744777990700773215316795)
    ·
      refine ⟨166117166986051159822975193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110744777990700773215316795 166117166986051159822975193)
      ·
        refine ⟨124587875239538369867231395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 166117166986051159822975193 124587875239538369867231395)
        ·
          refine ⟨186881812859307554800847093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124587875239538369867231395 186881812859307554800847093)
          ·
            refine ⟨17520169955560083262579415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 186881812859307554800847093 17520169955560083262579415)
            ·
              refine ⟨26280254933340124893869123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17520169955560083262579415 26280254933340124893869123)
              ·
                refine ⟨39420382400010187340803685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26280254933340124893869123 39420382400010187340803685)
                ·
                  refine ⟨7391321700001910126400691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39420382400010187340803685 7391321700001910126400691)
                  ·
                    refine ⟨11086982550002865189601037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7391321700001910126400691 11086982550002865189601037)
                    ·
                      refine ⟨4157618456251074446100389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11086982550002865189601037 4157618456251074446100389)
                      ·
                        rfl

theorem cell23_8096933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 5, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 5, 1, 1, 4, 1, 3].length) (baseStart_8096933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8096933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8096933 prefixEnd_8096933 := by exact prefixLift 8096933
  have htrace : WordTrace (prefixWord ++ tailWord_8096933) baseStart_8096933 baseEnd_8096933 := by
    simpa [prefixWord, tailWord_8096933, baseEnd_8096933] using wordTrace_append hprefix tailTrace_8096933
  have hstable : (prefixWord ++ tailWord_8096933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8096933).length < 2 ^ (prefixWord ++ tailWord_8096933).sum := by decide
  have hdescent : baseEnd_8096933 < baseStart_8096933 := by decide
  rcases family_descends (prefixWord ++ tailWord_8096933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8096996 : List Nat := [2, 3, 1, 1, 1, 2, 5, 1, 7]
def baseStart_8096996 : Nat := 118140960795 + 8096996 * 2 ^ 59
def prefixEnd_8096996 : Nat := 4983230072969 + 3 ^ 40 * 8096996 * 2
def baseEnd_8096996 : Nat := 461961200614700855512511

theorem tailTrace_8096996 : CollatzResearch.WordTrace tailWord_8096996 prefixEnd_8096996 461961200614700855512511 := by
  unfold tailWord_8096996
  simp only [CollatzResearch.WordTrace]
  refine ⟨147660852886986911833527421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196881137182649215778036561 147660852886986911833527421)
  ·
    refine ⟨55372819832620091937572783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 147660852886986911833527421 55372819832620091937572783)
    ·
      refine ⟨83059229748930137906359175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55372819832620091937572783 83059229748930137906359175)
      ·
        refine ⟨124588844623395206859538763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83059229748930137906359175 124588844623395206859538763)
        ·
          refine ⟨186883266935092810289308145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124588844623395206859538763 186883266935092810289308145)
          ·
            refine ⟨140162450201319607716981109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 186883266935092810289308145 140162450201319607716981109)
            ·
              refine ⟨13140229706373713223466979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 140162450201319607716981109 13140229706373713223466979)
              ·
                refine ⟨19710344559560569835200469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13140229706373713223466979 19710344559560569835200469)
                ·
                  refine ⟨461961200614700855512511, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19710344559560569835200469 461961200614700855512511)
                  ·
                    rfl

theorem cell23_8096996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 5, 1, 7].length) (baseStart_8096996 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8096996 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8096996 prefixEnd_8096996 := by exact prefixLift 8096996
  have htrace : WordTrace (prefixWord ++ tailWord_8096996) baseStart_8096996 baseEnd_8096996 := by
    simpa [prefixWord, tailWord_8096996, baseEnd_8096996] using wordTrace_append hprefix tailTrace_8096996
  have hstable : (prefixWord ++ tailWord_8096996).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8096996).length < 2 ^ (prefixWord ++ tailWord_8096996).sum := by decide
  have hdescent : baseEnd_8096996 < baseStart_8096996 := by decide
  rcases family_descends (prefixWord ++ tailWord_8096996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8097007 : List Nat := [1, 1, 2, 1, 7, 1, 1, 3, 2, 2, 2]
def baseStart_8097007 : Nat := 118140960795 + 8097007 * 2 ^ 59
def prefixEnd_8097007 : Nat := 4983230072969 + 3 ^ 40 * 8097007 * 2
def baseEnd_8097007 : Nat := 4157656453819507156575049

theorem tailTrace_8097007 : CollatzResearch.WordTrace tailWord_8097007 prefixEnd_8097007 4157656453819507156575049 := by
  unfold tailWord_8097007
  simp only [CollatzResearch.WordTrace]
  refine ⟨295322106976933972545705275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196881404651289315030470183 295322106976933972545705275)
  ·
    refine ⟨442983160465400958818557913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 295322106976933972545705275 442983160465400958818557913)
    ·
      refine ⟨332237370349050719113918435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 442983160465400958818557913 332237370349050719113918435)
      ·
        refine ⟨498356055523576078670877653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 332237370349050719113918435 498356055523576078670877653)
        ·
          refine ⟨11680220051333814343848695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 498356055523576078670877653 11680220051333814343848695)
          ·
            refine ⟨17520330077000721515773043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11680220051333814343848695 17520330077000721515773043)
            ·
              refine ⟨26280495115501082273659565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17520330077000721515773043 26280495115501082273659565)
              ·
                refine ⟨9855185668312905852622337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26280495115501082273659565 9855185668312905852622337)
                ·
                  refine ⟨7391389251234679389466753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9855185668312905852622337 7391389251234679389466753)
                  ·
                    refine ⟨5543541938426009542100065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7391389251234679389466753 5543541938426009542100065)
                    ·
                      refine ⟨4157656453819507156575049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5543541938426009542100065 4157656453819507156575049)
                      ·
                        rfl

theorem cell23_8097007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 1, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 1, 1, 3, 2, 2, 2].length) (baseStart_8097007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8097007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8097007 prefixEnd_8097007 := by exact prefixLift 8097007
  have htrace : WordTrace (prefixWord ++ tailWord_8097007) baseStart_8097007 baseEnd_8097007 := by
    simpa [prefixWord, tailWord_8097007, baseEnd_8097007] using wordTrace_append hprefix tailTrace_8097007
  have hstable : (prefixWord ++ tailWord_8097007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8097007).length < 2 ^ (prefixWord ++ tailWord_8097007).sum := by decide
  have hdescent : baseEnd_8097007 < baseStart_8097007 := by decide
  rcases family_descends (prefixWord ++ tailWord_8097007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8097036 : List Nat := [2, 2, 1, 2, 2, 3, 1, 2, 1, 2, 5]
def baseStart_8097036 : Nat := 118140960795 + 8097036 * 2 ^ 59
def prefixEnd_8097036 : Nat := 4983230072969 + 3 ^ 40 * 8097036 * 2
def baseEnd_8097036 : Nat := 4157671344758487543112415

theorem tailTrace_8097036 : CollatzResearch.WordTrace tailWord_8097036 prefixEnd_8097036 4157671344758487543112415 := by
  unfold tailWord_8097036
  simp only [CollatzResearch.WordTrace]
  refine ⟨147661582346914455249255481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196882109795885940332340641 147661582346914455249255481)
  ·
    refine ⟨110746186760185841436941611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147661582346914455249255481 110746186760185841436941611)
    ·
      refine ⟨166119280140278762155412417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110746186760185841436941611 166119280140278762155412417)
      ·
        refine ⟨124589460105209071616559313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 166119280140278762155412417 124589460105209071616559313)
        ·
          refine ⟨93442095078906803712419485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 124589460105209071616559313 93442095078906803712419485)
          ·
            refine ⟨35040785654590051392157307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 93442095078906803712419485 35040785654590051392157307)
            ·
              refine ⟨52561178481885077088235961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35040785654590051392157307 52561178481885077088235961)
              ·
                refine ⟨39420883861413807816176971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52561178481885077088235961 39420883861413807816176971)
                ·
                  refine ⟨59131325792120711724265457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39420883861413807816176971 59131325792120711724265457)
                  ·
                    refine ⟨44348494344090533793199093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 59131325792120711724265457 44348494344090533793199093)
                    ·
                      refine ⟨4157671344758487543112415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44348494344090533793199093 4157671344758487543112415)
                      ·
                        rfl

theorem cell23_8097036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 1, 2, 1, 2, 5].length) (baseStart_8097036 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8097036 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8097036 prefixEnd_8097036 := by exact prefixLift 8097036
  have htrace : WordTrace (prefixWord ++ tailWord_8097036) baseStart_8097036 baseEnd_8097036 := by
    simpa [prefixWord, tailWord_8097036, baseEnd_8097036] using wordTrace_append hprefix tailTrace_8097036
  have hstable : (prefixWord ++ tailWord_8097036).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8097036).length < 2 ^ (prefixWord ++ tailWord_8097036).sum := by decide
  have hdescent : baseEnd_8097036 < baseStart_8097036 := by decide
  rcases family_descends (prefixWord ++ tailWord_8097036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8097053 : List Nat := [1, 4, 2, 3, 1, 1, 2, 1, 1, 2, 5]
def baseStart_8097053 : Nat := 118140960795 + 8097053 * 2 ^ 59
def prefixEnd_8097053 : Nat := 4983230072969 + 3 ^ 40 * 8097053 * 2
def baseEnd_8097053 : Nat := 4157680073929613976599837

theorem tailTrace_8097053 : CollatzResearch.WordTrace tailWord_8097053 prefixEnd_8097053 4157680073929613976599837 := by
  unfold tailWord_8097053
  simp only [CollatzResearch.WordTrace]
  refine ⟨295323784734767322401879813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196882523156511548267919875 295323784734767322401879813)
  ·
    refine ⟨55373209637768872950352465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 295323784734767322401879813 55373209637768872950352465)
    ·
      refine ⟨41529907228326654712764349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55373209637768872950352465 41529907228326654712764349)
      ·
        refine ⟨15573715210622495517286631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41529907228326654712764349 15573715210622495517286631)
        ·
          refine ⟨23360572815933743275929947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15573715210622495517286631 23360572815933743275929947)
          ·
            refine ⟨35040859223900614913894921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23360572815933743275929947 35040859223900614913894921)
            ·
              refine ⟨26280644417925461185421191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35040859223900614913894921 26280644417925461185421191)
              ·
                refine ⟨39420966626888191778131787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26280644417925461185421191 39420966626888191778131787)
                ·
                  refine ⟨59131449940332287667197681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39420966626888191778131787 59131449940332287667197681)
                  ·
                    refine ⟨44348587455249215750398261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 59131449940332287667197681 44348587455249215750398261)
                    ·
                      refine ⟨4157680073929613976599837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44348587455249215750398261 4157680073929613976599837)
                      ·
                        rfl

theorem cell23_8097053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 2, 1, 1, 2, 5].length) (baseStart_8097053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8097053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8097053 prefixEnd_8097053 := by exact prefixLift 8097053
  have htrace : WordTrace (prefixWord ++ tailWord_8097053) baseStart_8097053 baseEnd_8097053 := by
    simpa [prefixWord, tailWord_8097053, baseEnd_8097053] using wordTrace_append hprefix tailTrace_8097053
  have hstable : (prefixWord ++ tailWord_8097053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8097053).length < 2 ^ (prefixWord ++ tailWord_8097053).sum := by decide
  have hdescent : baseEnd_8097053 < baseStart_8097053 := by decide
  rcases family_descends (prefixWord ++ tailWord_8097053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8097073 : List Nat := [1, 2, 2, 3, 3, 1, 1, 1, 5, 4]
def baseStart_8097073 : Nat := 118140960795 + 8097073 * 2 ^ 59
def prefixEnd_8097073 : Nat := 4983230072969 + 3 ^ 40 * 8097073 * 2
def baseEnd_8097073 : Nat := 1385896781180901299449915

theorem tailTrace_8097073 : CollatzResearch.WordTrace tailWord_8097073 prefixEnd_8097073 1385896781180901299449915 := by
  unfold tailWord_8097073
  simp only [CollatzResearch.WordTrace]
  refine ⟨295324514194694865817607873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196883009463129910545071915 295324514194694865817607873)
  ·
    refine ⟨221493385646021149363205905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 295324514194694865817607873 221493385646021149363205905)
    ·
      refine ⟨166120039234515862022404429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 221493385646021149363205905 166120039234515862022404429)
      ·
        refine ⟨62295014712943448258401661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 166120039234515862022404429 62295014712943448258401661)
        ·
          refine ⟨23360630517353793096900623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62295014712943448258401661 23360630517353793096900623)
          ·
            refine ⟨35040945776030689645350935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23360630517353793096900623 35040945776030689645350935)
            ·
              refine ⟨52561418664046034468026403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35040945776030689645350935 52561418664046034468026403)
              ·
                refine ⟨78842127996069051702039605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52561418664046034468026403 78842127996069051702039605)
                ·
                  refine ⟨7391449499631473597066213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 78842127996069051702039605 7391449499631473597066213)
                  ·
                    refine ⟨1385896781180901299449915, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7391449499631473597066213 1385896781180901299449915)
                    ·
                      rfl

theorem cell23_8097073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 1, 1, 5, 4].length) (baseStart_8097073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8097073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8097073 prefixEnd_8097073 := by exact prefixLift 8097073
  have htrace : WordTrace (prefixWord ++ tailWord_8097073) baseStart_8097073 baseEnd_8097073 := by
    simpa [prefixWord, tailWord_8097073, baseEnd_8097073] using wordTrace_append hprefix tailTrace_8097073
  have hstable : (prefixWord ++ tailWord_8097073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8097073).length < 2 ^ (prefixWord ++ tailWord_8097073).sum := by decide
  have hdescent : baseEnd_8097073 < baseStart_8097073 := by decide
  rcases family_descends (prefixWord ++ tailWord_8097073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8097120 : List Nat := [2, 1, 1, 3, 4, 2, 3, 1, 6]
def baseStart_8097120 : Nat := 118140960795 + 8097120 * 2 ^ 59
def prefixEnd_8097120 : Nat := 4983230072969 + 3 ^ 40 * 8097120 * 2
def baseEnd_8097120 : Nat := 461968275237051690495781

theorem tailTrace_8097120 : CollatzResearch.WordTrace tailWord_8097120 prefixEnd_8097120 461968275237051690495781 := by
  unfold tailWord_8097120
  simp only [CollatzResearch.WordTrace]
  refine ⟨147663114212762296422284407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196884152283683061896379209 147663114212762296422284407)
  ·
    refine ⟨221494671319143444633426611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147663114212762296422284407 221494671319143444633426611)
    ·
      refine ⟨332242006978715166950139917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 221494671319143444633426611 332242006978715166950139917)
      ·
        refine ⟨124590752617018187606302469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 332242006978715166950139917 124590752617018187606302469)
        ·
          refine ⟨23360766115690910176181713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 124590752617018187606302469 23360766115690910176181713)
          ·
            refine ⟨17520574586768182632136285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23360766115690910176181713 17520574586768182632136285)
            ·
              refine ⟨6570215470038068487051107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17520574586768182632136285 6570215470038068487051107)
              ·
                refine ⟨9855323205057102730576661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6570215470038068487051107 9855323205057102730576661)
                ·
                  refine ⟨461968275237051690495781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9855323205057102730576661 461968275237051690495781)
                  ·
                    rfl

theorem cell23_8097120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 2, 3, 1, 6].length) (baseStart_8097120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8097120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8097120 prefixEnd_8097120 := by exact prefixLift 8097120
  have htrace : WordTrace (prefixWord ++ tailWord_8097120) baseStart_8097120 baseEnd_8097120 := by
    simpa [prefixWord, tailWord_8097120, baseEnd_8097120] using wordTrace_append hprefix tailTrace_8097120
  have hstable : (prefixWord ++ tailWord_8097120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8097120).length < 2 ^ (prefixWord ++ tailWord_8097120).sum := by decide
  have hdescent : baseEnd_8097120 < baseStart_8097120 := by decide
  rcases family_descends (prefixWord ++ tailWord_8097120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8097141 : List Nat := [1, 3, 4, 1, 4, 1, 1, 3, 1, 4]
def baseStart_8097141 : Nat := 118140960795 + 8097141 * 2 ^ 59
def prefixEnd_8097141 : Nat := 4983230072969 + 3 ^ 40 * 8097141 * 2
def baseEnd_8097141 : Nat := 1385908420075736544099811

theorem tailTrace_8097141 : CollatzResearch.WordTrace tailWord_8097141 prefixEnd_8097141 1385908420075736544099811 := by
  unfold tailWord_8097141
  simp only [CollatzResearch.WordTrace]
  refine ⟨295326994358448513431083277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196884662905632342287388851 295326994358448513431083277)
  ·
    refine ⟨110747622884418192536656229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 295326994358448513431083277 110747622884418192536656229)
    ·
      refine ⟨20765179290828411100623043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 110747622884418192536656229 20765179290828411100623043)
      ·
        refine ⟨31147768936242616650934565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20765179290828411100623043 31147768936242616650934565)
        ·
          refine ⟨5840206675545490622050231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31147768936242616650934565 5840206675545490622050231)
          ·
            refine ⟨8760310013318235933075347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5840206675545490622050231 8760310013318235933075347)
            ·
              refine ⟨13140465019977353899613021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8760310013318235933075347 13140465019977353899613021)
              ·
                refine ⟨4927674382491507712354883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13140465019977353899613021 4927674382491507712354883)
                ·
                  refine ⟨7391511573737261568532325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4927674382491507712354883 7391511573737261568532325)
                  ·
                    refine ⟨1385908420075736544099811, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7391511573737261568532325 1385908420075736544099811)
                    ·
                      rfl

theorem cell23_8097141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 4, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 4, 1, 1, 3, 1, 4].length) (baseStart_8097141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8097141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8097141 prefixEnd_8097141 := by exact prefixLift 8097141
  have htrace : WordTrace (prefixWord ++ tailWord_8097141) baseStart_8097141 baseEnd_8097141 := by
    simpa [prefixWord, tailWord_8097141, baseEnd_8097141] using wordTrace_append hprefix tailTrace_8097141
  have hstable : (prefixWord ++ tailWord_8097141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8097141).length < 2 ^ (prefixWord ++ tailWord_8097141).sum := by decide
  have hdescent : baseEnd_8097141 < baseStart_8097141 := by decide
  rcases family_descends (prefixWord ++ tailWord_8097141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8097163 : List Nat := [1, 1, 1, 1, 4, 3, 1, 3, 4, 4]
def baseStart_8097163 : Nat := 118140960795 + 8097163 * 2 ^ 59
def prefixEnd_8097163 : Nat := 4983230072969 + 3 ^ 40 * 8097163 * 2
def baseEnd_8097163 : Nat := 1385912185600536182074777

theorem tailTrace_8097163 : CollatzResearch.WordTrace tailWord_8097163 prefixEnd_8097163 1385912185600536182074777 := by
  unfold tailWord_8097163
  simp only [CollatzResearch.WordTrace]
  refine ⟨295327796764368811188384143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196885197842912540792256095 295327796764368811188384143)
  ·
    refine ⟨442991695146553216782576215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 295327796764368811188384143 442991695146553216782576215)
    ·
      refine ⟨664487542719829825173864323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 442991695146553216782576215 664487542719829825173864323)
      ·
        refine ⟨996731314079744737760796485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 664487542719829825173864323 996731314079744737760796485)
        ·
          refine ⟨186887121389952138330149341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 996731314079744737760796485 186887121389952138330149341)
          ·
            refine ⟨70082670521232051873806003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 186887121389952138330149341 70082670521232051873806003)
            ·
              refine ⟨105124005781848077810709005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70082670521232051873806003 105124005781848077810709005)
              ·
                refine ⟨39421502168193029179015877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 105124005781848077810709005 39421502168193029179015877)
                ·
                  refine ⟨7391531656536192971065477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39421502168193029179015877 7391531656536192971065477)
                  ·
                    refine ⟨1385912185600536182074777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7391531656536192971065477 1385912185600536182074777)
                    ·
                      rfl

theorem cell23_8097163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 1, 3, 4, 4].length) (baseStart_8097163 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8097163 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8097163 prefixEnd_8097163 := by exact prefixLift 8097163
  have htrace : WordTrace (prefixWord ++ tailWord_8097163) baseStart_8097163 baseEnd_8097163 := by
    simpa [prefixWord, tailWord_8097163, baseEnd_8097163] using wordTrace_append hprefix tailTrace_8097163
  have hstable : (prefixWord ++ tailWord_8097163).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8097163).length < 2 ^ (prefixWord ++ tailWord_8097163).sum := by decide
  have hdescent : baseEnd_8097163 < baseStart_8097163 := by decide
  rcases family_descends (prefixWord ++ tailWord_8097163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8097164 : List Nat := [2, 2, 1, 2, 1, 3, 5, 2, 1, 1, 3]
def baseStart_8097164 : Nat := 118140960795 + 8097164 * 2 ^ 59
def prefixEnd_8097164 : Nat := 4983230072969 + 3 ^ 40 * 8097164 * 2
def baseEnd_8097164 : Nat := 4157737070282263042311827

theorem tailTrace_8097164 : CollatzResearch.WordTrace tailWord_8097164 prefixEnd_8097164 4157737070282263042311827 := by
  unfold tailWord_8097164
  simp only [CollatzResearch.WordTrace]
  refine ⟨147663916618682594179585273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196885222158243458906113697 147663916618682594179585273)
  ·
    refine ⟨110747937464011945634688955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147663916618682594179585273 110747937464011945634688955)
    ·
      refine ⟨166121906196017918452033433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110747937464011945634688955 166121906196017918452033433)
      ·
        refine ⟨124591429647013438839025075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 166121906196017918452033433 124591429647013438839025075)
        ·
          refine ⟨186887144470520158258537613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124591429647013438839025075 186887144470520158258537613)
          ·
            refine ⟨70082679176445059346951605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 186887144470520158258537613 70082679176445059346951605)
            ·
              refine ⟨6570251172791724313776713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 70082679176445059346951605 6570251172791724313776713)
              ·
                refine ⟨4927688379593793235332535, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6570251172791724313776713 4927688379593793235332535)
                ·
                  refine ⟨7391532569390689852998803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4927688379593793235332535 7391532569390689852998803)
                  ·
                    refine ⟨11087298854086034779498205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7391532569390689852998803 11087298854086034779498205)
                    ·
                      refine ⟨4157737070282263042311827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11087298854086034779498205 4157737070282263042311827)
                      ·
                        rfl

theorem cell23_8097164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 5, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 5, 2, 1, 1, 3].length) (baseStart_8097164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8097164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8097164 prefixEnd_8097164 := by exact prefixLift 8097164
  have htrace : WordTrace (prefixWord ++ tailWord_8097164) baseStart_8097164 baseEnd_8097164 := by
    simpa [prefixWord, tailWord_8097164, baseEnd_8097164] using wordTrace_append hprefix tailTrace_8097164
  have hstable : (prefixWord ++ tailWord_8097164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8097164).length < 2 ^ (prefixWord ++ tailWord_8097164).sum := by decide
  have hdescent : baseEnd_8097164 < baseStart_8097164 := by decide
  rcases family_descends (prefixWord ++ tailWord_8097164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8097173 : List Nat := [1, 3, 2, 1, 1, 2, 4, 2, 1, 1, 5]
def baseStart_8097173 : Nat := 118140960795 + 8097173 * 2 ^ 59
def prefixEnd_8097173 : Nat := 4983230072969 + 3 ^ 40 * 8097173 * 2
def baseEnd_8097173 : Nat := 4157741691608153507099285

theorem tailTrace_8097173 : CollatzResearch.WordTrace tailWord_8097173 prefixEnd_8097173 4157741691608153507099285 := by
  unfold tailWord_8097173
  simp only [CollatzResearch.WordTrace]
  refine ⟨295328161494332582896248173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196885440996221721930832115 295328161494332582896248173)
  ·
    refine ⟨110748060560374718586093065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 295328161494332582896248173 110748060560374718586093065)
    ·
      refine ⟨83061045420281038939569799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110748060560374718586093065 83061045420281038939569799)
      ·
        refine ⟨124591568130421558409354699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83061045420281038939569799 124591568130421558409354699)
        ·
          refine ⟨186887352195632337614032049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124591568130421558409354699 186887352195632337614032049)
          ·
            refine ⟨140165514146724253210524037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 186887352195632337614032049 140165514146724253210524037)
            ·
              refine ⟨26281033902510797476973257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 140165514146724253210524037 26281033902510797476973257)
              ·
                refine ⟨19710775426883098107729943, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26281033902510797476973257 19710775426883098107729943)
                ·
                  refine ⟨29566163140324647161594915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19710775426883098107729943 29566163140324647161594915)
                  ·
                    refine ⟨44349244710486970742392373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29566163140324647161594915 44349244710486970742392373)
                    ·
                      refine ⟨4157741691608153507099285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44349244710486970742392373 4157741691608153507099285)
                      ·
                        rfl

theorem cell23_8097173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 4, 2, 1, 1, 5].length) (baseStart_8097173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8097173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8097173 prefixEnd_8097173 := by exact prefixLift 8097173
  have htrace : WordTrace (prefixWord ++ tailWord_8097173) baseStart_8097173 baseEnd_8097173 := by
    simpa [prefixWord, tailWord_8097173, baseEnd_8097173] using wordTrace_append hprefix tailTrace_8097173
  have hstable : (prefixWord ++ tailWord_8097173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8097173).length < 2 ^ (prefixWord ++ tailWord_8097173).sum := by decide
  have hdescent : baseEnd_8097173 < baseStart_8097173 := by decide
  rcases family_descends (prefixWord ++ tailWord_8097173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8097183 : List Nat := [1, 1, 2, 5, 1, 2, 2, 1, 1, 1, 6]
def baseStart_8097183 : Nat := 118140960795 + 8097183 * 2 ^ 59
def prefixEnd_8097183 : Nat := 4983230072969 + 3 ^ 40 * 8097183 * 2
def baseEnd_8097183 : Nat := 4157746826414698467974239

theorem tailTrace_8097183 : CollatzResearch.WordTrace tailWord_8097183 prefixEnd_8097183 4157746826414698467974239 := by
  unfold tailWord_8097183
  simp only [CollatzResearch.WordTrace]
  refine ⟨295328526224296354604112203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196885684149530903069408135 295328526224296354604112203)
  ·
    refine ⟨442992789336444531906168305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 295328526224296354604112203 442992789336444531906168305)
    ·
      refine ⟨332244592002333398929626229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 442992789336444531906168305 332244592002333398929626229)
      ·
        refine ⟨31147930500218756149652459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 332244592002333398929626229 31147930500218756149652459)
        ·
          refine ⟨46721895750328134224478689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31147930500218756149652459 46721895750328134224478689)
          ·
            refine ⟨35041421812746100668359017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46721895750328134224478689 35041421812746100668359017)
            ·
              refine ⟨26281066359559575501269263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35041421812746100668359017 26281066359559575501269263)
              ·
                refine ⟨39421599539339363251903895, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26281066359559575501269263 39421599539339363251903895)
                ·
                  refine ⟨59132399309009044877855843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39421599539339363251903895 59132399309009044877855843)
                  ·
                    refine ⟨88698598963513567316783765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 59132399309009044877855843 88698598963513567316783765)
                    ·
                      refine ⟨4157746826414698467974239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 88698598963513567316783765 4157746826414698467974239)
                      ·
                        rfl

theorem cell23_8097183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 2, 1, 1, 1, 6].length) (baseStart_8097183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8097183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8097183 prefixEnd_8097183 := by exact prefixLift 8097183
  have htrace : WordTrace (prefixWord ++ tailWord_8097183) baseStart_8097183 baseEnd_8097183 := by
    simpa [prefixWord, tailWord_8097183, baseEnd_8097183] using wordTrace_append hprefix tailTrace_8097183
  have hstable : (prefixWord ++ tailWord_8097183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8097183).length < 2 ^ (prefixWord ++ tailWord_8097183).sum := by decide
  have hdescent : baseEnd_8097183 < baseStart_8097183 := by decide
  rcases family_descends (prefixWord ++ tailWord_8097183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8097207 : List Nat := [1, 1, 3, 1, 3, 2, 5, 1, 1, 2, 3]
def baseStart_8097207 : Nat := 118140960795 + 8097207 * 2 ^ 59
def prefixEnd_8097207 : Nat := 4983230072969 + 3 ^ 40 * 8097207 * 2
def baseEnd_8097207 : Nat := 4157759149950406374074129

theorem tailTrace_8097207 : CollatzResearch.WordTrace tailWord_8097207 prefixEnd_8097207 4157759149950406374074129 := by
  unfold tailWord_8097207
  simp only [CollatzResearch.WordTrace]
  refine ⟨295329401576209406702985875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196886267717472937801990583 295329401576209406702985875)
  ·
    refine ⟨442994102364314110054478813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 295329401576209406702985875 442994102364314110054478813)
    ·
      refine ⟨166122788386617791270429555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 442994102364314110054478813 166122788386617791270429555)
      ·
        refine ⟨249184182579926686905644333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166122788386617791270429555 249184182579926686905644333)
        ·
          refine ⟨93444068467472507589616625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 249184182579926686905644333 93444068467472507589616625)
          ·
            refine ⟨70083051350604380692212469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 93444068467472507589616625 70083051350604380692212469)
            ·
              refine ⟨6570286064119160689894919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 70083051350604380692212469 6570286064119160689894919)
              ·
                refine ⟨9855429096178741034842379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6570286064119160689894919 9855429096178741034842379)
                ·
                  refine ⟨14783143644268111552263569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9855429096178741034842379 14783143644268111552263569)
                  ·
                    refine ⟨11087357733201083664197677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14783143644268111552263569 11087357733201083664197677)
                    ·
                      refine ⟨4157759149950406374074129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11087357733201083664197677 4157759149950406374074129)
                      ·
                        rfl

theorem cell23_8097207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 5, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 5, 1, 1, 2, 3].length) (baseStart_8097207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8097207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8097207 prefixEnd_8097207 := by exact prefixLift 8097207
  have htrace : WordTrace (prefixWord ++ tailWord_8097207) baseStart_8097207 baseEnd_8097207 := by
    simpa [prefixWord, tailWord_8097207, baseEnd_8097207] using wordTrace_append hprefix tailTrace_8097207
  have hstable : (prefixWord ++ tailWord_8097207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8097207).length < 2 ^ (prefixWord ++ tailWord_8097207).sum := by decide
  have hdescent : baseEnd_8097207 < baseStart_8097207 := by decide
  rcases family_descends (prefixWord ++ tailWord_8097207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8097237 : List Nat := [1, 3, 2, 3, 1, 1, 1, 5, 2, 1, 3]
def baseStart_8097237 : Nat := 118140960795 + 8097237 * 2 ^ 59
def prefixEnd_8097237 : Nat := 4983230072969 + 3 ^ 40 * 8097237 * 2
def baseEnd_8097237 : Nat := 4157774554370041256698991

theorem tailTrace_8097237 : CollatzResearch.WordTrace tailWord_8097237 prefixEnd_8097237 4157774554370041256698991 := by
  unfold tailWord_8097237
  simp only [CollatzResearch.WordTrace]
  refine ⟨295330495766100721826577965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196886997177400481217718643 295330495766100721826577965)
  ·
    refine ⟨110748935912287770684966737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 295330495766100721826577965 110748935912287770684966737)
    ·
      refine ⟨83061701934215828013725053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110748935912287770684966737 83061701934215828013725053)
      ·
        refine ⟨31148138225330935505146895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 83061701934215828013725053 31148138225330935505146895)
        ·
          refine ⟨46722207337996403257720343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31148138225330935505146895 46722207337996403257720343)
          ·
            refine ⟨70083311006994604886580515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46722207337996403257720343 70083311006994604886580515)
            ·
              refine ⟨105124966510491907329870773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70083311006994604886580515 105124966510491907329870773)
              ·
                refine ⟨9855465610358616312175385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 105124966510491907329870773 9855465610358616312175385)
                ·
                  refine ⟨7391599207768962234131539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9855465610358616312175385 7391599207768962234131539)
                  ·
                    refine ⟨11087398811653443351197309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7391599207768962234131539 11087398811653443351197309)
                    ·
                      refine ⟨4157774554370041256698991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11087398811653443351197309 4157774554370041256698991)
                      ·
                        rfl

theorem cell23_8097237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 1, 5, 2, 1, 3].length) (baseStart_8097237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8097237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8097237 prefixEnd_8097237 := by exact prefixLift 8097237
  have htrace : WordTrace (prefixWord ++ tailWord_8097237) baseStart_8097237 baseEnd_8097237 := by
    simpa [prefixWord, tailWord_8097237, baseEnd_8097237] using wordTrace_append hprefix tailTrace_8097237
  have hstable : (prefixWord ++ tailWord_8097237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8097237).length < 2 ^ (prefixWord ++ tailWord_8097237).sum := by decide
  have hdescent : baseEnd_8097237 < baseStart_8097237 := by decide
  rcases family_descends (prefixWord ++ tailWord_8097237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8097247 : List Nat := [1, 1, 2, 3, 3, 1, 2, 4, 1, 3, 2]
def baseStart_8097247 : Nat := 118140960795 + 8097247 * 2 ^ 59
def prefixEnd_8097247 : Nat := 4983230072969 + 3 ^ 40 * 8097247 * 2
def baseEnd_8097247 : Nat := 4157779689176586217573945

theorem tailTrace_8097247 : CollatzResearch.WordTrace tailWord_8097247 prefixEnd_8097247 4157779689176586217573945 := by
  unfold tailWord_8097247
  simp only [CollatzResearch.WordTrace]
  refine ⟨295330860496064493534441995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196887240330709662356294663 295330860496064493534441995)
  ·
    refine ⟨442996290744096740301662993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 295330860496064493534441995 442996290744096740301662993)
    ·
      refine ⟨332247218058072555226247245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 442996290744096740301662993 332247218058072555226247245)
      ·
        refine ⟨124592706771777208209842717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 332247218058072555226247245 124592706771777208209842717)
        ·
          refine ⟨46722265039416453078691019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 124592706771777208209842717 46722265039416453078691019)
          ·
            refine ⟨70083397559124679618036529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46722265039416453078691019 70083397559124679618036529)
            ·
              refine ⟨52562548169343509713527397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70083397559124679618036529 52562548169343509713527397)
              ·
                refine ⟨9855477781751908071286387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 52562548169343509713527397 9855477781751908071286387)
                ·
                  refine ⟨14783216672627862106929581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9855477781751908071286387 14783216672627862106929581)
                  ·
                    refine ⟨5543706252235448290098593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14783216672627862106929581 5543706252235448290098593)
                    ·
                      refine ⟨4157779689176586217573945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5543706252235448290098593 4157779689176586217573945)
                      ·
                        rfl

theorem cell23_8097247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 2, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 2, 4, 1, 3, 2].length) (baseStart_8097247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8097247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8097247 prefixEnd_8097247 := by exact prefixLift 8097247
  have htrace : WordTrace (prefixWord ++ tailWord_8097247) baseStart_8097247 baseEnd_8097247 := by
    simpa [prefixWord, tailWord_8097247, baseEnd_8097247] using wordTrace_append hprefix tailTrace_8097247
  have hstable : (prefixWord ++ tailWord_8097247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8097247).length < 2 ^ (prefixWord ++ tailWord_8097247).sum := by decide
  have hdescent : baseEnd_8097247 < baseStart_8097247 := by decide
  rcases family_descends (prefixWord ++ tailWord_8097247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8097260 : List Nat := [2, 2, 1, 1, 2, 1, 2, 3, 3, 4, 2]
def baseStart_8097260 : Nat := 118140960795 + 8097260 * 2 ^ 59
def prefixEnd_8097260 : Nat := 4983230072969 + 3 ^ 40 * 8097260 * 2
def baseEnd_8097260 : Nat := 4157786364425094666711385

theorem tailTrace_8097260 : CollatzResearch.WordTrace tailWord_8097260 prefixEnd_8097260 4157786364425094666711385 := by
  unfold tailWord_8097260
  simp only [CollatzResearch.WordTrace]
  refine ⟨147665667322508698377332617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196887556430011597836443489 147665667322508698377332617)
  ·
    refine ⟨110749250491881523782999463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147665667322508698377332617 110749250491881523782999463)
    ·
      refine ⟨166123875737822285674499195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110749250491881523782999463 166123875737822285674499195)
      ·
        refine ⟨249185813606733428511748793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166123875737822285674499195 249185813606733428511748793)
        ·
          refine ⟨186889360205050071383811595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 249185813606733428511748793 186889360205050071383811595)
          ·
            refine ⟨280334040307575107075717393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 186889360205050071383811595 280334040307575107075717393)
            ·
              refine ⟨210250530230681330306788045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 280334040307575107075717393 210250530230681330306788045)
              ·
                refine ⟨78843948836505498865045517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 210250530230681330306788045 78843948836505498865045517)
                ·
                  refine ⟨29566480813689562074392069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 78843948836505498865045517 29566480813689562074392069)
                  ·
                    refine ⟨5543715152566792888948513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29566480813689562074392069 5543715152566792888948513)
                    ·
                      refine ⟨4157786364425094666711385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5543715152566792888948513 4157786364425094666711385)
                      ·
                        rfl

theorem cell23_8097260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 4, 2].length) (baseStart_8097260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8097260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8097260 prefixEnd_8097260 := by exact prefixLift 8097260
  have htrace : WordTrace (prefixWord ++ tailWord_8097260) baseStart_8097260 baseEnd_8097260 := by
    simpa [prefixWord, tailWord_8097260, baseEnd_8097260] using wordTrace_append hprefix tailTrace_8097260
  have hstable : (prefixWord ++ tailWord_8097260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8097260).length < 2 ^ (prefixWord ++ tailWord_8097260).sum := by decide
  have hdescent : baseEnd_8097260 < baseStart_8097260 := by decide
  rcases family_descends (prefixWord ++ tailWord_8097260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8097263 : List Nat := [1, 1, 2, 1, 4, 1, 2, 3, 2, 1, 5]
def baseStart_8097263 : Nat := 118140960795 + 8097263 * 2 ^ 59
def prefixEnd_8097263 : Nat := 4983230072969 + 3 ^ 40 * 8097263 * 2
def baseEnd_8097263 : Nat := 4157787904867058154973871

theorem tailTrace_8097263 : CollatzResearch.WordTrace tailWord_8097263 prefixEnd_8097263 4157787904867058154973871 := by
  unfold tailWord_8097263
  simp only [CollatzResearch.WordTrace]
  refine ⟨295331444064006528267024443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196887629376004352178016295 295331444064006528267024443)
  ·
    refine ⟨442997166096009792400536665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 295331444064006528267024443 442997166096009792400536665)
    ·
      refine ⟨332247874572007344300402499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 442997166096009792400536665 332247874572007344300402499)
      ·
        refine ⟨498371811858011016450603749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 332247874572007344300402499 498371811858011016450603749)
        ·
          refine ⟨93444714723377065584488203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 498371811858011016450603749 93444714723377065584488203)
          ·
            refine ⟨140167072085065598376732305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93444714723377065584488203 140167072085065598376732305)
            ·
              refine ⟨105125304063799198782549229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 140167072085065598376732305 105125304063799198782549229)
              ·
                refine ⟨39421989023924699543455961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 105125304063799198782549229 39421989023924699543455961)
                ·
                  refine ⟨29566491767943524657591971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39421989023924699543455961 29566491767943524657591971)
                  ·
                    refine ⟨44349737651915286986387957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29566491767943524657591971 44349737651915286986387957)
                    ·
                      refine ⟨4157787904867058154973871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44349737651915286986387957 4157787904867058154973871)
                      ·
                        rfl

theorem cell23_8097263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 2, 3, 2, 1, 5].length) (baseStart_8097263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8097263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8097263 prefixEnd_8097263 := by exact prefixLift 8097263
  have htrace : WordTrace (prefixWord ++ tailWord_8097263) baseStart_8097263 baseEnd_8097263 := by
    simpa [prefixWord, tailWord_8097263, baseEnd_8097263] using wordTrace_append hprefix tailTrace_8097263
  have hstable : (prefixWord ++ tailWord_8097263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8097263).length < 2 ^ (prefixWord ++ tailWord_8097263).sum := by decide
  have hdescent : baseEnd_8097263 < baseStart_8097263 := by decide
  rcases family_descends (prefixWord ++ tailWord_8097263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8097264 : List Nat := [2, 1, 1, 1, 3, 4, 4, 1, 1, 3, 2]
def baseStart_8097264 : Nat := 118140960795 + 8097264 * 2 ^ 59
def prefixEnd_8097264 : Nat := 4983230072969 + 3 ^ 40 * 8097264 * 2
def baseEnd_8097264 : Nat := 4157788418347712651061367

theorem tailTrace_8097264 : CollatzResearch.WordTrace tailWord_8097264 prefixEnd_8097264 4157788418347712651061367 := by
  unfold tailWord_8097264
  simp only [CollatzResearch.WordTrace]
  refine ⟨147665740268501452718905423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196887653691335270291873897 147665740268501452718905423)
  ·
    refine ⟨221498610402752179078358135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147665740268501452718905423 221498610402752179078358135)
    ·
      refine ⟨332247915604128268617537203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 221498610402752179078358135 332247915604128268617537203)
      ·
        refine ⟨498371873406192402926305805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 332247915604128268617537203 498371873406192402926305805)
        ·
          refine ⟨186889452527322151097364677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 498371873406192402926305805 186889452527322151097364677)
          ·
            refine ⟨35041772348872903330755877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 186889452527322151097364677 35041772348872903330755877)
            ·
              refine ⟨6570332315413669374516727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35041772348872903330755877 6570332315413669374516727)
              ·
                refine ⟨9855498473120504061775091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6570332315413669374516727 9855498473120504061775091)
                ·
                  refine ⟨14783247709680756092662637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9855498473120504061775091 14783247709680756092662637)
                  ·
                    refine ⟨5543717891130283534748489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14783247709680756092662637 5543717891130283534748489)
                    ·
                      refine ⟨4157788418347712651061367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5543717891130283534748489 4157788418347712651061367)
                      ·
                        rfl

theorem cell23_8097264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 4, 1, 1, 3, 2].length) (baseStart_8097264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8097264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8097264 prefixEnd_8097264 := by exact prefixLift 8097264
  have htrace : WordTrace (prefixWord ++ tailWord_8097264) baseStart_8097264 baseEnd_8097264 := by
    simpa [prefixWord, tailWord_8097264, baseEnd_8097264] using wordTrace_append hprefix tailTrace_8097264
  have hstable : (prefixWord ++ tailWord_8097264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8097264).length < 2 ^ (prefixWord ++ tailWord_8097264).sum := by decide
  have hdescent : baseEnd_8097264 < baseStart_8097264 := by decide
  rcases family_descends (prefixWord ++ tailWord_8097264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8097270 : List Nat := [5, 1, 1, 1, 2, 2, 1, 2, 2, 6]
def baseStart_8097270 : Nat := 118140960795 + 8097270 * 2 ^ 59
def prefixEnd_8097270 : Nat := 4983230072969 + 3 ^ 40 * 8097270 * 2
def baseEnd_8097270 : Nat := 1385930499743879875862113

theorem tailTrace_8097270 : CollatzResearch.WordTrace tailWord_8097270 prefixEnd_8097270 1385930499743879875862113 := by
  unfold tailWord_8097270
  simp only [CollatzResearch.WordTrace]
  refine ⟨18458231210936323028908079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 196887799583320778975019509 18458231210936323028908079)
  ·
    refine ⟨27687346816404484543362119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18458231210936323028908079 27687346816404484543362119)
    ·
      refine ⟨41531020224606726815043179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27687346816404484543362119 41531020224606726815043179)
      ·
        refine ⟨62296530336910090222564769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41531020224606726815043179 62296530336910090222564769)
        ·
          refine ⟨46722397752682567666923577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62296530336910090222564769 46722397752682567666923577)
          ·
            refine ⟨35041798314511925750192683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46722397752682567666923577 35041798314511925750192683)
            ·
              refine ⟨52562697471767888625289025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35041798314511925750192683 52562697471767888625289025)
              ·
                refine ⟨39422023103825916468966769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52562697471767888625289025 39422023103825916468966769)
                ·
                  refine ⟨29566517327869437351725077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39422023103825916468966769 29566517327869437351725077)
                  ·
                    refine ⟨1385930499743879875862113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29566517327869437351725077 1385930499743879875862113)
                    ·
                      rfl

theorem cell23_8097270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 1, 2, 2, 6].length) (baseStart_8097270 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8097270 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8097270 prefixEnd_8097270 := by exact prefixLift 8097270
  have htrace : WordTrace (prefixWord ++ tailWord_8097270) baseStart_8097270 baseEnd_8097270 := by
    simpa [prefixWord, tailWord_8097270, baseEnd_8097270] using wordTrace_append hprefix tailTrace_8097270
  have hstable : (prefixWord ++ tailWord_8097270).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8097270).length < 2 ^ (prefixWord ++ tailWord_8097270).sum := by decide
  have hdescent : baseEnd_8097270 < baseStart_8097270 := by decide
  rcases family_descends (prefixWord ++ tailWord_8097270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8097290 : List Nat := [3, 1, 2, 2, 2, 2, 2, 1, 2, 2, 4]
def baseStart_8097290 : Nat := 118140960795 + 8097290 * 2 ^ 59
def prefixEnd_8097290 : Nat := 4983230072969 + 3 ^ 40 * 8097290 * 2
def baseEnd_8097290 : Nat := 4157801768844729549336247

theorem tailTrace_8097290 : CollatzResearch.WordTrace tailWord_8097290 prefixEnd_8097290 4157801768844729549336247 := by
  unfold tailWord_8097290
  simp only [CollatzResearch.WordTrace]
  refine ⟨73833107208727177969564331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 196888285889939141252171549 73833107208727177969564331)
  ·
    refine ⟨110749660813090766954346497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73833107208727177969564331 110749660813090766954346497)
    ·
      refine ⟨83062245609818075215759873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110749660813090766954346497 83062245609818075215759873)
      ·
        refine ⟨62296684207363556411819905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83062245609818075215759873 62296684207363556411819905)
        ·
          refine ⟨46722513155522667308864929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62296684207363556411819905 46722513155522667308864929)
          ·
            refine ⟨35041884866642000481648697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46722513155522667308864929 35041884866642000481648697)
            ·
              refine ⟨26281413649981500361236523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35041884866642000481648697 26281413649981500361236523)
              ·
                refine ⟨39422120474972250541854785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26281413649981500361236523 39422120474972250541854785)
                ·
                  refine ⟨29566590356229187906391089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39422120474972250541854785 29566590356229187906391089)
                  ·
                    refine ⟨22174942767171890929793317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29566590356229187906391089 22174942767171890929793317)
                    ·
                      refine ⟨4157801768844729549336247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22174942767171890929793317 4157801768844729549336247)
                      ·
                        rfl

theorem cell23_8097290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 2, 1, 2, 2, 4].length) (baseStart_8097290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8097290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8097290 prefixEnd_8097290 := by exact prefixLift 8097290
  have htrace : WordTrace (prefixWord ++ tailWord_8097290) baseStart_8097290 baseEnd_8097290 := by
    simpa [prefixWord, tailWord_8097290, baseEnd_8097290] using wordTrace_append hprefix tailTrace_8097290
  have hstable : (prefixWord ++ tailWord_8097290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8097290).length < 2 ^ (prefixWord ++ tailWord_8097290).sum := by decide
  have hdescent : baseEnd_8097290 < baseStart_8097290 := by decide
  rcases family_descends (prefixWord ++ tailWord_8097290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8097334 : List Nat := [5, 1, 2, 1, 3, 2, 1, 1, 7]
def baseStart_8097334 : Nat := 118140960795 + 8097334 * 2 ^ 59
def prefixEnd_8097334 : Nat := 4983230072969 + 3 ^ 40 * 8097334 * 2
def baseEnd_8097334 : Nat := 461980484665947486354005

theorem tailTrace_8097334 : CollatzResearch.WordTrace tailWord_8097334 prefixEnd_8097334 461980484665947486354005 := by
  unfold tailWord_8097334
  simp only [CollatzResearch.WordTrace]
  refine ⟨18458377102921831712053691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 196889355764499538261906037 18458377102921831712053691)
  ·
    refine ⟨27687565654382747568080537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18458377102921831712053691 27687565654382747568080537)
    ·
      refine ⟨20765674240787060676060403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27687565654382747568080537 20765674240787060676060403)
      ·
        refine ⟨31148511361180591014090605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20765674240787060676060403 31148511361180591014090605)
        ·
          refine ⟨11680691760442721630283977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31148511361180591014090605 11680691760442721630283977)
          ·
            refine ⟨8760518820332041222712983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11680691760442721630283977 8760518820332041222712983)
            ·
              refine ⟨13140778230498061834069475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8760518820332041222712983 13140778230498061834069475)
              ·
                refine ⟨19711167345747092751104213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13140778230498061834069475 19711167345747092751104213)
                ·
                  refine ⟨461980484665947486354005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19711167345747092751104213 461980484665947486354005)
                  ·
                    rfl

theorem cell23_8097334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 2, 1, 1, 7].length) (baseStart_8097334 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8097334 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8097334 prefixEnd_8097334 := by exact prefixLift 8097334
  have htrace : WordTrace (prefixWord ++ tailWord_8097334) baseStart_8097334 baseEnd_8097334 := by
    simpa [prefixWord, tailWord_8097334, baseEnd_8097334] using wordTrace_append hprefix tailTrace_8097334
  have hstable : (prefixWord ++ tailWord_8097334).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8097334).length < 2 ^ (prefixWord ++ tailWord_8097334).sum := by decide
  have hdescent : baseEnd_8097334 < baseStart_8097334 := by decide
  rcases family_descends (prefixWord ++ tailWord_8097334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8097353 : List Nat := [1, 2, 1, 1, 2, 2, 1, 2, 1, 5, 5]
def baseStart_8097353 : Nat := 118140960795 + 8097353 * 2 ^ 59
def prefixEnd_8097353 : Nat := 4983230072969 + 3 ^ 40 * 8097353 * 2
def baseEnd_8097353 : Nat := 4157834118125962802848457

theorem tailTrace_8097353 : CollatzResearch.WordTrace tailWord_8097353 prefixEnd_8097353 4157834118125962802848457 := by
  unfold tailWord_8097353
  simp only [CollatzResearch.WordTrace]
  refine ⟨295334726633680473637800713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196889817755786982425200475 295334726633680473637800713)
  ·
    refine ⟨221501044975260355228350535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 295334726633680473637800713 221501044975260355228350535)
    ·
      refine ⟨332251567462890532842525803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 221501044975260355228350535 332251567462890532842525803)
      ·
        refine ⟨498377351194335799263788705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 332251567462890532842525803 498377351194335799263788705)
        ·
          refine ⟨373783013395751849447841529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 498377351194335799263788705 373783013395751849447841529)
          ·
            refine ⟨280337260046813887085881147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 373783013395751849447841529 280337260046813887085881147)
            ·
              refine ⟨420505890070220830628821721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 280337260046813887085881147 420505890070220830628821721)
              ·
                refine ⟨315379417552665622971616291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 420505890070220830628821721 315379417552665622971616291)
                ·
                  refine ⟨473069126328998434457424437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 315379417552665622971616291 473069126328998434457424437)
                  ·
                    refine ⟨44350230593343603230383541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 473069126328998434457424437 44350230593343603230383541)
                    ·
                      refine ⟨4157834118125962802848457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44350230593343603230383541 4157834118125962802848457)
                      ·
                        rfl

theorem cell23_8097353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 2, 1, 5, 5].length) (baseStart_8097353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8097353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8097353 prefixEnd_8097353 := by exact prefixLift 8097353
  have htrace : WordTrace (prefixWord ++ tailWord_8097353) baseStart_8097353 baseEnd_8097353 := by
    simpa [prefixWord, tailWord_8097353, baseEnd_8097353] using wordTrace_append hprefix tailTrace_8097353
  have hstable : (prefixWord ++ tailWord_8097353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8097353).length < 2 ^ (prefixWord ++ tailWord_8097353).sum := by decide
  have hdescent : baseEnd_8097353 < baseStart_8097353 := by decide
  rcases family_descends (prefixWord ++ tailWord_8097353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8097360 : List Nat := [2, 1, 1, 1, 1, 3, 4, 1, 5, 4]
def baseStart_8097360 : Nat := 118140960795 + 8097360 * 2 ^ 59
def prefixEnd_8097360 : Nat := 4983230072969 + 3 ^ 40 * 8097360 * 2
def baseEnd_8097360 : Nat := 1385945904163514758486975

theorem tailTrace_8097360 : CollatzResearch.WordTrace tailWord_8097360 prefixEnd_8097360 1385945904163514758486975 := by
  unfold tailWord_8097360
  simp only [CollatzResearch.WordTrace]
  refine ⟨147667490972327556916652767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196889987963103409222203689 147667490972327556916652767)
  ·
    refine ⟨221501236458491335374979151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147667490972327556916652767 221501236458491335374979151)
    ·
      refine ⟨332251854687737003062468727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 221501236458491335374979151 332251854687737003062468727)
      ·
        refine ⟨498377782031605504593703091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 332251854687737003062468727 498377782031605504593703091)
        ·
          refine ⟨747566673047408256890554637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 498377782031605504593703091 747566673047408256890554637)
          ·
            refine ⟨280337502392778096333957989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 747566673047408256890554637 280337502392778096333957989)
            ·
              refine ⟨52563281698645893062617123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 280337502392778096333957989 52563281698645893062617123)
              ·
                refine ⟨78844922547968839593925685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52563281698645893062617123 78844922547968839593925685)
                ·
                  refine ⟨7391711488872078711930533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 78844922547968839593925685 7391711488872078711930533)
                  ·
                    refine ⟨1385945904163514758486975, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7391711488872078711930533 1385945904163514758486975)
                    ·
                      rfl

theorem cell23_8097360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 4, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 4, 1, 5, 4].length) (baseStart_8097360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8097360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8097360 prefixEnd_8097360 := by exact prefixLift 8097360
  have htrace : WordTrace (prefixWord ++ tailWord_8097360) baseStart_8097360 baseEnd_8097360 := by
    simpa [prefixWord, tailWord_8097360, baseEnd_8097360] using wordTrace_append hprefix tailTrace_8097360
  have hstable : (prefixWord ++ tailWord_8097360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8097360).length < 2 ^ (prefixWord ++ tailWord_8097360).sum := by decide
  have hdescent : baseEnd_8097360 < baseStart_8097360 := by decide
  rcases family_descends (prefixWord ++ tailWord_8097360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8097363 : List Nat := [1, 1, 1, 2, 1, 1, 2, 1, 6, 1, 6]
def baseStart_8097363 : Nat := 118140960795 + 8097363 * 2 ^ 59
def prefixEnd_8097363 : Nat := 4983230072969 + 3 ^ 40 * 8097363 * 2
def baseEnd_8097363 : Nat := 4157839252932507763723411

theorem tailTrace_8097363 : CollatzResearch.WordTrace tailWord_8097363 prefixEnd_8097363 4157839252932507763723411 := by
  unfold tailWord_8097363
  simp only [CollatzResearch.WordTrace]
  refine ⟨295335091363644245345664743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196890060909096163563776495 295335091363644245345664743)
  ·
    refine ⟨443002637045466368018497115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 295335091363644245345664743 443002637045466368018497115)
    ·
      refine ⟨664503955568199552027745673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 443002637045466368018497115 664503955568199552027745673)
      ·
        refine ⟨498377966676149664020809255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 664503955568199552027745673 498377966676149664020809255)
        ·
          refine ⟨747566950014224496031213883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 498377966676149664020809255 747566950014224496031213883)
          ·
            refine ⟨1121350425021336744046820825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 747566950014224496031213883 1121350425021336744046820825)
            ·
              refine ⟨841012818766002558035115619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1121350425021336744046820825 841012818766002558035115619)
              ·
                refine ⟨1261519228149003837052673429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 841012818766002558035115619 1261519228149003837052673429)
                ·
                  refine ⟨59133713819484554861844067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1261519228149003837052673429 59133713819484554861844067)
                  ·
                    refine ⟨88700570729226832292766101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 59133713819484554861844067 88700570729226832292766101)
                    ·
                      refine ⟨4157839252932507763723411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 88700570729226832292766101 4157839252932507763723411)
                      ·
                        rfl

theorem cell23_8097363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 1, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 1, 6, 1, 6].length) (baseStart_8097363 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8097363 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8097363 prefixEnd_8097363 := by exact prefixLift 8097363
  have htrace : WordTrace (prefixWord ++ tailWord_8097363) baseStart_8097363 baseEnd_8097363 := by
    simpa [prefixWord, tailWord_8097363, baseEnd_8097363] using wordTrace_append hprefix tailTrace_8097363
  have hstable : (prefixWord ++ tailWord_8097363).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8097363).length < 2 ^ (prefixWord ++ tailWord_8097363).sum := by decide
  have hdescent : baseEnd_8097363 < baseStart_8097363 := by decide
  rcases family_descends (prefixWord ++ tailWord_8097363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8097367 : List Nat := [1, 1, 3, 2, 2, 4, 2, 1, 2, 1, 4]
def baseStart_8097367 : Nat := 118140960795 + 8097367 * 2 ^ 59
def prefixEnd_8097367 : Nat := 4983230072969 + 3 ^ 40 * 8097367 * 2
def baseEnd_8097367 : Nat := 4157841306855125748073393

theorem tailTrace_8097367 : CollatzResearch.WordTrace tailWord_8097367 prefixEnd_8097367 4157841306855125748073393 := by
  unfold tailWord_8097367
  simp only [CollatzResearch.WordTrace]
  refine ⟨295335237255629754028810355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196890158170419836019206903 295335237255629754028810355)
  ·
    refine ⟨443002855883444631043215533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 295335237255629754028810355 443002855883444631043215533)
    ·
      refine ⟨166126070956291736641205825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 443002855883444631043215533 166126070956291736641205825)
      ·
        refine ⟨124594553217218802480904369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 166126070956291736641205825 124594553217218802480904369)
        ·
          refine ⟨93445914912914101860678277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 124594553217218802480904369 93445914912914101860678277)
          ·
            refine ⟨17521109046171394098877177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 93445914912914101860678277 17521109046171394098877177)
            ·
              refine ⟨13140831784628545574157883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17521109046171394098877177 13140831784628545574157883)
              ·
                refine ⟨19711247676942818361236825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13140831784628545574157883 19711247676942818361236825)
                ·
                  refine ⟨14783435757707113770927619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19711247676942818361236825 14783435757707113770927619)
                  ·
                    refine ⟨22175153636560670656391429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14783435757707113770927619 22175153636560670656391429)
                    ·
                      refine ⟨4157841306855125748073393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22175153636560670656391429 4157841306855125748073393)
                      ·
                        rfl

theorem cell23_8097367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 4, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 4, 2, 1, 2, 1, 4].length) (baseStart_8097367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8097367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8097367 prefixEnd_8097367 := by exact prefixLift 8097367
  have htrace : WordTrace (prefixWord ++ tailWord_8097367) baseStart_8097367 baseEnd_8097367 := by
    simpa [prefixWord, tailWord_8097367, baseEnd_8097367] using wordTrace_append hprefix tailTrace_8097367
  have hstable : (prefixWord ++ tailWord_8097367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8097367).length < 2 ^ (prefixWord ++ tailWord_8097367).sum := by decide
  have hdescent : baseEnd_8097367 < baseStart_8097367 := by decide
  rcases family_descends (prefixWord ++ tailWord_8097367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8097370 : List Nat := [3, 1, 1, 2, 1, 1, 1, 5, 1, 4, 3]
def baseStart_8097370 : Nat := 118140960795 + 8097370 * 2 ^ 59
def prefixEnd_8097370 : Nat := 4983230072969 + 3 ^ 40 * 8097370 * 2
def baseEnd_8097370 : Nat := 4157842847297089236335879

theorem tailTrace_8097370 : CollatzResearch.WordTrace tailWord_8097370 prefixEnd_8097370 4157842847297089236335879 := by
  unfold tailWord_8097370
  simp only [CollatzResearch.WordTrace]
  refine ⟨73833836668654721385292391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 196890231116412590360779709 73833836668654721385292391)
  ·
    refine ⟨110750755002982082077938587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73833836668654721385292391 110750755002982082077938587)
    ·
      refine ⟨166126132504473123116907881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110750755002982082077938587 166126132504473123116907881)
      ·
        refine ⟨124594599378354842337680911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 166126132504473123116907881 124594599378354842337680911)
        ·
          refine ⟨186891899067532263506521367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124594599378354842337680911 186891899067532263506521367)
          ·
            refine ⟨280337848601298395259782051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 186891899067532263506521367 280337848601298395259782051)
            ·
              refine ⟨420506772901947592889673077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 280337848601298395259782051 420506772901947592889673077)
              ·
                refine ⟨39422509959557586833406851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 420506772901947592889673077 39422509959557586833406851)
                ·
                  refine ⟨59133764939336380250110277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39422509959557586833406851 59133764939336380250110277)
                  ·
                    refine ⟨11087580926125571296895677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 59133764939336380250110277 11087580926125571296895677)
                    ·
                      refine ⟨4157842847297089236335879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11087580926125571296895677 4157842847297089236335879)
                      ·
                        rfl

theorem cell23_8097370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 5, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 5, 1, 4, 3].length) (baseStart_8097370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8097370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8097370 prefixEnd_8097370 := by exact prefixLift 8097370
  have htrace : WordTrace (prefixWord ++ tailWord_8097370) baseStart_8097370 baseEnd_8097370 := by
    simpa [prefixWord, tailWord_8097370, baseEnd_8097370] using wordTrace_append hprefix tailTrace_8097370
  have hstable : (prefixWord ++ tailWord_8097370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8097370).length < 2 ^ (prefixWord ++ tailWord_8097370).sum := by decide
  have hdescent : baseEnd_8097370 < baseStart_8097370 := by decide
  rcases family_descends (prefixWord ++ tailWord_8097370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8097417 : List Nat := [1, 2, 1, 1, 4, 1, 3, 1, 5, 1, 3]
def baseStart_8097417 : Nat := 118140960795 + 8097417 * 2 ^ 59
def prefixEnd_8097417 : Nat := 4983230072969 + 3 ^ 40 * 8097417 * 2
def baseEnd_8097417 : Nat := 4157866980887850552448163

theorem tailTrace_8097417 : CollatzResearch.WordTrace tailWord_8097417 prefixEnd_8097417 4157866980887850552448163 := by
  unfold tailWord_8097417
  simp only [CollatzResearch.WordTrace]
  refine ⟨295337060905448612568130505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196891373936965741712087003 295337060905448612568130505)
  ·
    refine ⟨221502795679086459426097879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 295337060905448612568130505 221502795679086459426097879)
    ·
      refine ⟨332254193518629689139146819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 221502795679086459426097879 332254193518629689139146819)
      ·
        refine ⟨498381290277944533708720229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 332254193518629689139146819 498381290277944533708720229)
        ·
          refine ⟨93446491927114600070385043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 498381290277944533708720229 93446491927114600070385043)
          ·
            refine ⟨140169737890671900105577565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93446491927114600070385043 140169737890671900105577565)
            ·
              refine ⟨52563651709001962539591587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 140169737890671900105577565 52563651709001962539591587)
              ·
                refine ⟨78845477563502943809387381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52563651709001962539591587 78845477563502943809387381)
                ·
                  refine ⟨7391763521578400982130067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 78845477563502943809387381 7391763521578400982130067)
                  ·
                    refine ⟨11087645282367601473195101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7391763521578400982130067 11087645282367601473195101)
                    ·
                      refine ⟨4157866980887850552448163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11087645282367601473195101 4157866980887850552448163)
                      ·
                        rfl

theorem cell23_8097417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 3, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 3, 1, 5, 1, 3].length) (baseStart_8097417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8097417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8097417 prefixEnd_8097417 := by exact prefixLift 8097417
  have htrace : WordTrace (prefixWord ++ tailWord_8097417) baseStart_8097417 baseEnd_8097417 := by
    simpa [prefixWord, tailWord_8097417, baseEnd_8097417] using wordTrace_append hprefix tailTrace_8097417
  have hstable : (prefixWord ++ tailWord_8097417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8097417).length < 2 ^ (prefixWord ++ tailWord_8097417).sum := by decide
  have hdescent : baseEnd_8097417 < baseStart_8097417 := by decide
  rcases family_descends (prefixWord ++ tailWord_8097417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8097420 : List Nat := [2, 2, 1, 2, 1, 1, 3, 3, 3, 5]
def baseStart_8097420 : Nat := 118140960795 + 8097420 * 2 ^ 59
def prefixEnd_8097420 : Nat := 4983230072969 + 3 ^ 40 * 8097420 * 2
def baseEnd_8097420 : Nat := 1385956173776604680236883

theorem tailTrace_8097420 : CollatzResearch.WordTrace tailWord_8097420 prefixEnd_8097420 1385956173776604680236883 := by
  unfold tailWord_8097420
  simp only [CollatzResearch.WordTrace]
  refine ⟨147668585162218872040244857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196891446882958496053659809 147668585162218872040244857)
  ·
    refine ⟨110751438871664154030183643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147668585162218872040244857 110751438871664154030183643)
    ·
      refine ⟨166127158307496231045275465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110751438871664154030183643 166127158307496231045275465)
      ·
        refine ⟨124595368730622173283956599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 166127158307496231045275465 124595368730622173283956599)
        ·
          refine ⟨186893053095933259925934899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124595368730622173283956599 186893053095933259925934899)
          ·
            refine ⟨280339579643899889888902349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 186893053095933259925934899 280339579643899889888902349)
            ·
              refine ⟨105127342366462458708338381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 280339579643899889888902349 105127342366462458708338381)
              ·
                refine ⟨39422753387423422015626893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 105127342366462458708338381 39422753387423422015626893)
                ·
                  refine ⟨14783532520283783255860085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39422753387423422015626893 14783532520283783255860085)
                  ·
                    refine ⟨1385956173776604680236883, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14783532520283783255860085 1385956173776604680236883)
                    ·
                      rfl

theorem cell23_8097420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 3, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 3, 3, 3, 5].length) (baseStart_8097420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8097420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8097420 prefixEnd_8097420 := by exact prefixLift 8097420
  have htrace : WordTrace (prefixWord ++ tailWord_8097420) baseStart_8097420 baseEnd_8097420 := by
    simpa [prefixWord, tailWord_8097420, baseEnd_8097420] using wordTrace_append hprefix tailTrace_8097420
  have hstable : (prefixWord ++ tailWord_8097420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8097420).length < 2 ^ (prefixWord ++ tailWord_8097420).sum := by decide
  have hdescent : baseEnd_8097420 < baseStart_8097420 := by decide
  rcases family_descends (prefixWord ++ tailWord_8097420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8097428 : List Nat := [2, 4, 2, 2, 2, 1, 2, 3, 1, 4]
def baseStart_8097428 : Nat := 118140960795 + 8097428 * 2 ^ 59
def prefixEnd_8097428 : Nat := 4983230072969 + 3 ^ 40 * 8097428 * 2
def baseEnd_8097428 : Nat := 1385957543058350003136871

theorem tailTrace_8097428 : CollatzResearch.WordTrace tailWord_8097428 prefixEnd_8097428 1385957543058350003136871 := by
  unfold tailWord_8097428
  simp only [CollatzResearch.WordTrace]
  refine ⟨147668731054204380723390469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196891641405605840964520625 147668731054204380723390469)
  ·
    refine ⟨27687887072663321385635713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 147668731054204380723390469 27687887072663321385635713)
    ·
      refine ⟨20765915304497491039226785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27687887072663321385635713 20765915304497491039226785)
      ·
        refine ⟨15574436478373118279420089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20765915304497491039226785 15574436478373118279420089)
        ·
          refine ⟨11680827358779838709565067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15574436478373118279420089 11680827358779838709565067)
          ·
            refine ⟨17521241038169758064347601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11680827358779838709565067 17521241038169758064347601)
            ·
              refine ⟨13140930778627318548260701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17521241038169758064347601 13140930778627318548260701)
              ·
                refine ⟨4927849041985244455597763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13140930778627318548260701 4927849041985244455597763)
                ·
                  refine ⟨7391773562977866683396645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4927849041985244455597763 7391773562977866683396645)
                  ·
                    refine ⟨1385957543058350003136871, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7391773562977866683396645 1385957543058350003136871)
                    ·
                      rfl

theorem cell23_8097428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 1, 2, 3, 1, 4].length) (baseStart_8097428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8097428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8097428 prefixEnd_8097428 := by exact prefixLift 8097428
  have htrace : WordTrace (prefixWord ++ tailWord_8097428) baseStart_8097428 baseEnd_8097428 := by
    simpa [prefixWord, tailWord_8097428, baseEnd_8097428] using wordTrace_append hprefix tailTrace_8097428
  have hstable : (prefixWord ++ tailWord_8097428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8097428).length < 2 ^ (prefixWord ++ tailWord_8097428).sum := by decide
  have hdescent : baseEnd_8097428 < baseStart_8097428 := by decide
  rcases family_descends (prefixWord ++ tailWord_8097428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8097467 : List Nat := [1, 1, 1, 1, 1, 2, 3, 7, 2, 4]
def baseStart_8097467 : Nat := 118140960795 + 8097467 * 2 ^ 59
def prefixEnd_8097467 : Nat := 4983230072969 + 3 ^ 40 * 8097467 * 2
def baseEnd_8097467 : Nat := 1385964218306858452274311

theorem tailTrace_8097467 : CollatzResearch.WordTrace tailWord_8097467 prefixEnd_8097467 1385964218306858452274311 := by
  unfold tailWord_8097467
  simp only [CollatzResearch.WordTrace]
  refine ⟨295338884555267471107450655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196892589703511647404967103 295338884555267471107450655)
  ·
    refine ⟨443008326832901206661175983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 295338884555267471107450655 443008326832901206661175983)
    ·
      refine ⟨664512490249351809991763975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 443008326832901206661175983 664512490249351809991763975)
      ·
        refine ⟨996768735374027714987645963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 664512490249351809991763975 996768735374027714987645963)
        ·
          refine ⟨1495153103061041572481468945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 996768735374027714987645963 1495153103061041572481468945)
          ·
            refine ⟨1121364827295781179361101709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1495153103061041572481468945 1121364827295781179361101709)
            ·
              refine ⟨420511810235917942260413141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1121364827295781179361101709 420511810235917942260413141)
              ·
                refine ⟨9855745552404326771728433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 420511810235917942260413141 9855745552404326771728433)
                ·
                  refine ⟨7391809164303245078796325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9855745552404326771728433 7391809164303245078796325)
                  ·
                    refine ⟨1385964218306858452274311, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7391809164303245078796325 1385964218306858452274311)
                    ·
                      rfl

theorem cell23_8097467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 7, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 7, 2, 4].length) (baseStart_8097467 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8097467 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8097467 prefixEnd_8097467 := by exact prefixLift 8097467
  have htrace : WordTrace (prefixWord ++ tailWord_8097467) baseStart_8097467 baseEnd_8097467 := by
    simpa [prefixWord, tailWord_8097467, baseEnd_8097467] using wordTrace_append hprefix tailTrace_8097467
  have hstable : (prefixWord ++ tailWord_8097467).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8097467).length < 2 ^ (prefixWord ++ tailWord_8097467).sum := by decide
  have hdescent : baseEnd_8097467 < baseStart_8097467 := by decide
  rcases family_descends (prefixWord ++ tailWord_8097467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8097478 : List Nat := [6, 1, 2, 1, 1, 1, 2, 1, 1, 5, 2]
def baseStart_8097478 : Nat := 118140960795 + 8097478 * 2 ^ 59
def prefixEnd_8097478 : Nat := 4983230072969 + 3 ^ 40 * 8097478 * 2
def baseEnd_8097478 : Nat := 4157898303207774813785383

theorem tailTrace_8097478 : CollatzResearch.WordTrace tailWord_8097478 prefixEnd_8097478 4157898303207774813785383 := by
  unfold tailWord_8097478
  simp only [CollatzResearch.WordTrace]
  refine ⟨9229352679944613124565659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 196892857172151746657400725 9229352679944613124565659)
  ·
    refine ⟨13844029019916919686848489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9229352679944613124565659 13844029019916919686848489)
    ·
      refine ⟨10383021764937689765136367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13844029019916919686848489 10383021764937689765136367)
      ·
        refine ⟨15574532647406534647704551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10383021764937689765136367 15574532647406534647704551)
        ·
          refine ⟨23361798971109801971556827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15574532647406534647704551 23361798971109801971556827)
          ·
            refine ⟨35042698456664702957335241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23361798971109801971556827 35042698456664702957335241)
            ·
              refine ⟨26282023842498527218001431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35042698456664702957335241 26282023842498527218001431)
              ·
                refine ⟨39423035763747790827002147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26282023842498527218001431 39423035763747790827002147)
                ·
                  refine ⟨59134553645621686240503221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39423035763747790827002147 59134553645621686240503221)
                  ·
                    refine ⟨5543864404277033085047177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 59134553645621686240503221 5543864404277033085047177)
                    ·
                      refine ⟨4157898303207774813785383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5543864404277033085047177 4157898303207774813785383)
                      ·
                        rfl

theorem cell23_8097478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 2, 1, 1, 5, 2].length) (baseStart_8097478 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8097478 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8097478 prefixEnd_8097478 := by exact prefixLift 8097478
  have htrace : WordTrace (prefixWord ++ tailWord_8097478) baseStart_8097478 baseEnd_8097478 := by
    simpa [prefixWord, tailWord_8097478, baseEnd_8097478] using wordTrace_append hprefix tailTrace_8097478
  have hstable : (prefixWord ++ tailWord_8097478).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8097478).length < 2 ^ (prefixWord ++ tailWord_8097478).sum := by decide
  have hdescent : baseEnd_8097478 < baseStart_8097478 := by decide
  rcases family_descends (prefixWord ++ tailWord_8097478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8097480 : List Nat := [2, 1, 3, 1, 2, 2, 3, 9]
def baseStart_8097480 : Nat := 118140960795 + 8097480 * 2 ^ 59
def prefixEnd_8097480 : Nat := 4983230072969 + 3 ^ 40 * 8097480 * 2
def baseEnd_8097480 : Nat := 153996271487743844665199

theorem tailTrace_8097480 : CollatzResearch.WordTrace tailWord_8097480 prefixEnd_8097480 153996271487743844665199 := by
  unfold tailWord_8097480
  simp only [CollatzResearch.WordTrace]
  refine ⟨147669679352110187163836947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196892905802813582885115929 147669679352110187163836947)
  ·
    refine ⟨221504519028165280745755421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147669679352110187163836947 221504519028165280745755421)
    ·
      refine ⟨83064194635561980279658283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 221504519028165280745755421 83064194635561980279658283)
      ·
        refine ⟨124596291953342970419487425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83064194635561980279658283 124596291953342970419487425)
        ·
          refine ⟨93447218965007227814615569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 124596291953342970419487425 93447218965007227814615569)
          ·
            refine ⟨70085414223755420860961677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 93447218965007227814615569 70085414223755420860961677)
            ·
              refine ⟨26282030333908282822860629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 70085414223755420860961677 26282030333908282822860629)
              ·
                refine ⟨153996271487743844665199, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 26282030333908282822860629 153996271487743844665199)
                ·
                  rfl

theorem cell23_8097480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 3, 9].length) (baseStart_8097480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8097480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8097480 prefixEnd_8097480 := by exact prefixLift 8097480
  have htrace : WordTrace (prefixWord ++ tailWord_8097480) baseStart_8097480 baseEnd_8097480 := by
    simpa [prefixWord, tailWord_8097480, baseEnd_8097480] using wordTrace_append hprefix tailTrace_8097480
  have hstable : (prefixWord ++ tailWord_8097480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8097480).length < 2 ^ (prefixWord ++ tailWord_8097480).sum := by decide
  have hdescent : baseEnd_8097480 < baseStart_8097480 := by decide
  rcases family_descends (prefixWord ++ tailWord_8097480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8097485 : List Nat := [1, 6, 2, 1, 1, 1, 3, 3, 1, 1, 3]
def baseStart_8097485 : Nat := 118140960795 + 8097485 * 2 ^ 59
def prefixEnd_8097485 : Nat := 4983230072969 + 3 ^ 40 * 8097485 * 2
def baseEnd_8097485 : Nat := 4157901897572356286397851

theorem tailTrace_8097485 : CollatzResearch.WordTrace tailWord_8097485 prefixEnd_8097485 4157901897572356286397851 := by
  unfold tailWord_8097485
  simp only [CollatzResearch.WordTrace]
  refine ⟨295339541069202260181605909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196893027379468173454403939 295339541069202260181605909)
  ·
    refine ⟨13844040987618855946012777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 295339541069202260181605909 13844040987618855946012777)
    ·
      refine ⟨10383030740714141959509583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13844040987618855946012777 10383030740714141959509583)
      ·
        refine ⟨15574546111071212939264375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10383030740714141959509583 15574546111071212939264375)
        ·
          refine ⟨23361819166606819408896563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15574546111071212939264375 23361819166606819408896563)
          ·
            refine ⟨35042728749910229113344845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23361819166606819408896563 35042728749910229113344845)
            ·
              refine ⟨13141023281216335917504317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35042728749910229113344845 13141023281216335917504317)
              ·
                refine ⟨4927883730456125969064119, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13141023281216335917504317 4927883730456125969064119)
                ·
                  refine ⟨7391825595684188953596179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4927883730456125969064119 7391825595684188953596179)
                  ·
                    refine ⟨11087738393526283430394269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7391825595684188953596179 11087738393526283430394269)
                    ·
                      refine ⟨4157901897572356286397851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11087738393526283430394269 4157901897572356286397851)
                      ·
                        rfl

theorem cell23_8097485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 3, 3, 1, 1, 3].length) (baseStart_8097485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8097485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8097485 prefixEnd_8097485 := by exact prefixLift 8097485
  have htrace : WordTrace (prefixWord ++ tailWord_8097485) baseStart_8097485 baseEnd_8097485 := by
    simpa [prefixWord, tailWord_8097485, baseEnd_8097485] using wordTrace_append hprefix tailTrace_8097485
  have hstable : (prefixWord ++ tailWord_8097485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8097485).length < 2 ^ (prefixWord ++ tailWord_8097485).sum := by decide
  have hdescent : baseEnd_8097485 < baseStart_8097485 := by decide
  rcases family_descends (prefixWord ++ tailWord_8097485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8097520 : List Nat := [2, 1, 1, 1, 3, 1, 2, 2, 1, 4, 5]
def baseStart_8097520 : Nat := 118140960795 + 8097520 * 2 ^ 59
def prefixEnd_8097520 : Nat := 4983230072969 + 3 ^ 40 * 8097520 * 2
def baseEnd_8097520 : Nat := 4157919869395263649460189

theorem tailTrace_8097520 : CollatzResearch.WordTrace tailWord_8097520 prefixEnd_8097520 4157919869395263649460189 := by
  unfold tailWord_8097520
  simp only [CollatzResearch.WordTrace]
  refine ⟨147670408812037730579565007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196893878416050307439420009 147670408812037730579565007)
  ·
    refine ⟨221505613218056595869347511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147670408812037730579565007 221505613218056595869347511)
    ·
      refine ⟨332258419827084893804021267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 221505613218056595869347511 332258419827084893804021267)
      ·
        refine ⟨498387629740627340706031901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 332258419827084893804021267 498387629740627340706031901)
        ·
          refine ⟨186895361152735252764761963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 498387629740627340706031901 186895361152735252764761963)
          ·
            refine ⟨280343041729102879147142945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 186895361152735252764761963 280343041729102879147142945)
            ·
              refine ⟨210257281296827159360357209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 280343041729102879147142945 210257281296827159360357209)
              ·
                refine ⟨157692960972620369520267907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 210257281296827159360357209 157692960972620369520267907)
                ·
                  refine ⟨236539441458930554280401861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 157692960972620369520267907 236539441458930554280401861)
                  ·
                    refine ⟨44351145273549478927575349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 236539441458930554280401861 44351145273549478927575349)
                    ·
                      refine ⟨4157919869395263649460189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44351145273549478927575349 4157919869395263649460189)
                      ·
                        rfl

theorem cell23_8097520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 2, 1, 4, 5].length) (baseStart_8097520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8097520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8097520 prefixEnd_8097520 := by exact prefixLift 8097520
  have htrace : WordTrace (prefixWord ++ tailWord_8097520) baseStart_8097520 baseEnd_8097520 := by
    simpa [prefixWord, tailWord_8097520, baseEnd_8097520] using wordTrace_append hprefix tailTrace_8097520
  have hstable : (prefixWord ++ tailWord_8097520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8097520).length < 2 ^ (prefixWord ++ tailWord_8097520).sum := by decide
  have hdescent : baseEnd_8097520 < baseStart_8097520 := by decide
  rcases family_descends (prefixWord ++ tailWord_8097520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8097530 : List Nat := [3, 1, 1, 1, 1, 3, 1, 1, 1, 2, 8]
def baseStart_8097530 : Nat := 118140960795 + 8097530 * 2 ^ 59
def prefixEnd_8097530 : Nat := 4983230072969 + 3 ^ 40 * 8097530 * 2
def baseEnd_8097530 : Nat := 4157925004201808610335143

theorem tailTrace_8097530 : CollatzResearch.WordTrace tailWord_8097530 prefixEnd_8097530 4157925004201808610335143 := by
  unfold tailWord_8097530
  simp only [CollatzResearch.WordTrace]
  refine ⟨73835295588509808216748511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 196894121569359488577996029 73835295588509808216748511)
  ·
    refine ⟨110752943382764712325122767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73835295588509808216748511 110752943382764712325122767)
    ·
      refine ⟨166129415074147068487684151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110752943382764712325122767 166129415074147068487684151)
      ·
        refine ⟨249194122611220602731526227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166129415074147068487684151 249194122611220602731526227)
        ·
          refine ⟨373791183916830904097289341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 249194122611220602731526227 373791183916830904097289341)
          ·
            refine ⟨140171693968811589036483503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 373791183916830904097289341 140171693968811589036483503)
            ·
              refine ⟨210257540953217383554725255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 140171693968811589036483503 210257540953217383554725255)
              ·
                refine ⟨315386311429826075332087883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 210257540953217383554725255 315386311429826075332087883)
                ·
                  refine ⟨473079467144739112998131825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 315386311429826075332087883 473079467144739112998131825)
                  ·
                    refine ⟨354809600358554334748598869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 473079467144739112998131825 354809600358554334748598869)
                    ·
                      refine ⟨4157925004201808610335143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 354809600358554334748598869 4157925004201808610335143)
                      ·
                        rfl

theorem cell23_8097530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 1, 1, 2, 8].length) (baseStart_8097530 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8097530 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8097530 prefixEnd_8097530 := by exact prefixLift 8097530
  have htrace : WordTrace (prefixWord ++ tailWord_8097530) baseStart_8097530 baseEnd_8097530 := by
    simpa [prefixWord, tailWord_8097530, baseEnd_8097530] using wordTrace_append hprefix tailTrace_8097530
  have hstable : (prefixWord ++ tailWord_8097530).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8097530).length < 2 ^ (prefixWord ++ tailWord_8097530).sum := by decide
  have hdescent : baseEnd_8097530 < baseStart_8097530 := by decide
  rcases family_descends (prefixWord ++ tailWord_8097530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8097564 : List Nat := [2, 2, 3, 1, 1, 2, 1, 2, 3, 4, 2]
def baseStart_8097564 : Nat := 118140960795 + 8097564 * 2 ^ 59
def prefixEnd_8097564 : Nat := 4983230072969 + 3 ^ 40 * 8097564 * 2
def baseEnd_8097564 : Nat := 4157942462544061477309987

theorem tailTrace_8097564 : CollatzResearch.WordTrace tailWord_8097564 prefixEnd_8097564 4157942462544061477309987 := by
  unfold tailWord_8097564
  simp only [CollatzResearch.WordTrace]
  refine ⟨147671211217958028336865873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196894948290610704449154497 147671211217958028336865873)
  ·
    refine ⟨110753408413468521252649405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147671211217958028336865873 110753408413468521252649405)
    ·
      refine ⟨41532528155050695469743527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 110753408413468521252649405 41532528155050695469743527)
      ·
        refine ⟨62298792232576043204615291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41532528155050695469743527 62298792232576043204615291)
        ·
          refine ⟨93448188348864064806922937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62298792232576043204615291 93448188348864064806922937)
          ·
            refine ⟨70086141261648048605192203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 93448188348864064806922937 70086141261648048605192203)
            ·
              refine ⟨105129211892472072907788305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70086141261648048605192203 105129211892472072907788305)
              ·
                refine ⟨78846908919354054680841229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 105129211892472072907788305 78846908919354054680841229)
                ·
                  refine ⟨29567590844757770505315461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 78846908919354054680841229 29567590844757770505315461)
                  ·
                    refine ⟨5543923283392081969746649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29567590844757770505315461 5543923283392081969746649)
                    ·
                      refine ⟨4157942462544061477309987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5543923283392081969746649 4157942462544061477309987)
                      ·
                        rfl

theorem cell23_8097564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 1, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 1, 2, 3, 4, 2].length) (baseStart_8097564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8097564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8097564 prefixEnd_8097564 := by exact prefixLift 8097564
  have htrace : WordTrace (prefixWord ++ tailWord_8097564) baseStart_8097564 baseEnd_8097564 := by
    simpa [prefixWord, tailWord_8097564, baseEnd_8097564] using wordTrace_append hprefix tailTrace_8097564
  have hstable : (prefixWord ++ tailWord_8097564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8097564).length < 2 ^ (prefixWord ++ tailWord_8097564).sum := by decide
  have hdescent : baseEnd_8097564 < baseStart_8097564 := by decide
  rcases family_descends (prefixWord ++ tailWord_8097564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8097567 : List Nat := [1, 1, 2, 4, 2, 1, 1, 1, 1, 6, 3]
def baseStart_8097567 : Nat := 118140960795 + 8097567 * 2 ^ 59
def prefixEnd_8097567 : Nat := 4983230072969 + 3 ^ 40 * 8097567 * 2
def baseEnd_8097567 : Nat := 4157944002986024965572473

theorem tailTrace_8097567 : CollatzResearch.WordTrace tailWord_8097567 prefixEnd_8097567 4157944002986024965572473 := by
  unfold tailWord_8097567
  simp only [CollatzResearch.WordTrace]
  refine ⟨295342531854905188186090955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196895021236603458790727303 295342531854905188186090955)
  ·
    refine ⟨443013797782357782279136433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 295342531854905188186090955 443013797782357782279136433)
    ·
      refine ⟨332260348336768336709352325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 443013797782357782279136433 332260348336768336709352325)
      ·
        refine ⟨62298815313144063133003561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 332260348336768336709352325 62298815313144063133003561)
        ·
          refine ⟨46724111484858047349752671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62298815313144063133003561 46724111484858047349752671)
          ·
            refine ⟨70086167227287071024629007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46724111484858047349752671 70086167227287071024629007)
            ·
              refine ⟨105129250840930606536943511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70086167227287071024629007 105129250840930606536943511)
              ·
                refine ⟨157693876261395909805415267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 105129250840930606536943511 157693876261395909805415267)
                ·
                  refine ⟨236540814392093864708122901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 157693876261395909805415267 236540814392093864708122901)
                  ·
                    refine ⟨11087850674629399908193261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 236540814392093864708122901 11087850674629399908193261)
                    ·
                      refine ⟨4157944002986024965572473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11087850674629399908193261 4157944002986024965572473)
                      ·
                        rfl

theorem cell23_8097567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 1, 1, 1, 6, 3].length) (baseStart_8097567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8097567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8097567 prefixEnd_8097567 := by exact prefixLift 8097567
  have htrace : WordTrace (prefixWord ++ tailWord_8097567) baseStart_8097567 baseEnd_8097567 := by
    simpa [prefixWord, tailWord_8097567, baseEnd_8097567] using wordTrace_append hprefix tailTrace_8097567
  have hstable : (prefixWord ++ tailWord_8097567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8097567).length < 2 ^ (prefixWord ++ tailWord_8097567).sum := by decide
  have hdescent : baseEnd_8097567 < baseStart_8097567 := by decide
  rcases family_descends (prefixWord ++ tailWord_8097567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8097634 : List Nat := [3, 3, 2, 1, 2, 1, 1, 2, 1, 7]
def baseStart_8097634 : Nat := 118140960795 + 8097634 * 2 ^ 59
def prefixEnd_8097634 : Nat := 4983230072969 + 3 ^ 40 * 8097634 * 2
def baseEnd_8097634 : Nat := 1385992802063292067811555

theorem tailTrace_8097634 : CollatzResearch.WordTrace tailWord_8097634 prefixEnd_8097634 1385992802063292067811555 := by
  unfold tailWord_8097634
  simp only [CollatzResearch.WordTrace]
  refine ⟨73836243886415614657194989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 196896650363774972419186637 73836243886415614657194989)
  ·
    refine ⟨27688591457405855496448121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73836243886415614657194989 27688591457405855496448121)
    ·
      refine ⟨20766443593054391622336091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27688591457405855496448121 20766443593054391622336091)
      ·
        refine ⟨31149665389581587433504137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20766443593054391622336091 31149665389581587433504137)
        ·
          refine ⟨23362249042186190575128103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31149665389581587433504137 23362249042186190575128103)
          ·
            refine ⟨35043373563279285862692155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23362249042186190575128103 35043373563279285862692155)
            ·
              refine ⟨52565060344918928794038233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35043373563279285862692155 52565060344918928794038233)
              ·
                refine ⟨39423795258689196595528675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52565060344918928794038233 39423795258689196595528675)
                ·
                  refine ⟨59135692888033794893293013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39423795258689196595528675 59135692888033794893293013)
                  ·
                    refine ⟨1385992802063292067811555, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 59135692888033794893293013 1385992802063292067811555)
                    ·
                      rfl

theorem cell23_8097634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 1, 2, 1, 7].length) (baseStart_8097634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8097634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8097634 prefixEnd_8097634 := by exact prefixLift 8097634
  have htrace : WordTrace (prefixWord ++ tailWord_8097634) baseStart_8097634 baseEnd_8097634 := by
    simpa [prefixWord, tailWord_8097634, baseEnd_8097634] using wordTrace_append hprefix tailTrace_8097634
  have hstable : (prefixWord ++ tailWord_8097634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8097634).length < 2 ^ (prefixWord ++ tailWord_8097634).sum := by decide
  have hdescent : baseEnd_8097634 < baseStart_8097634 := by decide
  rcases family_descends (prefixWord ++ tailWord_8097634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8097671 : List Nat := [1, 1, 4, 2, 4, 1, 1, 2, 2, 1, 4]
def baseStart_8097671 : Nat := 118140960795 + 8097671 * 2 ^ 59
def prefixEnd_8097671 : Nat := 4983230072969 + 3 ^ 40 * 8097671 * 2
def baseEnd_8097671 : Nat := 4157997404974092558671995

theorem tailTrace_8097671 : CollatzResearch.WordTrace tailWord_8097671 prefixEnd_8097671 4157997404974092558671995 := by
  unfold tailWord_8097671
  simp only [CollatzResearch.WordTrace]
  refine ⟨295346325046528413947876867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196897550031018942631917911 295346325046528413947876867)
  ·
    refine ⟨443019487569792620921815301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 295346325046528413947876867 443019487569792620921815301)
    ·
      refine ⟨83066153919336116422840369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 443019487569792620921815301 83066153919336116422840369)
      ·
        refine ⟨62299615439502087317130277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83066153919336116422840369 62299615439502087317130277)
        ·
          refine ⟨11681177894906641371961927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 62299615439502087317130277 11681177894906641371961927)
          ·
            refine ⟨17521766842359962057942891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11681177894906641371961927 17521766842359962057942891)
            ·
              refine ⟨26282650263539943086914337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17521766842359962057942891 26282650263539943086914337)
              ·
                refine ⟨19711987697654957315185753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26282650263539943086914337 19711987697654957315185753)
                ·
                  refine ⟨14783990773241217986389315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19711987697654957315185753 14783990773241217986389315)
                  ·
                    refine ⟨22175986159861826979583973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14783990773241217986389315 22175986159861826979583973)
                    ·
                      refine ⟨4157997404974092558671995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22175986159861826979583973 4157997404974092558671995)
                      ·
                        rfl

theorem cell23_8097671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 1, 1, 2, 2, 1, 4].length) (baseStart_8097671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8097671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8097671 prefixEnd_8097671 := by exact prefixLift 8097671
  have htrace : WordTrace (prefixWord ++ tailWord_8097671) baseStart_8097671 baseEnd_8097671 := by
    simpa [prefixWord, tailWord_8097671, baseEnd_8097671] using wordTrace_append hprefix tailTrace_8097671
  have hstable : (prefixWord ++ tailWord_8097671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8097671).length < 2 ^ (prefixWord ++ tailWord_8097671).sum := by decide
  have hdescent : baseEnd_8097671 < baseStart_8097671 := by decide
  rcases family_descends (prefixWord ++ tailWord_8097671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8097681 : List Nat := [1, 2, 2, 1, 1, 1, 4, 6, 1, 4]
def baseStart_8097681 : Nat := 118140960795 + 8097681 * 2 ^ 59
def prefixEnd_8097681 : Nat := 4983230072969 + 3 ^ 40 * 8097681 * 2
def baseEnd_8097681 : Nat := 1386000846593545839848983

theorem tailTrace_8097681 : CollatzResearch.WordTrace tailWord_8097681 prefixEnd_8097681 1386000846593545839848983 := by
  unfold tailWord_8097681
  simp only [CollatzResearch.WordTrace]
  refine ⟨295346689776492185655740897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196897793184328123770493931 295346689776492185655740897)
  ·
    refine ⟨221510017332369139241805673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 295346689776492185655740897 221510017332369139241805673)
    ·
      refine ⟨166132512999276854431354255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 221510017332369139241805673 166132512999276854431354255)
      ·
        refine ⟨249198769498915281647031383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166132512999276854431354255 249198769498915281647031383)
        ·
          refine ⟨373798154248372922470547075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 249198769498915281647031383 373798154248372922470547075)
          ·
            refine ⟨560697231372559383705820613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 373798154248372922470547075 560697231372559383705820613)
            ·
              refine ⟨105130730882354884444841365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 560697231372559383705820613 105130730882354884444841365)
              ·
                refine ⟨4928003010110385208351939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 105130730882354884444841365 4928003010110385208351939)
                ·
                  refine ⟨7392004515165577812527909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4928003010110385208351939 7392004515165577812527909)
                  ·
                    refine ⟨1386000846593545839848983, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7392004515165577812527909 1386000846593545839848983)
                    ·
                      rfl

theorem cell23_8097681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 4, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 4, 6, 1, 4].length) (baseStart_8097681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8097681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8097681 prefixEnd_8097681 := by exact prefixLift 8097681
  have htrace : WordTrace (prefixWord ++ tailWord_8097681) baseStart_8097681 baseEnd_8097681 := by
    simpa [prefixWord, tailWord_8097681, baseEnd_8097681] using wordTrace_append hprefix tailTrace_8097681
  have hstable : (prefixWord ++ tailWord_8097681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8097681).length < 2 ^ (prefixWord ++ tailWord_8097681).sum := by decide
  have hdescent : baseEnd_8097681 < baseStart_8097681 := by decide
  rcases family_descends (prefixWord ++ tailWord_8097681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8097744 : List Nat := [2, 1, 1, 1, 1, 2, 5, 2, 3, 1, 4]
def baseStart_8097744 : Nat := 118140960795 + 8097744 * 2 ^ 59
def prefixEnd_8097744 : Nat := 4983230072969 + 3 ^ 40 * 8097744 * 2
def baseEnd_8097744 : Nat := 4158034889061870773059159

theorem tailTrace_8097744 : CollatzResearch.WordTrace tailWord_8097744 prefixEnd_8097744 4158034889061870773059159 := by
  unfold tailWord_8097744
  simp only [CollatzResearch.WordTrace]
  refine ⟨147674493787631973707642143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196899325050175964943522857 147674493787631973707642143)
  ·
    refine ⟨221511740681447960561463215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147674493787631973707642143 221511740681447960561463215)
    ·
      refine ⟨332267611022171940842194823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 221511740681447960561463215 332267611022171940842194823)
      ·
        refine ⟨498401416533257911263292235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 332267611022171940842194823 498401416533257911263292235)
        ·
          refine ⟨747602124799886866894938353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 498401416533257911263292235 747602124799886866894938353)
          ·
            refine ⟨560701593599915150171203765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 747602124799886866894938353 560701593599915150171203765)
            ·
              refine ⟨52565774399992045328550353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 560701593599915150171203765 52565774399992045328550353)
              ·
                refine ⟨39424330799994033996412765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52565774399992045328550353 39424330799994033996412765)
                ·
                  refine ⟨14784124049997762748654787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39424330799994033996412765 14784124049997762748654787)
                  ·
                    refine ⟨22176186074996644122982181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14784124049997762748654787 22176186074996644122982181)
                    ·
                      refine ⟨4158034889061870773059159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22176186074996644122982181 4158034889061870773059159)
                      ·
                        rfl

theorem cell23_8097744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 5, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 5, 2, 3, 1, 4].length) (baseStart_8097744 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8097744 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8097744 prefixEnd_8097744 := by exact prefixLift 8097744
  have htrace : WordTrace (prefixWord ++ tailWord_8097744) baseStart_8097744 baseEnd_8097744 := by
    simpa [prefixWord, tailWord_8097744, baseEnd_8097744] using wordTrace_append hprefix tailTrace_8097744
  have hstable : (prefixWord ++ tailWord_8097744).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8097744).length < 2 ^ (prefixWord ++ tailWord_8097744).sum := by decide
  have hdescent : baseEnd_8097744 < baseStart_8097744 := by decide
  rcases family_descends (prefixWord ++ tailWord_8097744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8097811 : List Nat := [1, 1, 1, 2, 1, 4, 5, 1, 1, 3, 3]
def baseStart_8097811 : Nat := 118140960795 + 8097811 * 2 ^ 59
def prefixEnd_8097811 : Nat := 4983230072969 + 3 ^ 40 * 8097811 * 2
def baseEnd_8097811 : Nat := 4158069292265722010921351

theorem tailTrace_8097811 : CollatzResearch.WordTrace tailWord_8097811 prefixEnd_8097811 4158069292265722010921351 := by
  unfold tailWord_8097811
  simp only [CollatzResearch.WordTrace]
  refine ⟨295351431266021217857973287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196900954177347478571982191 295351431266021217857973287)
  ·
    refine ⟨443027146899031826786959931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 295351431266021217857973287 443027146899031826786959931)
    ·
      refine ⟨664540720348547740180439897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 443027146899031826786959931 664540720348547740180439897)
      ·
        refine ⟨498405540261410805135329923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 664540720348547740180439897 498405540261410805135329923)
        ·
          refine ⟨747608310392116207702994885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 498405540261410805135329923 747608310392116207702994885)
          ·
            refine ⟨140176558198521788944311541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 747608310392116207702994885 140176558198521788944311541)
            ·
              refine ⟨13141552331111417713529207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 140176558198521788944311541 13141552331111417713529207)
              ·
                refine ⟨19712328496667126570293811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13141552331111417713529207 19712328496667126570293811)
                ·
                  refine ⟨29568492745000689855440717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19712328496667126570293811 29568492745000689855440717)
                  ·
                    refine ⟨11088184779375258695790269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29568492745000689855440717 11088184779375258695790269)
                    ·
                      refine ⟨4158069292265722010921351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11088184779375258695790269 4158069292265722010921351)
                      ·
                        rfl

theorem cell23_8097811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 5, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 5, 1, 1, 3, 3].length) (baseStart_8097811 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8097811 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8097811 prefixEnd_8097811 := by exact prefixLift 8097811
  have htrace : WordTrace (prefixWord ++ tailWord_8097811) baseStart_8097811 baseEnd_8097811 := by
    simpa [prefixWord, tailWord_8097811, baseEnd_8097811] using wordTrace_append hprefix tailTrace_8097811
  have hstable : (prefixWord ++ tailWord_8097811).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8097811).length < 2 ^ (prefixWord ++ tailWord_8097811).sum := by decide
  have hdescent : baseEnd_8097811 < baseStart_8097811 := by decide
  rcases family_descends (prefixWord ++ tailWord_8097811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8097812 : List Nat := [2, 4, 3, 2, 1, 1, 2, 2, 1, 1, 4]
def baseStart_8097812 : Nat := 118140960795 + 8097812 * 2 ^ 59
def prefixEnd_8097812 : Nat := 4983230072969 + 3 ^ 40 * 8097812 * 2
def baseEnd_8097812 : Nat := 4158069805746376507008847

theorem tailTrace_8097812 : CollatzResearch.WordTrace tailWord_8097812 prefixEnd_8097812 4158069805746376507008847 := by
  unfold tailWord_8097812
  simp only [CollatzResearch.WordTrace]
  refine ⟨147675733869508797514379845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196900978492678396685839793 147675733869508797514379845)
  ·
    refine ⟨27689200100532899533946221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 147675733869508797514379845 27689200100532899533946221)
    ·
      refine ⟨10383450037699837325229833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27689200100532899533946221 10383450037699837325229833)
      ·
        refine ⟨7787587528274877993922375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10383450037699837325229833 7787587528274877993922375)
        ·
          refine ⟨11681381292412316990883563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7787587528274877993922375 11681381292412316990883563)
          ·
            refine ⟨17522071938618475486325345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11681381292412316990883563 17522071938618475486325345)
            ·
              refine ⟨13141553953963856614744009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17522071938618475486325345 13141553953963856614744009)
              ·
                refine ⟨9856165465472892461058007, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13141553953963856614744009 9856165465472892461058007)
                ·
                  refine ⟨14784248198209338691587011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9856165465472892461058007 14784248198209338691587011)
                  ·
                    refine ⟨22176372297314008037380517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14784248198209338691587011 22176372297314008037380517)
                    ·
                      refine ⟨4158069805746376507008847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22176372297314008037380517 4158069805746376507008847)
                      ·
                        rfl

theorem cell23_8097812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 1, 2, 2, 1, 1, 4].length) (baseStart_8097812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8097812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8097812 prefixEnd_8097812 := by exact prefixLift 8097812
  have htrace : WordTrace (prefixWord ++ tailWord_8097812) baseStart_8097812 baseEnd_8097812 := by
    simpa [prefixWord, tailWord_8097812, baseEnd_8097812] using wordTrace_append hprefix tailTrace_8097812
  have hstable : (prefixWord ++ tailWord_8097812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8097812).length < 2 ^ (prefixWord ++ tailWord_8097812).sum := by decide
  have hdescent : baseEnd_8097812 < baseStart_8097812 := by decide
  rcases family_descends (prefixWord ++ tailWord_8097812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8097815 : List Nat := [1, 1, 3, 5, 2, 1, 2, 2, 1, 2, 3]
def baseStart_8097815 : Nat := 118140960795 + 8097815 * 2 ^ 59
def prefixEnd_8097815 : Nat := 4983230072969 + 3 ^ 40 * 8097815 * 2
def baseEnd_8097815 : Nat := 4158071346188339995271333

theorem tailTrace_8097815 : CollatzResearch.WordTrace tailWord_8097815 prefixEnd_8097815 4158071346188339995271333 := by
  unfold tailWord_8097815
  simp only [CollatzResearch.WordTrace]
  refine ⟨295351577158006726541118899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196901051438671151027412599 295351577158006726541118899)
  ·
    refine ⟨443027365737010089811678349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 295351577158006726541118899 443027365737010089811678349)
    ·
      refine ⟨166135262151378783679379381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 443027365737010089811678349 166135262151378783679379381)
      ·
        refine ⟨15575180826691760969941817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 166135262151378783679379381 15575180826691760969941817)
        ·
          refine ⟨11681385620018820727456363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15575180826691760969941817 11681385620018820727456363)
          ·
            refine ⟨17522078430028231091184545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11681385620018820727456363 17522078430028231091184545)
            ·
              refine ⟨13141558822521173318388409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17522078430028231091184545 13141558822521173318388409)
              ·
                refine ⟨9856169116890879988791307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13141558822521173318388409 9856169116890879988791307)
                ·
                  refine ⟨14784253675336319983186961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9856169116890879988791307 14784253675336319983186961)
                  ·
                    refine ⟨11088190256502239987390221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14784253675336319983186961 11088190256502239987390221)
                    ·
                      refine ⟨4158071346188339995271333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11088190256502239987390221 4158071346188339995271333)
                      ·
                        rfl

theorem cell23_8097815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 1, 2, 2, 1, 2, 3].length) (baseStart_8097815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8097815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8097815 prefixEnd_8097815 := by exact prefixLift 8097815
  have htrace : WordTrace (prefixWord ++ tailWord_8097815) baseStart_8097815 baseEnd_8097815 := by
    simpa [prefixWord, tailWord_8097815, baseEnd_8097815] using wordTrace_append hprefix tailTrace_8097815
  have hstable : (prefixWord ++ tailWord_8097815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8097815).length < 2 ^ (prefixWord ++ tailWord_8097815).sum := by decide
  have hdescent : baseEnd_8097815 < baseStart_8097815 := by decide
  rcases family_descends (prefixWord ++ tailWord_8097815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8097851 : List Nat := [1, 1, 1, 1, 1, 2, 1, 6, 3, 4, 2]
def baseStart_8097851 : Nat := 118140960795 + 8097851 * 2 ^ 59
def prefixEnd_8097851 : Nat := 4983230072969 + 3 ^ 40 * 8097851 * 2
def baseEnd_8097851 : Nat := 4158089831491901854421167

theorem tailTrace_8097851 : CollatzResearch.WordTrace tailWord_8097851 prefixEnd_8097851 4158089831491901854421167 := by
  unfold tailWord_8097851
  simp only [CollatzResearch.WordTrace]
  refine ⟨295352890185876304689429407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196901926790584203126286271 295352890185876304689429407)
  ·
    refine ⟨443029335278814457034144111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 295352890185876304689429407 443029335278814457034144111)
    ·
      refine ⟨664544002918221685551216167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 443029335278814457034144111 664544002918221685551216167)
      ·
        refine ⟨996816004377332528326824251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 664544002918221685551216167 996816004377332528326824251)
        ·
          refine ⟨1495224006565998792490236377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 996816004377332528326824251 1495224006565998792490236377)
          ·
            refine ⟨1121418004924499094367677283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1495224006565998792490236377 1121418004924499094367677283)
            ·
              refine ⟨1682127007386748641551515925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1121418004924499094367677283 1682127007386748641551515925)
              ·
                refine ⟨78849703471253842572727309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1682127007386748641551515925 78849703471253842572727309)
                ·
                  refine ⟨29568638801720190964772741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 78849703471253842572727309 29568638801720190964772741)
                  ·
                    refine ⟨5544119775322535805894889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29568638801720190964772741 5544119775322535805894889)
                    ·
                      refine ⟨4158089831491901854421167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5544119775322535805894889 4158089831491901854421167)
                      ·
                        rfl

theorem cell23_8097851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 6, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 6, 3, 4, 2].length) (baseStart_8097851 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8097851 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8097851 prefixEnd_8097851 := by exact prefixLift 8097851
  have htrace : WordTrace (prefixWord ++ tailWord_8097851) baseStart_8097851 baseEnd_8097851 := by
    simpa [prefixWord, tailWord_8097851, baseEnd_8097851] using wordTrace_append hprefix tailTrace_8097851
  have hstable : (prefixWord ++ tailWord_8097851).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8097851).length < 2 ^ (prefixWord ++ tailWord_8097851).sum := by decide
  have hdescent : baseEnd_8097851 < baseStart_8097851 := by decide
  rcases family_descends (prefixWord ++ tailWord_8097851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8097862 : List Nat := [6, 1, 1, 1, 1, 1, 3, 3, 2, 1, 3]
def baseStart_8097862 : Nat := 118140960795 + 8097862 * 2 ^ 59
def prefixEnd_8097862 : Nat := 4983230072969 + 3 ^ 40 * 8097862 * 2
def baseEnd_8097862 : Nat := 4158095479779101311383617

theorem tailTrace_8097862 : CollatzResearch.WordTrace tailWord_8097862 prefixEnd_8097862 4158095479779101311383617 := by
  unfold tailWord_8097862
  simp only [CollatzResearch.WordTrace]
  refine ⟨9229790355901139174002495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 196902194259224302378719893 9229790355901139174002495)
  ·
    refine ⟨13844685533851708761003743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9229790355901139174002495 13844685533851708761003743)
    ·
      refine ⟨20767028300777563141505615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13844685533851708761003743 20767028300777563141505615)
      ·
        refine ⟨31150542451166344712258423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20767028300777563141505615 31150542451166344712258423)
        ·
          refine ⟨46725813676749517068387635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31150542451166344712258423 46725813676749517068387635)
          ·
            refine ⟨70088720515124275602581453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46725813676749517068387635 70088720515124275602581453)
            ·
              refine ⟨26283270193171603350968045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 70088720515124275602581453 26283270193171603350968045)
              ·
                refine ⟨9856226322439351256613017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26283270193171603350968045 9856226322439351256613017)
                ·
                  refine ⟨7392169741829513442459763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9856226322439351256613017 7392169741829513442459763)
                  ·
                    refine ⟨11088254612744270163689645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7392169741829513442459763 11088254612744270163689645)
                    ·
                      refine ⟨4158095479779101311383617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11088254612744270163689645 4158095479779101311383617)
                      ·
                        rfl

theorem cell23_8097862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 3, 3, 2, 1, 3].length) (baseStart_8097862 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8097862 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8097862 prefixEnd_8097862 := by exact prefixLift 8097862
  have htrace : WordTrace (prefixWord ++ tailWord_8097862) baseStart_8097862 baseEnd_8097862 := by
    simpa [prefixWord, tailWord_8097862, baseEnd_8097862] using wordTrace_append hprefix tailTrace_8097862
  have hstable : (prefixWord ++ tailWord_8097862).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8097862).length < 2 ^ (prefixWord ++ tailWord_8097862).sum := by decide
  have hdescent : baseEnd_8097862 < baseStart_8097862 := by decide
  rcases family_descends (prefixWord ++ tailWord_8097862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8097885 : List Nat := [1, 4, 4, 1, 1, 1, 1, 1, 3, 4, 2]
def baseStart_8097885 : Nat := 118140960795 + 8097885 * 2 ^ 59
def prefixEnd_8097885 : Nat := 4983230072969 + 3 ^ 40 * 8097885 * 2
def baseEnd_8097885 : Nat := 4158107289834154721396011

theorem tailTrace_8097885 : CollatzResearch.WordTrace tailWord_8097885 prefixEnd_8097885 4158107289834154721396011 := by
  unfold tailWord_8097885
  simp only [CollatzResearch.WordTrace]
  refine ⟨295354130267753128496167109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196902753511835418997444739 295354130267753128496167109)
  ·
    refine ⟨55378899425203711593031333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 295354130267753128496167109 55378899425203711593031333)
    ·
      refine ⟨10383543642225695923693375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 55378899425203711593031333 10383543642225695923693375)
      ·
        refine ⟨15575315463338543885540063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10383543642225695923693375 15575315463338543885540063)
        ·
          refine ⟨23362973195007815828310095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15575315463338543885540063 23362973195007815828310095)
          ·
            refine ⟨35044459792511723742465143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23362973195007815828310095 35044459792511723742465143)
            ·
              refine ⟨52566689688767585613697715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35044459792511723742465143 52566689688767585613697715)
              ·
                refine ⟨78850034533151378420546573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52566689688767585613697715 78850034533151378420546573)
                ·
                  refine ⟨29568762949931766907704965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 78850034533151378420546573 29568762949931766907704965)
                  ·
                    refine ⟨5544143053112206295194681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29568762949931766907704965 5544143053112206295194681)
                    ·
                      refine ⟨4158107289834154721396011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5544143053112206295194681 4158107289834154721396011)
                      ·
                        rfl

theorem cell23_8097885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 1, 1, 3, 4, 2].length) (baseStart_8097885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8097885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8097885 prefixEnd_8097885 := by exact prefixLift 8097885
  have htrace : WordTrace (prefixWord ++ tailWord_8097885) baseStart_8097885 baseEnd_8097885 := by
    simpa [prefixWord, tailWord_8097885, baseEnd_8097885] using wordTrace_append hprefix tailTrace_8097885
  have hstable : (prefixWord ++ tailWord_8097885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8097885).length < 2 ^ (prefixWord ++ tailWord_8097885).sum := by decide
  have hdescent : baseEnd_8097885 < baseStart_8097885 := by decide
  rcases family_descends (prefixWord ++ tailWord_8097885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8097902 : List Nat := [4, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2]
def baseStart_8097902 : Nat := 118140960795 + 8097902 * 2 ^ 59
def prefixEnd_8097902 : Nat := 4983230072969 + 3 ^ 40 * 8097902 * 2
def baseEnd_8097902 : Nat := 4158116019005281154883433

theorem tailTrace_8097902 : CollatzResearch.WordTrace tailWord_8097902 prefixEnd_8097902 4158116019005281154883433 := by
  unfold tailWord_8097902
  simp only [CollatzResearch.WordTrace]
  refine ⟨36919343788586442549941995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 196903166872461026933023973 36919343788586442549941995)
  ·
    refine ⟨55379015682879663824912993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36919343788586442549941995 55379015682879663824912993)
    ·
      refine ⟨41534261762159747868684745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55379015682879663824912993 41534261762159747868684745)
      ·
        refine ⟨31150696321619810901513559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41534261762159747868684745 31150696321619810901513559)
        ·
          refine ⟨46726044482429716352270339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31150696321619810901513559 46726044482429716352270339)
          ·
            refine ⟨70089066723644574528405509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46726044482429716352270339 70089066723644574528405509)
            ·
              refine ⟨13141700010683357724076033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 70089066723644574528405509 13141700010683357724076033)
              ·
                refine ⟨9856275008012518293057025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13141700010683357724076033 9856275008012518293057025)
                ·
                  refine ⟨7392206256009388719792769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9856275008012518293057025 7392206256009388719792769)
                  ·
                    refine ⟨5544154692007041539844577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7392206256009388719792769 5544154692007041539844577)
                    ·
                      refine ⟨4158116019005281154883433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5544154692007041539844577 4158116019005281154883433)
                      ·
                        rfl

theorem cell23_8097902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2].length) (baseStart_8097902 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8097902 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8097902 prefixEnd_8097902 := by exact prefixLift 8097902
  have htrace : WordTrace (prefixWord ++ tailWord_8097902) baseStart_8097902 baseEnd_8097902 := by
    simpa [prefixWord, tailWord_8097902, baseEnd_8097902] using wordTrace_append hprefix tailTrace_8097902
  have hstable : (prefixWord ++ tailWord_8097902).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8097902).length < 2 ^ (prefixWord ++ tailWord_8097902).sum := by decide
  have hdescent : baseEnd_8097902 < baseStart_8097902 := by decide
  rcases family_descends (prefixWord ++ tailWord_8097902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8097941 : List Nat := [1, 3, 2, 1, 1, 1, 5, 1, 1, 3, 4]
def baseStart_8097941 : Nat := 118140960795 + 8097941 * 2 ^ 59
def prefixEnd_8097941 : Nat := 4983230072969 + 3 ^ 40 * 8097941 * 2
def baseEnd_8097941 : Nat := 4158136044750806502295753

theorem tailTrace_8097941 : CollatzResearch.WordTrace tailWord_8097941 prefixEnd_8097941 4158136044750806502295753 := by
  unfold tailWord_8097941
  simp only [CollatzResearch.WordTrace]
  refine ⟨295356172755550250060205677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196904115170366833373470451 295356172755550250060205677)
  ·
    refine ⟨110758564783331343772577129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 295356172755550250060205677 110758564783331343772577129)
    ·
      refine ⟨83068923587498507829432847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110758564783331343772577129 83068923587498507829432847)
      ·
        refine ⟨124603385381247761744149271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83068923587498507829432847 124603385381247761744149271)
        ·
          refine ⟨186905078071871642616223907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124603385381247761744149271 186905078071871642616223907)
          ·
            refine ⟨280357617107807463924335861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 186905078071871642616223907 280357617107807463924335861)
            ·
              refine ⟨26283526603856949742906487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 280357617107807463924335861 26283526603856949742906487)
              ·
                refine ⟨39425289905785424614359731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26283526603856949742906487 39425289905785424614359731)
                ·
                  refine ⟨59137934858678136921539597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39425289905785424614359731 59137934858678136921539597)
                  ·
                    refine ⟨22176725572004301345577349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 59137934858678136921539597 22176725572004301345577349)
                    ·
                      refine ⟨4158136044750806502295753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22176725572004301345577349 4158136044750806502295753)
                      ·
                        rfl

theorem cell23_8097941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 5, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 5, 1, 1, 3, 4].length) (baseStart_8097941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8097941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8097941 prefixEnd_8097941 := by exact prefixLift 8097941
  have htrace : WordTrace (prefixWord ++ tailWord_8097941) baseStart_8097941 baseEnd_8097941 := by
    simpa [prefixWord, tailWord_8097941, baseEnd_8097941] using wordTrace_append hprefix tailTrace_8097941
  have hstable : (prefixWord ++ tailWord_8097941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8097941).length < 2 ^ (prefixWord ++ tailWord_8097941).sum := by decide
  have hdescent : baseEnd_8097941 < baseStart_8097941 := by decide
  rcases family_descends (prefixWord ++ tailWord_8097941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8098002 : List Nat := [3, 2, 2, 2, 1, 2, 3, 3, 1, 4]
def baseStart_8098002 : Nat := 118140960795 + 8098002 * 2 ^ 59
def prefixEnd_8098002 : Nat := 4983230072969 + 3 ^ 40 * 8098002 * 2
def baseEnd_8098002 : Nat := 1386055789023576921210991

theorem tailTrace_8098002 : CollatzResearch.WordTrace tailWord_8098002 prefixEnd_8098002 1386055789023576921210991 := by
  unfold tailWord_8098002
  simp only [CollatzResearch.WordTrace]
  refine ⟨73839599402082314369544065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 196905598405552838318784173 73839599402082314369544065)
  ·
    refine ⟨55379699551561735777158049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73839599402082314369544065 55379699551561735777158049)
    ·
      refine ⟨41534774663671301832868537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55379699551561735777158049 41534774663671301832868537)
      ·
        refine ⟨31151080997753476374651403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41534774663671301832868537 31151080997753476374651403)
        ·
          refine ⟨46726621496630214561977105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31151080997753476374651403 46726621496630214561977105)
          ·
            refine ⟨35044966122472660921482829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46726621496630214561977105 35044966122472660921482829)
            ·
              refine ⟨13141862295927247845556061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35044966122472660921482829 13141862295927247845556061)
              ·
                refine ⟨4928198360972717942083523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13141862295927247845556061 4928198360972717942083523)
                ·
                  refine ⟨7392297541459076913125285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4928198360972717942083523 7392297541459076913125285)
                  ·
                    refine ⟨1386055789023576921210991, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7392297541459076913125285 1386055789023576921210991)
                    ·
                      rfl

theorem cell23_8098002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 3, 3, 1, 4].length) (baseStart_8098002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8098002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8098002 prefixEnd_8098002 := by exact prefixLift 8098002
  have htrace : WordTrace (prefixWord ++ tailWord_8098002) baseStart_8098002 baseEnd_8098002 := by
    simpa [prefixWord, tailWord_8098002, baseEnd_8098002] using wordTrace_append hprefix tailTrace_8098002
  have hstable : (prefixWord ++ tailWord_8098002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8098002).length < 2 ^ (prefixWord ++ tailWord_8098002).sum := by decide
  have hdescent : baseEnd_8098002 < baseStart_8098002 := by decide
  rcases family_descends (prefixWord ++ tailWord_8098002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8098019 : List Nat := [1, 1, 1, 8, 2, 1, 1, 1, 3, 4]
def baseStart_8098019 : Nat := 118140960795 + 8098019 * 2 ^ 59
def prefixEnd_8098019 : Nat := 4983230072969 + 3 ^ 40 * 8098019 * 2
def baseEnd_8098019 : Nat := 1386058698747285732373465

theorem tailTrace_8098019 : CollatzResearch.WordTrace tailWord_8098019 prefixEnd_8098019 1386058698747285732373465 := by
  unfold tailWord_8098019
  simp only [CollatzResearch.WordTrace]
  refine ⟨295359017649267669381545111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196906011766178446254363407 295359017649267669381545111)
  ·
    refine ⟨443038526473901504072317667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 295359017649267669381545111 443038526473901504072317667)
    ·
      refine ⟨664557789710852256108476501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 443038526473901504072317667 664557789710852256108476501)
      ·
        refine ⟨7787786598174049876271209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 8 664557789710852256108476501 7787786598174049876271209)
        ·
          refine ⟨5840839948630537407203407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7787786598174049876271209 5840839948630537407203407)
          ·
            refine ⟨8761259922945806110805111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5840839948630537407203407 8761259922945806110805111)
            ·
              refine ⟨13141889884418709166207667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8761259922945806110805111 13141889884418709166207667)
              ·
                refine ⟨19712834826628063749311501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13141889884418709166207667 19712834826628063749311501)
                ·
                  refine ⟨7392313059985523905991813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19712834826628063749311501 7392313059985523905991813)
                  ·
                    refine ⟨1386058698747285732373465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7392313059985523905991813 1386058698747285732373465)
                    ·
                      rfl

theorem cell23_8098019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 2, 1, 1, 1, 3, 4].length) (baseStart_8098019 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8098019 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8098019 prefixEnd_8098019 := by exact prefixLift 8098019
  have htrace : WordTrace (prefixWord ++ tailWord_8098019) baseStart_8098019 baseEnd_8098019 := by
    simpa [prefixWord, tailWord_8098019, baseEnd_8098019] using wordTrace_append hprefix tailTrace_8098019
  have hstable : (prefixWord ++ tailWord_8098019).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8098019).length < 2 ^ (prefixWord ++ tailWord_8098019).sum := by decide
  have hdescent : baseEnd_8098019 < baseStart_8098019 := by decide
  rcases family_descends (prefixWord ++ tailWord_8098019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8098048 : List Nat := [2, 1, 1, 2, 1, 1, 4, 1, 2, 6, 2]
def baseStart_8098048 : Nat := 118140960795 + 8098048 * 2 ^ 59
def prefixEnd_8098048 : Nat := 4983230072969 + 3 ^ 40 * 8098048 * 2
def baseEnd_8098048 : Nat := 4158190987180837583657761

theorem tailTrace_8098048 : CollatzResearch.WordTrace tailWord_8098048 prefixEnd_8098048 4158190987180837583657761 := by
  unfold tailWord_8098048
  simp only [CollatzResearch.WordTrace]
  refine ⟨147680037683081303667175399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196906716910775071556233865 147680037683081303667175399)
  ·
    refine ⟨221520056524621955500763099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147680037683081303667175399 221520056524621955500763099)
    ·
      refine ⟨332280084786932933251144649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 221520056524621955500763099 332280084786932933251144649)
      ·
        refine ⟨249210063590199699938358487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 332280084786932933251144649 249210063590199699938358487)
        ·
          refine ⟨373815095385299549907537731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 249210063590199699938358487 373815095385299549907537731)
          ·
            refine ⟨560722643077949324861306597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 373815095385299549907537731 560722643077949324861306597)
            ·
              refine ⟨105135495577115498411494987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 560722643077949324861306597 105135495577115498411494987)
              ·
                refine ⟨157703243365673247617242481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 105135495577115498411494987 157703243365673247617242481)
                ·
                  refine ⟨118277432524254935712931861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 157703243365673247617242481 118277432524254935712931861)
                  ·
                    refine ⟨5544254649574450111543681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 118277432524254935712931861 5544254649574450111543681)
                    ·
                      refine ⟨4158190987180837583657761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5544254649574450111543681 4158190987180837583657761)
                      ·
                        rfl

theorem cell23_8098048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 1, 2, 6, 2].length) (baseStart_8098048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8098048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8098048 prefixEnd_8098048 := by exact prefixLift 8098048
  have htrace : WordTrace (prefixWord ++ tailWord_8098048) baseStart_8098048 baseEnd_8098048 := by
    simpa [prefixWord, tailWord_8098048, baseEnd_8098048] using wordTrace_append hprefix tailTrace_8098048
  have hstable : (prefixWord ++ tailWord_8098048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8098048).length < 2 ^ (prefixWord ++ tailWord_8098048).sum := by decide
  have hdescent : baseEnd_8098048 < baseStart_8098048 := by decide
  rcases family_descends (prefixWord ++ tailWord_8098048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8098058 : List Nat := [3, 1, 2, 2, 1, 1, 2, 1, 6, 4]
def baseStart_8098058 : Nat := 118140960795 + 8098058 * 2 ^ 59
def prefixEnd_8098058 : Nat := 4983230072969 + 3 ^ 40 * 8098058 * 2
def baseEnd_8098058 : Nat := 1386065373995794181510905

theorem tailTrace_8098058 : CollatzResearch.WordTrace tailWord_8098058 prefixEnd_8098058 1386065373995794181510905 := by
  unfold tailWord_8098058
  simp only [CollatzResearch.WordTrace]
  refine ⟨73840110024031594760553707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 196906960064084252694809885 73840110024031594760553707)
  ·
    refine ⟨110760165036047392140830561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73840110024031594760553707 110760165036047392140830561)
    ·
      refine ⟨83070123777035544105622921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110760165036047392140830561 83070123777035544105622921)
      ·
        refine ⟨62302592832776658079217191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83070123777035544105622921 62302592832776658079217191)
        ·
          refine ⟨93453889249164987118825787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62302592832776658079217191 93453889249164987118825787)
          ·
            refine ⟨140180833873747480678238681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93453889249164987118825787 140180833873747480678238681)
            ·
              refine ⟨105135625405310610508679011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 140180833873747480678238681 105135625405310610508679011)
              ·
                refine ⟨157703438107965915763018517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 105135625405310610508679011 157703438107965915763018517)
                ·
                  refine ⟨7392348661310902301391493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 157703438107965915763018517 7392348661310902301391493)
                  ·
                    refine ⟨1386065373995794181510905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7392348661310902301391493 1386065373995794181510905)
                    ·
                      rfl

theorem cell23_8098058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 2, 1, 6, 4].length) (baseStart_8098058 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8098058 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8098058 prefixEnd_8098058 := by exact prefixLift 8098058
  have htrace : WordTrace (prefixWord ++ tailWord_8098058) baseStart_8098058 baseEnd_8098058 := by
    simpa [prefixWord, tailWord_8098058, baseEnd_8098058] using wordTrace_append hprefix tailTrace_8098058
  have hstable : (prefixWord ++ tailWord_8098058).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8098058).length < 2 ^ (prefixWord ++ tailWord_8098058).sum := by decide
  have hdescent : baseEnd_8098058 < baseStart_8098058 := by decide
  rcases family_descends (prefixWord ++ tailWord_8098058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8098071 : List Nat := [1, 1, 3, 4, 1, 13]
def baseStart_8098071 : Nat := 118140960795 + 8098071 * 2 ^ 59
def prefixEnd_8098071 : Nat := 4983230072969 + 3 ^ 40 * 8098071 * 2
def baseEnd_8098071 : Nat := 17111945667637411496585

theorem tailTrace_8098071 : CollatzResearch.WordTrace tailWord_8098071 prefixEnd_8098071 17111945667637411496585 := by
  unfold tailWord_8098071
  simp only [CollatzResearch.WordTrace]
  refine ⟨295360914245079282262438067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196907276163386188174958711 295360914245079282262438067)
  ·
    refine ⟨443041371367618923393657101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 295360914245079282262438067 443041371367618923393657101)
    ·
      refine ⟨166140514262857096272621413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 443041371367618923393657101 166140514262857096272621413)
      ·
        refine ⟨31151346424285705551116515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 166140514262857096272621413 31151346424285705551116515)
        ·
          refine ⟨46727019636428558326674773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31151346424285705551116515 46727019636428558326674773)
          ·
            refine ⟨17111945667637411496585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 13 46727019636428558326674773 17111945667637411496585)
            ·
              rfl

theorem cell23_8098071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 13].length) (baseStart_8098071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8098071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8098071 prefixEnd_8098071 := by exact prefixLift 8098071
  have htrace : WordTrace (prefixWord ++ tailWord_8098071) baseStart_8098071 baseEnd_8098071 := by
    simpa [prefixWord, tailWord_8098071, baseEnd_8098071] using wordTrace_append hprefix tailTrace_8098071
  have hstable : (prefixWord ++ tailWord_8098071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8098071).length < 2 ^ (prefixWord ++ tailWord_8098071).sum := by decide
  have hdescent : baseEnd_8098071 < baseStart_8098071 := by decide
  rcases family_descends (prefixWord ++ tailWord_8098071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8098105 : List Nat := [1, 2, 1, 6, 1, 2, 3, 7]
def baseStart_8098105 : Nat := 118140960795 + 8098105 * 2 ^ 59
def prefixEnd_8098105 : Nat := 4983230072969 + 3 ^ 40 * 8098105 * 2
def baseEnd_8098105 : Nat := 154008157614005328172037

theorem tailTrace_8098105 : CollatzResearch.WordTrace tailWord_8098105 prefixEnd_8098105 154008157614005328172037 := by
  unfold tailWord_8098105
  simp only [CollatzResearch.WordTrace]
  refine ⟨295362154326956106069175769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196908102884637404046117179 295362154326956106069175769)
  ·
    refine ⟨221521615745217079551881827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 295362154326956106069175769 221521615745217079551881827)
    ·
      refine ⟨332282423617825619327822741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 221521615745217079551881827 332282423617825619327822741)
      ·
        refine ⟨15575738607085575905991691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 332282423617825619327822741 15575738607085575905991691)
        ·
          refine ⟨23363607910628363858987537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15575738607085575905991691 23363607910628363858987537)
          ·
            refine ⟨17522705932971272894240653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23363607910628363858987537 17522705932971272894240653)
            ·
              refine ⟨6571014724864227335340245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17522705932971272894240653 6571014724864227335340245)
              ·
                refine ⟨154008157614005328172037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6571014724864227335340245 154008157614005328172037)
                ·
                  rfl

theorem cell23_8098105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 2, 3, 7].length) (baseStart_8098105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8098105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8098105 prefixEnd_8098105 := by exact prefixLift 8098105
  have htrace : WordTrace (prefixWord ++ tailWord_8098105) baseStart_8098105 baseEnd_8098105 := by
    simpa [prefixWord, tailWord_8098105, baseEnd_8098105] using wordTrace_append hprefix tailTrace_8098105
  have hstable : (prefixWord ++ tailWord_8098105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8098105).length < 2 ^ (prefixWord ++ tailWord_8098105).sum := by decide
  have hdescent : baseEnd_8098105 < baseStart_8098105 := by decide
  rcases family_descends (prefixWord ++ tailWord_8098105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8098116 : List Nat := [2, 3, 4, 1, 2, 2, 2, 1, 1, 1, 4]
def baseStart_8098116 : Nat := 118140960795 + 8098116 * 2 ^ 59
def prefixEnd_8098116 : Nat := 4983230072969 + 3 ^ 40 * 8098116 * 2
def baseEnd_8098116 : Nat := 4158225903865343317607449

theorem tailTrace_8098116 : CollatzResearch.WordTrace tailWord_8098116 prefixEnd_8098116 4158225903865343317607449 := by
  unfold tailWord_8098116
  simp only [CollatzResearch.WordTrace]
  refine ⟨147681277764958127473913101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196908370353277503298550801 147681277764958127473913101)
  ·
    refine ⟨55380479161859297802717413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 147681277764958127473913101 55380479161859297802717413)
    ·
      refine ⟨10383839842848618338009515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 55380479161859297802717413 10383839842848618338009515)
      ·
        refine ⟨15575759764272927507014273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10383839842848618338009515 15575759764272927507014273)
        ·
          refine ⟨11681819823204695630260705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15575759764272927507014273 11681819823204695630260705)
          ·
            refine ⟨8761364867403521722695529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11681819823204695630260705 8761364867403521722695529)
            ·
              refine ⟨6571023650552641292021647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8761364867403521722695529 6571023650552641292021647)
              ·
                refine ⟨9856535475828961938032471, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6571023650552641292021647 9856535475828961938032471)
                ·
                  refine ⟨14784803213743442907048707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9856535475828961938032471 14784803213743442907048707)
                  ·
                    refine ⟨22177204820615164360573061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14784803213743442907048707 22177204820615164360573061)
                    ·
                      refine ⟨4158225903865343317607449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22177204820615164360573061 4158225903865343317607449)
                      ·
                        rfl

theorem cell23_8098116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 2, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 2, 2, 1, 1, 1, 4].length) (baseStart_8098116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8098116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8098116 prefixEnd_8098116 := by exact prefixLift 8098116
  have htrace : WordTrace (prefixWord ++ tailWord_8098116) baseStart_8098116 baseEnd_8098116 := by
    simpa [prefixWord, tailWord_8098116, baseEnd_8098116] using wordTrace_append hprefix tailTrace_8098116
  have hstable : (prefixWord ++ tailWord_8098116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8098116).length < 2 ^ (prefixWord ++ tailWord_8098116).sum := by decide
  have hdescent : baseEnd_8098116 < baseStart_8098116 := by decide
  rcases family_descends (prefixWord ++ tailWord_8098116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8098132 : List Nat := [2, 4, 1, 1, 2, 3, 1, 1, 4, 1, 3]
def baseStart_8098132 : Nat := 118140960795 + 8098132 * 2 ^ 59
def prefixEnd_8098132 : Nat := 4983230072969 + 3 ^ 40 * 8098132 * 2
def baseEnd_8098132 : Nat := 4158234119555815255007375

theorem tailTrace_8098132 : CollatzResearch.WordTrace tailWord_8098132 prefixEnd_8098132 4158234119555815255007375 := by
  unfold tailWord_8098132
  simp only [CollatzResearch.WordTrace]
  refine ⟨147681569548929144840204325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196908759398572193120272433 147681569548929144840204325)
  ·
    refine ⟨27690294290424214657538311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 147681569548929144840204325 27690294290424214657538311)
    ·
      refine ⟨41535441435636321986307467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27690294290424214657538311 41535441435636321986307467)
      ·
        refine ⟨62303162153454482979461201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41535441435636321986307467 62303162153454482979461201)
        ·
          refine ⟨46727371615090862234595901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62303162153454482979461201 46727371615090862234595901)
          ·
            refine ⟨17522764355659073337973463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46727371615090862234595901 17522764355659073337973463)
            ·
              refine ⟨26284146533488610006960195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17522764355659073337973463 26284146533488610006960195)
              ·
                refine ⟨39426219800232915010440293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26284146533488610006960195 39426219800232915010440293)
                ·
                  refine ⟨7392416212543671564457555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39426219800232915010440293 7392416212543671564457555)
                  ·
                    refine ⟨11088624318815507346686333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7392416212543671564457555 11088624318815507346686333)
                    ·
                      refine ⟨4158234119555815255007375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11088624318815507346686333 4158234119555815255007375)
                      ·
                        rfl

theorem cell23_8098132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 3, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 3, 1, 1, 4, 1, 3].length) (baseStart_8098132 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8098132 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8098132 prefixEnd_8098132 := by exact prefixLift 8098132
  have htrace : WordTrace (prefixWord ++ tailWord_8098132) baseStart_8098132 baseEnd_8098132 := by
    simpa [prefixWord, tailWord_8098132, baseEnd_8098132] using wordTrace_append hprefix tailTrace_8098132
  have hstable : (prefixWord ++ tailWord_8098132).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8098132).length < 2 ^ (prefixWord ++ tailWord_8098132).sum := by decide
  have hdescent : baseEnd_8098132 < baseStart_8098132 := by decide
  rcases family_descends (prefixWord ++ tailWord_8098132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8098148 : List Nat := [2, 3, 1, 1, 3, 1, 1, 3, 2, 6]
def baseStart_8098148 : Nat := 118140960795 + 8098148 * 2 ^ 59
def prefixEnd_8098148 : Nat := 4983230072969 + 3 ^ 40 * 8098148 * 2
def baseEnd_8098148 : Nat := 1386080778415429064135767

theorem tailTrace_8098148 : CollatzResearch.WordTrace tailWord_8098148 prefixEnd_8098148 1386080778415429064135767 := by
  unfold tailWord_8098148
  simp only [CollatzResearch.WordTrace]
  refine ⟨147681861332900162206495549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196909148443866882941994065 147681861332900162206495549)
  ·
    refine ⟨55380697999837560827435831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 147681861332900162206495549 55380697999837560827435831)
    ·
      refine ⟨83071046999756341241153747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55380697999837560827435831 83071046999756341241153747)
      ·
        refine ⟨124606570499634511861730621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83071046999756341241153747 124606570499634511861730621)
        ·
          refine ⟨46727463937362941948148983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 124606570499634511861730621 46727463937362941948148983)
          ·
            refine ⟨70091195906044412922223475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46727463937362941948148983 70091195906044412922223475)
            ·
              refine ⟨105136793859066619383335213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70091195906044412922223475 105136793859066619383335213)
              ·
                refine ⟨39426297697149982268750705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 105136793859066619383335213 39426297697149982268750705)
                ·
                  refine ⟨29569723272862486701563029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39426297697149982268750705 29569723272862486701563029)
                  ·
                    refine ⟨1386080778415429064135767, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29569723272862486701563029 1386080778415429064135767)
                    ·
                      rfl

theorem cell23_8098148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 1, 3, 2, 6].length) (baseStart_8098148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8098148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8098148 prefixEnd_8098148 := by exact prefixLift 8098148
  have htrace : WordTrace (prefixWord ++ tailWord_8098148) baseStart_8098148 baseEnd_8098148 := by
    simpa [prefixWord, tailWord_8098148, baseEnd_8098148] using wordTrace_append hprefix tailTrace_8098148
  have hstable : (prefixWord ++ tailWord_8098148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8098148).length < 2 ^ (prefixWord ++ tailWord_8098148).sum := by decide
  have hdescent : baseEnd_8098148 < baseStart_8098148 := by decide
  rcases family_descends (prefixWord ++ tailWord_8098148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8098149 : List Nat := [1, 3, 1, 3, 1, 4, 3, 1, 2, 1, 3]
def baseStart_8098149 : Nat := 118140960795 + 8098149 * 2 ^ 59
def prefixEnd_8098149 : Nat := 4983230072969 + 3 ^ 40 * 8098149 * 2
def baseEnd_8098149 : Nat := 4158242848726941688494797

theorem tailTrace_8098149 : CollatzResearch.WordTrace tailWord_8098149 prefixEnd_8098149 4158242848726941688494797 := by
  unfold tailWord_8098149
  simp only [CollatzResearch.WordTrace]
  refine ⟨295363759138796701583777501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196909172759197801055851667 295363759138796701583777501)
  ·
    refine ⟨110761409677048763093916563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 295363759138796701583777501 110761409677048763093916563)
    ·
      refine ⟨166142114515573144640874845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110761409677048763093916563 166142114515573144640874845)
      ·
        refine ⟨62303292943339929240328067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 166142114515573144640874845 62303292943339929240328067)
        ·
          refine ⟨93454939415009893860492101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62303292943339929240328067 93454939415009893860492101)
          ·
            refine ⟨17522801140314355098842269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 93454939415009893860492101 17522801140314355098842269)
            ·
              refine ⟨6571050427617883162065851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17522801140314355098842269 6571050427617883162065851)
              ·
                refine ⟨9856575641426824743098777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6571050427617883162065851 9856575641426824743098777)
                ·
                  refine ⟨7392431731070118557324083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9856575641426824743098777 7392431731070118557324083)
                  ·
                    refine ⟨11088647596605177835986125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7392431731070118557324083 11088647596605177835986125)
                    ·
                      refine ⟨4158242848726941688494797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11088647596605177835986125 4158242848726941688494797)
                      ·
                        rfl

theorem cell23_8098149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 4, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 4, 3, 1, 2, 1, 3].length) (baseStart_8098149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8098149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8098149 prefixEnd_8098149 := by exact prefixLift 8098149
  have htrace : WordTrace (prefixWord ++ tailWord_8098149) baseStart_8098149 baseEnd_8098149 := by
    simpa [prefixWord, tailWord_8098149, baseEnd_8098149] using wordTrace_append hprefix tailTrace_8098149
  have hstable : (prefixWord ++ tailWord_8098149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8098149).length < 2 ^ (prefixWord ++ tailWord_8098149).sum := by decide
  have hdescent : baseEnd_8098149 < baseStart_8098149 := by decide
  rcases family_descends (prefixWord ++ tailWord_8098149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8098225 : List Nat := [1, 2, 2, 4, 1, 2, 1, 3, 2, 5]
def baseStart_8098225 : Nat := 118140960795 + 8098225 * 2 ^ 59
def prefixEnd_8098225 : Nat := 4983230072969 + 3 ^ 40 * 8098225 * 2
def baseEnd_8098225 : Nat := 1386093957752227797048149

theorem tailTrace_8098225 : CollatzResearch.WordTrace tailWord_8098225 prefixEnd_8098225 1386093957752227797048149 := by
  unfold tailWord_8098225
  simp only [CollatzResearch.WordTrace]
  refine ⟨295366531086521366563544129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196911020724347577709029419 295366531086521366563544129)
  ·
    refine ⟨221524898314891024922658097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 295366531086521366563544129 221524898314891024922658097)
    ·
      refine ⟨166143673736168268691993573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 221524898314891024922658097 166143673736168268691993573)
      ·
        refine ⟨31151938825531550379748795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 166143673736168268691993573 31151938825531550379748795)
        ·
          refine ⟨46727908238297325569623193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31151938825531550379748795 46727908238297325569623193)
          ·
            refine ⟨35045931178722994177217395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46727908238297325569623193 35045931178722994177217395)
            ·
              refine ⟨52568896768084491265826093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35045931178722994177217395 52568896768084491265826093)
              ·
                refine ⟨19713336288031684224684785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52568896768084491265826093 19713336288031684224684785)
                ·
                  refine ⟨14785002216023763168513589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19713336288031684224684785 14785002216023763168513589)
                  ·
                    refine ⟨1386093957752227797048149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14785002216023763168513589 1386093957752227797048149)
                    ·
                      rfl

theorem cell23_8098225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 1, 3, 2, 5].length) (baseStart_8098225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8098225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8098225 prefixEnd_8098225 := by exact prefixLift 8098225
  have htrace : WordTrace (prefixWord ++ tailWord_8098225) baseStart_8098225 baseEnd_8098225 := by
    simpa [prefixWord, tailWord_8098225, baseEnd_8098225] using wordTrace_append hprefix tailTrace_8098225
  have hstable : (prefixWord ++ tailWord_8098225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8098225).length < 2 ^ (prefixWord ++ tailWord_8098225).sum := by decide
  have hdescent : baseEnd_8098225 < baseStart_8098225 := by decide
  rcases family_descends (prefixWord ++ tailWord_8098225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8098245 : List Nat := [1, 3, 1, 1, 1, 1, 1, 1, 5, 6, 2]
def baseStart_8098245 : Nat := 118140960795 + 8098245 * 2 ^ 59
def prefixEnd_8098245 : Nat := 4983230072969 + 3 ^ 40 * 8098245 * 2
def baseEnd_8098245 : Nat := 4158292142869773312894355

theorem tailTrace_8098245 : CollatzResearch.WordTrace tailWord_8098245 prefixEnd_8098245 4158292142869773312894355 := by
  unfold tailWord_8098245
  simp only [CollatzResearch.WordTrace]
  refine ⟨295367260546448909979272189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196911507030965939986181459 295367260546448909979272189)
  ·
    refine ⟨110762722704918341242227071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 295367260546448909979272189 110762722704918341242227071)
    ·
      refine ⟨166144084057377511863340607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110762722704918341242227071 166144084057377511863340607)
      ·
        refine ⟨249216126086066267795010911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166144084057377511863340607 249216126086066267795010911)
        ·
          refine ⟨373824189129099401692516367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 249216126086066267795010911 373824189129099401692516367)
          ·
            refine ⟨560736283693649102538774551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 373824189129099401692516367 560736283693649102538774551)
            ·
              refine ⟨841104425540473653808161827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 560736283693649102538774551 841104425540473653808161827)
              ·
                refine ⟨1261656638310710480712242741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 841104425540473653808161827 1261656638310710480712242741)
                ·
                  refine ⟨118280309841629107566772757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1261656638310710480712242741 118280309841629107566772757)
                  ·
                    refine ⟨5544389523826364417192473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 118280309841629107566772757 5544389523826364417192473)
                    ·
                      refine ⟨4158292142869773312894355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5544389523826364417192473 4158292142869773312894355)
                      ·
                        rfl

theorem cell23_8098245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 1, 5, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 1, 5, 6, 2].length) (baseStart_8098245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8098245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8098245 prefixEnd_8098245 := by exact prefixLift 8098245
  have htrace : WordTrace (prefixWord ++ tailWord_8098245) baseStart_8098245 baseEnd_8098245 := by
    simpa [prefixWord, tailWord_8098245, baseEnd_8098245] using wordTrace_append hprefix tailTrace_8098245
  have hstable : (prefixWord ++ tailWord_8098245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8098245).length < 2 ^ (prefixWord ++ tailWord_8098245).sum := by decide
  have hdescent : baseEnd_8098245 < baseStart_8098245 := by decide
  rcases family_descends (prefixWord ++ tailWord_8098245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8098255 : List Nat := [1, 1, 2, 1, 1, 4, 1, 5, 3, 4]
def baseStart_8098255 : Nat := 118140960795 + 8098255 * 2 ^ 59
def prefixEnd_8098255 : Nat := 4983230072969 + 3 ^ 40 * 8098255 * 2
def baseEnd_8098255 : Nat := 1386099092558772757923103

theorem tailTrace_8098255 : CollatzResearch.WordTrace tailWord_8098255 prefixEnd_8098255 1386099092558772757923103 := by
  unfold tailWord_8098255
  simp only [CollatzResearch.WordTrace]
  refine ⟨295367625276412681687136219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196911750184275121124757479 295367625276412681687136219)
  ·
    refine ⟨443051437914619022530704329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 295367625276412681687136219 443051437914619022530704329)
    ·
      refine ⟨332288578435964266898028247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 443051437914619022530704329 332288578435964266898028247)
      ·
        refine ⟨498432867653946400347042371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 332288578435964266898028247 498432867653946400347042371)
        ·
          refine ⟨747649301480919600520563557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 498432867653946400347042371 747649301480919600520563557)
          ·
            refine ⟨140184244027672425097605667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 747649301480919600520563557 140184244027672425097605667)
            ·
              refine ⟨210276366041508637646408501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 140184244027672425097605667 210276366041508637646408501)
              ·
                refine ⟨19713409316391434779350797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 210276366041508637646408501 19713409316391434779350797)
                ·
                  refine ⟨7392528493646788042256549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19713409316391434779350797 7392528493646788042256549)
                  ·
                    refine ⟨1386099092558772757923103, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7392528493646788042256549 1386099092558772757923103)
                    ·
                      rfl

theorem cell23_8098255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 5, 3, 4].length) (baseStart_8098255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8098255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8098255 prefixEnd_8098255 := by exact prefixLift 8098255
  have htrace : WordTrace (prefixWord ++ tailWord_8098255) baseStart_8098255 baseEnd_8098255 := by
    simpa [prefixWord, tailWord_8098255, baseEnd_8098255] using wordTrace_append hprefix tailTrace_8098255
  have hstable : (prefixWord ++ tailWord_8098255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8098255).length < 2 ^ (prefixWord ++ tailWord_8098255).sum := by decide
  have hdescent : baseEnd_8098255 < baseStart_8098255 := by decide
  rcases family_descends (prefixWord ++ tailWord_8098255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8098262 : List Nat := [5, 2, 1, 1, 1, 1, 2, 2, 1, 3, 4]
def baseStart_8098262 : Nat := 118140960795 + 8098262 * 2 ^ 59
def prefixEnd_8098262 : Nat := 4983230072969 + 3 ^ 40 * 8098262 * 2
def baseEnd_8098262 : Nat := 4158300872040899746381777

theorem tailTrace_8098262 : CollatzResearch.WordTrace tailWord_8098262 prefixEnd_8098262 4158300872040899746381777 := by
  unfold tailWord_8098262
  simp only [CollatzResearch.WordTrace]
  refine ⟨18460492536711707617665065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 196911920391591547921760693 18460492536711707617665065)
  ·
    refine ⟨13845369402533780713248799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18460492536711707617665065 13845369402533780713248799)
    ·
      refine ⟨20768054103800671069873199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13845369402533780713248799 20768054103800671069873199)
      ·
        refine ⟨31152081155701006604809799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20768054103800671069873199 31152081155701006604809799)
        ·
          refine ⟨46728121733551509907214699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31152081155701006604809799 46728121733551509907214699)
          ·
            refine ⟨70092182600327264860822049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46728121733551509907214699 70092182600327264860822049)
            ·
              refine ⟨52569136950245448645616537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70092182600327264860822049 52569136950245448645616537)
              ·
                refine ⟨39426852712684086484212403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52569136950245448645616537 39426852712684086484212403)
                ·
                  refine ⟨59140279069026129726318605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39426852712684086484212403 59140279069026129726318605)
                  ·
                    refine ⟨22177604650884798647369477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 59140279069026129726318605 22177604650884798647369477)
                    ·
                      refine ⟨4158300872040899746381777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22177604650884798647369477 4158300872040899746381777)
                      ·
                        rfl

theorem cell23_8098262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 2, 2, 1, 3, 4].length) (baseStart_8098262 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8098262 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8098262 prefixEnd_8098262 := by exact prefixLift 8098262
  have htrace : WordTrace (prefixWord ++ tailWord_8098262) baseStart_8098262 baseEnd_8098262 := by
    simpa [prefixWord, tailWord_8098262, baseEnd_8098262] using wordTrace_append hprefix tailTrace_8098262
  have hstable : (prefixWord ++ tailWord_8098262).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8098262).length < 2 ^ (prefixWord ++ tailWord_8098262).sum := by decide
  have hdescent : baseEnd_8098262 < baseStart_8098262 := by decide
  rcases family_descends (prefixWord ++ tailWord_8098262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8098265 : List Nat := [1, 2, 1, 2, 4, 1, 2, 2, 1, 4, 3]
def baseStart_8098265 : Nat := 118140960795 + 8098265 * 2 ^ 59
def prefixEnd_8098265 : Nat := 4983230072969 + 3 ^ 40 * 8098265 * 2
def baseEnd_8098265 : Nat := 4158302412482863234644263

theorem tailTrace_8098265 : CollatzResearch.WordTrace tailWord_8098265 prefixEnd_8098265 4158302412482863234644263 := by
  unfold tailWord_8098265
  simp only [CollatzResearch.WordTrace]
  refine ⟨295367990006376453395000249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196911993337584302263333499 295367990006376453395000249)
  ·
    refine ⟨221525992504782340046250187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 295367990006376453395000249 221525992504782340046250187)
    ·
      refine ⟨332288988757173510069375281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 221525992504782340046250187 332288988757173510069375281)
      ·
        refine ⟨249216741567880132552031461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 332288988757173510069375281 249216741567880132552031461)
        ·
          refine ⟨46728139043977524853505899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 249216741567880132552031461 46728139043977524853505899)
          ·
            refine ⟨70092208565966287280258849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46728139043977524853505899 70092208565966287280258849)
            ·
              refine ⟨52569156424474715460194137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70092208565966287280258849 52569156424474715460194137)
              ·
                refine ⟨39426867318356036595145603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52569156424474715460194137 39426867318356036595145603)
                ·
                  refine ⟨59140300977534054892718405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39426867318356036595145603 59140300977534054892718405)
                  ·
                    refine ⟨11088806433287635292384701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 59140300977534054892718405 11088806433287635292384701)
                    ·
                      refine ⟨4158302412482863234644263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11088806433287635292384701 4158302412482863234644263)
                      ·
                        rfl

theorem cell23_8098265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 2, 2, 1, 4, 3].length) (baseStart_8098265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8098265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8098265 prefixEnd_8098265 := by exact prefixLift 8098265
  have htrace : WordTrace (prefixWord ++ tailWord_8098265) baseStart_8098265 baseEnd_8098265 := by
    simpa [prefixWord, tailWord_8098265, baseEnd_8098265] using wordTrace_append hprefix tailTrace_8098265
  have hstable : (prefixWord ++ tailWord_8098265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8098265).length < 2 ^ (prefixWord ++ tailWord_8098265).sum := by decide
  have hdescent : baseEnd_8098265 < baseStart_8098265 := by decide
  rcases family_descends (prefixWord ++ tailWord_8098265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8098282 : List Nat := [3, 1, 3, 1, 3, 2, 1, 1, 1, 4, 3]
def baseStart_8098282 : Nat := 118140960795 + 8098282 * 2 ^ 59
def prefixEnd_8098282 : Nat := 4983230072969 + 3 ^ 40 * 8098282 * 2
def baseEnd_8098282 : Nat := 4158311141653989668131685

theorem tailTrace_8098282 : CollatzResearch.WordTrace tailWord_8098282 prefixEnd_8098282 4158311141653989668131685 := by
  unfold tailWord_8098282
  simp only [CollatzResearch.WordTrace]
  refine ⟨73842152511828716324592275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 196912406698209910198912733 73842152511828716324592275)
  ·
    refine ⟨110763228767743074486888413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73842152511828716324592275 110763228767743074486888413)
    ·
      refine ⟨41536210787903652932583155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 110763228767743074486888413 41536210787903652932583155)
      ·
        refine ⟨62304316181855479398874733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41536210787903652932583155 62304316181855479398874733)
        ·
          refine ⟨23364118568195804774578025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62304316181855479398874733 23364118568195804774578025)
          ·
            refine ⟨17523088926146853580933519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23364118568195804774578025 17523088926146853580933519)
            ·
              refine ⟨26284633389220280371400279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17523088926146853580933519 26284633389220280371400279)
              ·
                refine ⟨39426950083830420557100419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26284633389220280371400279 39426950083830420557100419)
                ·
                  refine ⟨59140425125745630835650629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39426950083830420557100419 59140425125745630835650629)
                  ·
                    refine ⟨11088829711077305781684493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 59140425125745630835650629 11088829711077305781684493)
                    ·
                      refine ⟨4158311141653989668131685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11088829711077305781684493 4158311141653989668131685)
                      ·
                        rfl

theorem cell23_8098282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 2, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 2, 1, 1, 1, 4, 3].length) (baseStart_8098282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8098282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8098282 prefixEnd_8098282 := by exact prefixLift 8098282
  have htrace : WordTrace (prefixWord ++ tailWord_8098282) baseStart_8098282 baseEnd_8098282 := by
    simpa [prefixWord, tailWord_8098282, baseEnd_8098282] using wordTrace_append hprefix tailTrace_8098282
  have hstable : (prefixWord ++ tailWord_8098282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8098282).length < 2 ^ (prefixWord ++ tailWord_8098282).sum := by decide
  have hdescent : baseEnd_8098282 < baseStart_8098282 := by decide
  rcases family_descends (prefixWord ++ tailWord_8098282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8098289 : List Nat := [1, 2, 2, 2, 3, 1, 4, 3, 1, 4]
def baseStart_8098289 : Nat := 118140960795 + 8098289 * 2 ^ 59
def prefixEnd_8098289 : Nat := 4983230072969 + 3 ^ 40 * 8098289 * 2
def baseEnd_8098289 : Nat := 1386104912006190380248051

theorem tailTrace_8098289 : CollatzResearch.WordTrace tailWord_8098289 prefixEnd_8098289 1386104912006190380248051 := by
  unfold tailWord_8098289
  simp only [CollatzResearch.WordTrace]
  refine ⟨295368865358289505493873921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196912576905526336995915947 295368865358289505493873921)
  ·
    refine ⟨221526649018717129120405441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 295368865358289505493873921 221526649018717129120405441)
    ·
      refine ⟨166144986764037846840304081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 221526649018717129120405441 166144986764037846840304081)
      ·
        refine ⟨124608740073028385130228061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 166144986764037846840304081 124608740073028385130228061)
        ·
          refine ⟨46728277527385644423835523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 124608740073028385130228061 46728277527385644423835523)
          ·
            refine ⟨70092416291078466635753285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46728277527385644423835523 70092416291078466635753285)
            ·
              refine ⟨13142328054577212494203741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 70092416291078466635753285 13142328054577212494203741)
              ·
                refine ⟨4928373020466454685326403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13142328054577212494203741 4928373020466454685326403)
                ·
                  refine ⟨7392559530699682027989605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4928373020466454685326403 7392559530699682027989605)
                  ·
                    refine ⟨1386104912006190380248051, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7392559530699682027989605 1386104912006190380248051)
                    ·
                      rfl

theorem cell23_8098289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 4, 3, 1, 4].length) (baseStart_8098289 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8098289 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8098289 prefixEnd_8098289 := by exact prefixLift 8098289
  have htrace : WordTrace (prefixWord ++ tailWord_8098289) baseStart_8098289 baseEnd_8098289 := by
    simpa [prefixWord, tailWord_8098289, baseEnd_8098289] using wordTrace_append hprefix tailTrace_8098289
  have hstable : (prefixWord ++ tailWord_8098289).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8098289).length < 2 ^ (prefixWord ++ tailWord_8098289).sum := by decide
  have hdescent : baseEnd_8098289 < baseStart_8098289 := by decide
  rcases family_descends (prefixWord ++ tailWord_8098289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8098305 : List Nat := [1, 2, 4, 1, 3, 1, 1, 1, 1, 2, 6]
def baseStart_8098305 : Nat := 118140960795 + 8098305 * 2 ^ 59
def prefixEnd_8098305 : Nat := 4983230072969 + 3 ^ 40 * 8098305 * 2
def baseEnd_8098305 : Nat := 4158322951709043078144079

theorem tailTrace_8098305 : CollatzResearch.WordTrace tailWord_8098305 prefixEnd_8098305 4158322951709043078144079 := by
  unfold tailWord_8098305
  simp only [CollatzResearch.WordTrace]
  refine ⟨295369448926231540226456369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196912965950821026817637579 295369448926231540226456369)
  ·
    refine ⟨221527086694673655169842277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 295369448926231540226456369 221527086694673655169842277)
    ·
      refine ⟨41536328755251310344345427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 221527086694673655169842277 41536328755251310344345427)
      ·
        refine ⟨62304493132876965516518141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41536328755251310344345427 62304493132876965516518141)
        ·
          refine ⟨23364184924828862068694303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62304493132876965516518141 23364184924828862068694303)
          ·
            refine ⟨35046277387243293103041455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23364184924828862068694303 35046277387243293103041455)
            ·
              refine ⟨52569416080864939654562183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35046277387243293103041455 52569416080864939654562183)
              ·
                refine ⟨78854124121297409481843275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52569416080864939654562183 78854124121297409481843275)
                ·
                  refine ⟨118281186181946114222764913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 78854124121297409481843275 118281186181946114222764913)
                  ·
                    refine ⟨88710889636459585667073685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 118281186181946114222764913 88710889636459585667073685)
                    ·
                      refine ⟨4158322951709043078144079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 88710889636459585667073685 4158322951709043078144079)
                      ·
                        rfl

theorem cell23_8098305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 1, 1, 1, 2, 6].length) (baseStart_8098305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8098305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8098305 prefixEnd_8098305 := by exact prefixLift 8098305
  have htrace : WordTrace (prefixWord ++ tailWord_8098305) baseStart_8098305 baseEnd_8098305 := by
    simpa [prefixWord, tailWord_8098305, baseEnd_8098305] using wordTrace_append hprefix tailTrace_8098305
  have hstable : (prefixWord ++ tailWord_8098305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8098305).length < 2 ^ (prefixWord ++ tailWord_8098305).sum := by decide
  have hdescent : baseEnd_8098305 < baseStart_8098305 := by decide
  rcases family_descends (prefixWord ++ tailWord_8098305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8098306 : List Nat := [3, 4, 1, 2, 2, 1, 2, 1, 3, 4]
def baseStart_8098306 : Nat := 118140960795 + 8098306 * 2 ^ 59
def prefixEnd_8098306 : Nat := 4983230072969 + 3 ^ 40 * 8098306 * 2
def baseEnd_8098306 : Nat := 1386107821729899191410525

theorem tailTrace_8098306 : CollatzResearch.WordTrace tailWord_8098306 prefixEnd_8098306 1386107821729899191410525 := by
  unfold tailWord_8098306
  simp only [CollatzResearch.WordTrace]
  refine ⟨73842371349806979349310693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 196912990266151944931495181 73842371349806979349310693)
  ·
    refine ⟨13845444628088808627995755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 73842371349806979349310693 13845444628088808627995755)
    ·
      refine ⟨20768166942133212941993633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13845444628088808627995755 20768166942133212941993633)
      ·
        refine ⟨15576125206599909706495225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20768166942133212941993633 15576125206599909706495225)
        ·
          refine ⟨11682093904949932279871419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15576125206599909706495225 11682093904949932279871419)
          ·
            refine ⟨17523140857424898419807129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11682093904949932279871419 17523140857424898419807129)
            ·
              refine ⟨13142355643068673814855347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17523140857424898419807129 13142355643068673814855347)
              ·
                refine ⟨19713533464603010722283021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13142355643068673814855347 19713533464603010722283021)
                ·
                  refine ⟨7392575049226129020856133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19713533464603010722283021 7392575049226129020856133)
                  ·
                    refine ⟨1386107821729899191410525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7392575049226129020856133 1386107821729899191410525)
                    ·
                      rfl

theorem cell23_8098306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 1, 2, 1, 3, 4].length) (baseStart_8098306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8098306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8098306 prefixEnd_8098306 := by exact prefixLift 8098306
  have htrace : WordTrace (prefixWord ++ tailWord_8098306) baseStart_8098306 baseEnd_8098306 := by
    simpa [prefixWord, tailWord_8098306, baseEnd_8098306] using wordTrace_append hprefix tailTrace_8098306
  have hstable : (prefixWord ++ tailWord_8098306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8098306).length < 2 ^ (prefixWord ++ tailWord_8098306).sum := by decide
  have hdescent : baseEnd_8098306 < baseStart_8098306 := by decide
  rcases family_descends (prefixWord ++ tailWord_8098306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8098332 : List Nat := [2, 2, 3, 1, 2, 2, 1, 4, 1, 5]
def baseStart_8098332 : Nat := 118140960795 + 8098332 * 2 ^ 59
def prefixEnd_8098332 : Nat := 4983230072969 + 3 ^ 40 * 8098332 * 2
def baseEnd_8098332 : Nat := 1386112271895571490835485

theorem tailTrace_8098332 : CollatzResearch.WordTrace tailWord_8098332 prefixEnd_8098332 1386112271895571490835485 := by
  unfold tailWord_8098332
  simp only [CollatzResearch.WordTrace]
  refine ⟨147685216848566861918844625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196913622464755815891792833 147685216848566861918844625)
  ·
    refine ⟨110763912636425146439133469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147685216848566861918844625 110763912636425146439133469)
    ·
      refine ⟨41536467238659429914675051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 110763912636425146439133469 41536467238659429914675051)
      ·
        refine ⟨62304700857989144872012577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41536467238659429914675051 62304700857989144872012577)
        ·
          refine ⟨46728525643491858654009433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62304700857989144872012577 46728525643491858654009433)
          ·
            refine ⟨35046394232618893990507075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46728525643491858654009433 35046394232618893990507075)
            ·
              refine ⟨52569591348928340985760613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35046394232618893990507075 52569591348928340985760613)
              ·
                refine ⟨9856798377924063934830115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 52569591348928340985760613 9856798377924063934830115)
                ·
                  refine ⟨14785197566886095902245173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9856798377924063934830115 14785197566886095902245173)
                  ·
                    refine ⟨1386112271895571490835485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14785197566886095902245173 1386112271895571490835485)
                    ·
                      rfl

theorem cell23_8098332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 1, 4, 1, 5].length) (baseStart_8098332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8098332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8098332 prefixEnd_8098332 := by exact prefixLift 8098332
  have htrace : WordTrace (prefixWord ++ tailWord_8098332) baseStart_8098332 baseEnd_8098332 := by
    simpa [prefixWord, tailWord_8098332, baseEnd_8098332] using wordTrace_append hprefix tailTrace_8098332
  have hstable : (prefixWord ++ tailWord_8098332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8098332).length < 2 ^ (prefixWord ++ tailWord_8098332).sum := by decide
  have hdescent : baseEnd_8098332 < baseStart_8098332 := by decide
  rcases family_descends (prefixWord ++ tailWord_8098332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8098340 : List Nat := [2, 3, 1, 5, 2, 1, 1, 3, 1, 4]
def baseStart_8098340 : Nat := 118140960795 + 8098340 * 2 ^ 59
def prefixEnd_8098340 : Nat := 4983230072969 + 3 ^ 40 * 8098340 * 2
def baseEnd_8098340 : Nat := 1386113641177316813735473

theorem tailTrace_8098340 : CollatzResearch.WordTrace tailWord_8098340 prefixEnd_8098340 1386113641177316813735473 := by
  unfold tailWord_8098340
  simp only [CollatzResearch.WordTrace]
  refine ⟨147685362740552370601990237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196913816987403160802653649 147685362740552370601990237)
  ·
    refine ⟨55382011027707138975746339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 147685362740552370601990237 55382011027707138975746339)
    ·
      refine ⟨83073016541560708463619509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55382011027707138975746339 83073016541560708463619509)
      ·
        refine ⟨7788095300771316418464329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 83073016541560708463619509 7788095300771316418464329)
        ·
          refine ⟨5841071475578487313848247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7788095300771316418464329 5841071475578487313848247)
          ·
            refine ⟨8761607213367730970772371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5841071475578487313848247 8761607213367730970772371)
            ·
              refine ⟨13142410820051596456158557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8761607213367730970772371 13142410820051596456158557)
              ·
                refine ⟨4928404057519348671059459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13142410820051596456158557 4928404057519348671059459)
                ·
                  refine ⟨7392606086279023006589189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4928404057519348671059459 7392606086279023006589189)
                  ·
                    refine ⟨1386113641177316813735473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7392606086279023006589189 1386113641177316813735473)
                    ·
                      rfl

theorem cell23_8098340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 2, 1, 1, 3, 1, 4].length) (baseStart_8098340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8098340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8098340 prefixEnd_8098340 := by exact prefixLift 8098340
  have htrace : WordTrace (prefixWord ++ tailWord_8098340) baseStart_8098340 baseEnd_8098340 := by
    simpa [prefixWord, tailWord_8098340, baseEnd_8098340] using wordTrace_append hprefix tailTrace_8098340
  have hstable : (prefixWord ++ tailWord_8098340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8098340).length < 2 ^ (prefixWord ++ tailWord_8098340).sum := by decide
  have hdescent : baseEnd_8098340 < baseStart_8098340 := by decide
  rcases family_descends (prefixWord ++ tailWord_8098340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8098352 : List Nat := [2, 1, 1, 1, 2, 3, 4, 3, 1, 1, 4]
def baseStart_8098352 : Nat := 118140960795 + 8098352 * 2 ^ 59
def prefixEnd_8098352 : Nat := 4983230072969 + 3 ^ 40 * 8098352 * 2
def baseEnd_8098352 : Nat := 4158347085299804394256363

theorem tailTrace_8098352 : CollatzResearch.WordTrace tailWord_8098352 prefixEnd_8098352 4158347085299804394256363 := by
  unfold tailWord_8098352
  simp only [CollatzResearch.WordTrace]
  refine ⟨147685581578530633626708655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196914108771374178168944873 147685581578530633626708655)
  ·
    refine ⟨221528372367795950440062983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147685581578530633626708655 221528372367795950440062983)
    ·
      refine ⟨332292558551693925660094475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 221528372367795950440062983 332292558551693925660094475)
      ·
        refine ⟨498438837827540888490141713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 332292558551693925660094475 498438837827540888490141713)
        ·
          refine ⟨373829128370655666367606285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 498438837827540888490141713 373829128370655666367606285)
          ·
            refine ⟨140185923138995874887852357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 373829128370655666367606285 140185923138995874887852357)
            ·
              refine ⟨26284860588561726541472317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 140185923138995874887852357 26284860588561726541472317)
              ·
                refine ⟨9856822720710647453052119, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26284860588561726541472317 9856822720710647453052119)
                ·
                  refine ⟨14785234081065971179578179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9856822720710647453052119 14785234081065971179578179)
                  ·
                    refine ⟨22177851121598956769367269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14785234081065971179578179 22177851121598956769367269)
                    ·
                      refine ⟨4158347085299804394256363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22177851121598956769367269 4158347085299804394256363)
                      ·
                        rfl

theorem cell23_8098352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 4, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 4, 3, 1, 1, 4].length) (baseStart_8098352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8098352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8098352 prefixEnd_8098352 := by exact prefixLift 8098352
  have htrace : WordTrace (prefixWord ++ tailWord_8098352) baseStart_8098352 baseEnd_8098352 := by
    simpa [prefixWord, tailWord_8098352, baseEnd_8098352] using wordTrace_append hprefix tailTrace_8098352
  have hstable : (prefixWord ++ tailWord_8098352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8098352).length < 2 ^ (prefixWord ++ tailWord_8098352).sum := by decide
  have hdescent : baseEnd_8098352 < baseStart_8098352 := by decide
  rcases family_descends (prefixWord ++ tailWord_8098352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8098362 : List Nat := [3, 1, 1, 1, 3, 3, 2, 1, 4, 4]
def baseStart_8098362 : Nat := 118140960795 + 8098362 * 2 ^ 59
def prefixEnd_8098362 : Nat := 4983230072969 + 3 ^ 40 * 8098362 * 2
def baseEnd_8098362 : Nat := 1386117406702116451710439

theorem tailTrace_8098362 : CollatzResearch.WordTrace tailWord_8098362 prefixEnd_8098362 1386117406702116451710439 := by
  unfold tailWord_8098362
  simp only [CollatzResearch.WordTrace]
  refine ⟨73842881971756259740320335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 196914351924683359307520893 73842881971756259740320335)
  ·
    refine ⟨110764322957634389610480503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73842881971756259740320335 110764322957634389610480503)
    ·
      refine ⟨166146484436451584415720755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110764322957634389610480503 166146484436451584415720755)
      ·
        refine ⟨249219726654677376623581133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166146484436451584415720755 249219726654677376623581133)
        ·
          refine ⟨93457397495504016233842925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 249219726654677376623581133 93457397495504016233842925)
          ·
            refine ⟨35046524060814006087691097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 93457397495504016233842925 35046524060814006087691097)
            ·
              refine ⟨26284893045610504565768323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35046524060814006087691097 26284893045610504565768323)
              ·
                refine ⟨39427339568415756848652485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26284893045610504565768323 39427339568415756848652485)
                ·
                  refine ⟨7392626169077954409122341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39427339568415756848652485 7392626169077954409122341)
                  ·
                    refine ⟨1386117406702116451710439, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7392626169077954409122341 1386117406702116451710439)
                    ·
                      rfl

theorem cell23_8098362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 2, 1, 4, 4].length) (baseStart_8098362 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8098362 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8098362 prefixEnd_8098362 := by exact prefixLift 8098362
  have htrace : WordTrace (prefixWord ++ tailWord_8098362) baseStart_8098362 baseEnd_8098362 := by
    simpa [prefixWord, tailWord_8098362, baseEnd_8098362] using wordTrace_append hprefix tailTrace_8098362
  have hstable : (prefixWord ++ tailWord_8098362).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8098362).length < 2 ^ (prefixWord ++ tailWord_8098362).sum := by decide
  have hdescent : baseEnd_8098362 < baseStart_8098362 := by decide
  rcases family_descends (prefixWord ++ tailWord_8098362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8098375 : List Nat := [1, 1, 4, 1, 4, 1, 1, 10]
def baseStart_8098375 : Nat := 118140960795 + 8098375 * 2 ^ 59
def prefixEnd_8098375 : Nat := 4983230072969 + 3 ^ 40 * 8098375 * 2
def baseEnd_8098375 : Nat := 154013292420550289046991

theorem tailTrace_8098375 : CollatzResearch.WordTrace tailWord_8098375 prefixEnd_8098375 154013292420550289046991 := by
  unfold tailWord_8098375
  simp only [CollatzResearch.WordTrace]
  refine ⟨295372002035977942181504579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196914668023985294787669719 295372002035977942181504579)
  ·
    refine ⟨443058003053966913272256869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 295372002035977942181504579 443058003053966913272256869)
    ·
      refine ⟨83073375572618796238548163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 443058003053966913272256869 83073375572618796238548163)
      ·
        refine ⟨124610063358928194357822245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83073375572618796238548163 124610063358928194357822245)
        ·
          refine ⟨23364386879799036442091671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 124610063358928194357822245 23364386879799036442091671)
          ·
            refine ⟨35046580319698554663137507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23364386879799036442091671 35046580319698554663137507)
            ·
              refine ⟨52569870479547831994706261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35046580319698554663137507 52569870479547831994706261)
              ·
                refine ⟨154013292420550289046991, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 52569870479547831994706261 154013292420550289046991)
                ·
                  rfl

theorem cell23_8098375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 1, 10].length) (baseStart_8098375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8098375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8098375 prefixEnd_8098375 := by exact prefixLift 8098375
  have htrace : WordTrace (prefixWord ++ tailWord_8098375) baseStart_8098375 baseEnd_8098375 := by
    simpa [prefixWord, tailWord_8098375, baseEnd_8098375] using wordTrace_append hprefix tailTrace_8098375
  have hstable : (prefixWord ++ tailWord_8098375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8098375).length < 2 ^ (prefixWord ++ tailWord_8098375).sum := by decide
  have hdescent : baseEnd_8098375 < baseStart_8098375 := by decide
  rcases family_descends (prefixWord ++ tailWord_8098375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8098379 : List Nat := [1, 1, 1, 1, 3, 1, 8, 1, 2, 4]
def baseStart_8098379 : Nat := 118140960795 + 8098379 * 2 ^ 59
def prefixEnd_8098379 : Nat := 4983230072969 + 3 ^ 40 * 8098379 * 2
def baseEnd_8098379 : Nat := 1386120316425825262872913

theorem tailTrace_8098379 : CollatzResearch.WordTrace tailWord_8098379 prefixEnd_8098379 1386120316425825262872913 := by
  unfold tailWord_8098379
  simp only [CollatzResearch.WordTrace]
  refine ⟨295372147927963450864650191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196914765285308967243100127 295372147927963450864650191)
  ·
    refine ⟨443058221891945176296975287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 295372147927963450864650191 443058221891945176296975287)
    ·
      refine ⟨664587332837917764445462931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 443058221891945176296975287 664587332837917764445462931)
      ·
        refine ⟨996880999256876646668194397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 664587332837917764445462931 996880999256876646668194397)
        ·
          refine ⟨373830374721328742500572899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 996880999256876646668194397 373830374721328742500572899)
          ·
            refine ⟨560745562081993113750859349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 373830374721328742500572899 560745562081993113750859349)
            ·
              refine ⟨6571237055648356801767883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 560745562081993113750859349 6571237055648356801767883)
              ·
                refine ⟨9856855583472535202651825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6571237055648356801767883 9856855583472535202651825)
                ·
                  refine ⟨7392641687604401401988869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9856855583472535202651825 7392641687604401401988869)
                  ·
                    refine ⟨1386120316425825262872913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7392641687604401401988869 1386120316425825262872913)
                    ·
                      rfl

theorem cell23_8098379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 8, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 8, 1, 2, 4].length) (baseStart_8098379 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8098379 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8098379 prefixEnd_8098379 := by exact prefixLift 8098379
  have htrace : WordTrace (prefixWord ++ tailWord_8098379) baseStart_8098379 baseEnd_8098379 := by
    simpa [prefixWord, tailWord_8098379, baseEnd_8098379] using wordTrace_append hprefix tailTrace_8098379
  have hstable : (prefixWord ++ tailWord_8098379).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8098379).length < 2 ^ (prefixWord ++ tailWord_8098379).sum := by decide
  have hdescent : baseEnd_8098379 < baseStart_8098379 := by decide
  rcases family_descends (prefixWord ++ tailWord_8098379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8098389 : List Nat := [1, 3, 2, 2, 1, 1, 5, 2, 1, 2, 3]
def baseStart_8098389 : Nat := 118140960795 + 8098389 * 2 ^ 59
def prefixEnd_8098389 : Nat := 4983230072969 + 3 ^ 40 * 8098389 * 2
def baseEnd_8098389 : Nat := 4158366084084020749493693

theorem tailTrace_8098389 : CollatzResearch.WordTrace tailWord_8098389 prefixEnd_8098389 4158366084084020749493693 := by
  unfold tailWord_8098389
  simp only [CollatzResearch.WordTrace]
  refine ⟨295372512657927222572514221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196915008438618148381676147 295372512657927222572514221)
  ·
    refine ⟨110764692246722708464692833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 295372512657927222572514221 110764692246722708464692833)
    ·
      refine ⟨83073519185042031348519625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110764692246722708464692833 83073519185042031348519625)
      ·
        refine ⟨62305139388781523511389719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83073519185042031348519625 62305139388781523511389719)
        ·
          refine ⟨93457709083172285267084579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62305139388781523511389719 93457709083172285267084579)
          ·
            refine ⟨140186563624758427900626869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93457709083172285267084579 140186563624758427900626869)
            ·
              refine ⟨13142490339821102615683769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 140186563624758427900626869 13142490339821102615683769)
              ·
                refine ⟨9856867754865826961762827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13142490339821102615683769 9856867754865826961762827)
                ·
                  refine ⟨14785301632298740442644241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9856867754865826961762827 14785301632298740442644241)
                  ·
                    refine ⟨11088976224224055331983181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14785301632298740442644241 11088976224224055331983181)
                    ·
                      refine ⟨4158366084084020749493693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11088976224224055331983181 4158366084084020749493693)
                      ·
                        rfl

theorem cell23_8098389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 5, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 5, 2, 1, 2, 3].length) (baseStart_8098389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8098389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8098389 prefixEnd_8098389 := by exact prefixLift 8098389
  have htrace : WordTrace (prefixWord ++ tailWord_8098389) baseStart_8098389 baseEnd_8098389 := by
    simpa [prefixWord, tailWord_8098389, baseEnd_8098389] using wordTrace_append hprefix tailTrace_8098389
  have hstable : (prefixWord ++ tailWord_8098389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8098389).length < 2 ^ (prefixWord ++ tailWord_8098389).sum := by decide
  have hdescent : baseEnd_8098389 < baseStart_8098389 := by decide
  rcases family_descends (prefixWord ++ tailWord_8098389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8098415 : List Nat := [1, 1, 2, 1, 3, 2, 2, 2, 2, 2, 5]
def baseStart_8098415 : Nat := 118140960795 + 8098415 * 2 ^ 59
def prefixEnd_8098415 : Nat := 4983230072969 + 3 ^ 40 * 8098415 * 2
def baseEnd_8098415 : Nat := 4158379434581037647768573

theorem tailTrace_8098415 : CollatzResearch.WordTrace tailWord_8098415 prefixEnd_8098415 4158379434581037647768573 := by
  unfold tailWord_8098415
  simp only [CollatzResearch.WordTrace]
  refine ⟨295373460955833029012960699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196915640637222019341973799 295373460955833029012960699)
  ·
    refine ⟨443060191433749543519441049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 295373460955833029012960699 443060191433749543519441049)
    ·
      refine ⟨332295143575312157639580787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 443060191433749543519441049 332295143575312157639580787)
      ·
        refine ⟨498442715362968236459371181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 332295143575312157639580787 498442715362968236459371181)
        ·
          refine ⟨186916018261113088672264193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 498442715362968236459371181 186916018261113088672264193)
          ·
            refine ⟨140187013695834816504198145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 186916018261113088672264193 140187013695834816504198145)
            ·
              refine ⟨105140260271876112378148609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 140187013695834816504198145 105140260271876112378148609)
              ·
                refine ⟨78855195203907084283611457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 105140260271876112378148609 78855195203907084283611457)
                ·
                  refine ⟨59141396402930313212708593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 78855195203907084283611457 59141396402930313212708593)
                  ·
                    refine ⟨44356047302197734909531445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 59141396402930313212708593 44356047302197734909531445)
                    ·
                      refine ⟨4158379434581037647768573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44356047302197734909531445 4158379434581037647768573)
                      ·
                        rfl

theorem cell23_8098415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 2, 2, 2, 2, 5].length) (baseStart_8098415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8098415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8098415 prefixEnd_8098415 := by exact prefixLift 8098415
  have htrace : WordTrace (prefixWord ++ tailWord_8098415) baseStart_8098415 baseEnd_8098415 := by
    simpa [prefixWord, tailWord_8098415, baseEnd_8098415] using wordTrace_append hprefix tailTrace_8098415
  have hstable : (prefixWord ++ tailWord_8098415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8098415).length < 2 ^ (prefixWord ++ tailWord_8098415).sum := by decide
  have hdescent : baseEnd_8098415 < baseStart_8098415 := by decide
  rcases family_descends (prefixWord ++ tailWord_8098415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8098435 : List Nat := [1, 1, 1, 3, 3, 1, 3, 1, 1, 8]
def baseStart_8098435 : Nat := 118140960795 + 8098435 * 2 ^ 59
def prefixEnd_8098435 : Nat := 4983230072969 + 3 ^ 40 * 8098435 * 2
def baseEnd_8098435 : Nat := 1386129901398042523172827

theorem tailTrace_8098435 : CollatzResearch.WordTrace tailWord_8098435 prefixEnd_8098435 1386129901398042523172827 := by
  unfold tailWord_8098435
  simp only [CollatzResearch.WordTrace]
  refine ⟨295374190415760572428688759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196916126943840381619125839 295374190415760572428688759)
  ·
    refine ⟨443061285623640858643033139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 295374190415760572428688759 443061285623640858643033139)
    ·
      refine ⟨664591928435461287964549709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 443061285623640858643033139 664591928435461287964549709)
      ·
        refine ⟨249221973163297982986706141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 664591928435461287964549709 249221973163297982986706141)
        ·
          refine ⟨93458239936236743620014803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 249221973163297982986706141 93458239936236743620014803)
          ·
            refine ⟨140187359904355115430022205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93458239936236743620014803 140187359904355115430022205)
            ·
              refine ⟨52570259964133168286258327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 140187359904355115430022205 52570259964133168286258327)
              ·
                refine ⟨78855389946199752429387491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52570259964133168286258327 78855389946199752429387491)
                ·
                  refine ⟨118283084919299628644081237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 78855389946199752429387491 118283084919299628644081237)
                  ·
                    refine ⟨1386129901398042523172827, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 118283084919299628644081237 1386129901398042523172827)
                    ·
                      rfl

theorem cell23_8098435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 3, 1, 1, 8].length) (baseStart_8098435 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8098435 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8098435 prefixEnd_8098435 := by exact prefixLift 8098435
  have htrace : WordTrace (prefixWord ++ tailWord_8098435) baseStart_8098435 baseEnd_8098435 := by
    simpa [prefixWord, tailWord_8098435, baseEnd_8098435] using wordTrace_append hprefix tailTrace_8098435
  have hstable : (prefixWord ++ tailWord_8098435).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8098435).length < 2 ^ (prefixWord ++ tailWord_8098435).sum := by decide
  have hdescent : baseEnd_8098435 < baseStart_8098435 := by decide
  rcases family_descends (prefixWord ++ tailWord_8098435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8098436 : List Nat := [2, 3, 2, 1, 3, 1, 2, 3, 2, 1, 3]
def baseStart_8098436 : Nat := 118140960795 + 8098436 * 2 ^ 59
def prefixEnd_8098436 : Nat := 4983230072969 + 3 ^ 40 * 8098436 * 2
def baseEnd_8098436 : Nat := 4158390217674782065605977

theorem tailTrace_8098436 : CollatzResearch.WordTrace tailWord_8098436 prefixEnd_8098436 4158390217674782065605977 := by
  unfold tailWord_8098436
  simp only [CollatzResearch.WordTrace]
  refine ⟨147687113444378474799737581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196916151259171299732983441 147687113444378474799737581)
  ·
    refine ⟨55382667541641928049901593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 147687113444378474799737581 55382667541641928049901593)
    ·
      refine ⟨41537000656231446037426195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55382667541641928049901593 41537000656231446037426195)
      ·
        refine ⟨62305500984347169056139293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41537000656231446037426195 62305500984347169056139293)
        ·
          refine ⟨23364562869130188396052235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62305500984347169056139293 23364562869130188396052235)
          ·
            refine ⟨35046844303695282594078353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23364562869130188396052235 35046844303695282594078353)
            ·
              refine ⟨26285133227771461945558765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35046844303695282594078353 26285133227771461945558765)
              ·
                refine ⟨9856924960414298229584537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26285133227771461945558765 9856924960414298229584537)
                ·
                  refine ⟨7392693720310723672188403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9856924960414298229584537 7392693720310723672188403)
                  ·
                    refine ⟨11089040580466085508282605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7392693720310723672188403 11089040580466085508282605)
                    ·
                      refine ⟨4158390217674782065605977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11089040580466085508282605 4158390217674782065605977)
                      ·
                        rfl

theorem cell23_8098436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 2, 3, 2, 1, 3].length) (baseStart_8098436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8098436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8098436 prefixEnd_8098436 := by exact prefixLift 8098436
  have htrace : WordTrace (prefixWord ++ tailWord_8098436) baseStart_8098436 baseEnd_8098436 := by
    simpa [prefixWord, tailWord_8098436, baseEnd_8098436] using wordTrace_append hprefix tailTrace_8098436
  have hstable : (prefixWord ++ tailWord_8098436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8098436).length < 2 ^ (prefixWord ++ tailWord_8098436).sum := by decide
  have hdescent : baseEnd_8098436 < baseStart_8098436 := by decide
  rcases family_descends (prefixWord ++ tailWord_8098436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8098446 : List Nat := [4, 1, 1, 3, 1, 1, 2, 4, 1, 3, 2]
def baseStart_8098446 : Nat := 118140960795 + 8098446 * 2 ^ 59
def prefixEnd_8098446 : Nat := 4983230072969 + 3 ^ 40 * 8098446 * 2
def baseEnd_8098446 : Nat := 4158395352481327026480931

theorem tailTrace_8098446 : CollatzResearch.WordTrace tailWord_8098446 prefixEnd_8098446 4158395352481327026480931 := by
  unfold tailWord_8098446
  simp only [CollatzResearch.WordTrace]
  refine ⟨36921823952340090163417399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 196916394412480480871559461 36921823952340090163417399)
  ·
    refine ⟨55382735928510135245126099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36921823952340090163417399 55382735928510135245126099)
    ·
      refine ⟨83074103892765202867689149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55382735928510135245126099 83074103892765202867689149)
      ·
        refine ⟨31152788959786951075383431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 83074103892765202867689149 31152788959786951075383431)
        ·
          refine ⟨46729183439680426613075147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31152788959786951075383431 46729183439680426613075147)
          ·
            refine ⟨70093775159520639919612721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46729183439680426613075147 70093775159520639919612721)
            ·
              refine ⟨52570331369640479939709541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70093775159520639919612721 52570331369640479939709541)
              ·
                refine ⟨9856937131807589988695539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 52570331369640479939709541 9856937131807589988695539)
                ·
                  refine ⟨14785405697711384983043309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9856937131807589988695539 14785405697711384983043309)
                  ·
                    refine ⟨5544527136641769368641241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14785405697711384983043309 5544527136641769368641241)
                    ·
                      refine ⟨4158395352481327026480931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5544527136641769368641241 4158395352481327026480931)
                      ·
                        rfl

theorem cell23_8098446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 2, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 2, 4, 1, 3, 2].length) (baseStart_8098446 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8098446 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8098446 prefixEnd_8098446 := by exact prefixLift 8098446
  have htrace : WordTrace (prefixWord ++ tailWord_8098446) baseStart_8098446 baseEnd_8098446 := by
    simpa [prefixWord, tailWord_8098446, baseEnd_8098446] using wordTrace_append hprefix tailTrace_8098446
  have hstable : (prefixWord ++ tailWord_8098446).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8098446).length < 2 ^ (prefixWord ++ tailWord_8098446).sum := by decide
  have hdescent : baseEnd_8098446 < baseStart_8098446 := by decide
  rcases family_descends (prefixWord ++ tailWord_8098446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8098522 : List Nat := [3, 1, 1, 2, 2, 2, 2, 2, 1, 2, 5]
def baseStart_8098522 : Nat := 118140960795 + 8098522 * 2 ^ 59
def prefixEnd_8098522 : Nat := 4983230072969 + 3 ^ 40 * 8098522 * 2
def baseEnd_8098522 : Nat := 4158434377011068729130581

theorem tailTrace_8098522 : CollatzResearch.WordTrace tailWord_8098522 prefixEnd_8098522 4158434377011068729130581 := by
  unfold tailWord_8098522
  simp only [CollatzResearch.WordTrace]
  refine ⟨73844340891611346571776455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 196918242377630257524737213 73844340891611346571776455)
  ·
    refine ⟨110766511337417019857664683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73844340891611346571776455 110766511337417019857664683)
    ·
      refine ⟨166149767006125529786497025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110766511337417019857664683 166149767006125529786497025)
      ·
        refine ⟨124612325254594147339872769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 166149767006125529786497025 124612325254594147339872769)
        ·
          refine ⟨93459243940945610504904577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 124612325254594147339872769 93459243940945610504904577)
          ·
            refine ⟨70094432955709207878678433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 93459243940945610504904577 70094432955709207878678433)
            ·
              refine ⟨52570824716781905909008825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70094432955709207878678433 52570824716781905909008825)
              ·
                refine ⟨39428118537586429431756619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52570824716781905909008825 39428118537586429431756619)
                ·
                  refine ⟨59142177806379644147634929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39428118537586429431756619 59142177806379644147634929)
                  ·
                    refine ⟨44356633354784733110726197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 59142177806379644147634929 44356633354784733110726197)
                    ·
                      refine ⟨4158434377011068729130581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44356633354784733110726197 4158434377011068729130581)
                      ·
                        rfl

theorem cell23_8098522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 2, 2, 1, 2, 5].length) (baseStart_8098522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8098522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8098522 prefixEnd_8098522 := by exact prefixLift 8098522
  have htrace : WordTrace (prefixWord ++ tailWord_8098522) baseStart_8098522 baseEnd_8098522 := by
    simpa [prefixWord, tailWord_8098522, baseEnd_8098522] using wordTrace_append hprefix tailTrace_8098522
  have hstable : (prefixWord ++ tailWord_8098522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8098522).length < 2 ^ (prefixWord ++ tailWord_8098522).sum := by decide
  have hdescent : baseEnd_8098522 < baseStart_8098522 := by decide
  rcases family_descends (prefixWord ++ tailWord_8098522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8098529 : List Nat := [1, 2, 3, 1, 4, 2, 1, 2, 2, 5]
def baseStart_8098529 : Nat := 118140960795 + 8098529 * 2 ^ 59
def prefixEnd_8098529 : Nat := 4983230072969 + 3 ^ 40 * 8098529 * 2
def baseEnd_8098529 : Nat := 1386145990458550067247683

theorem tailTrace_8098529 : CollatzResearch.WordTrace tailWord_8098529 prefixEnd_8098529 1386145990458550067247683 := by
  unfold tailWord_8098529
  simp only [CollatzResearch.WordTrace]
  refine ⟨295377618877420026482610641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196918412584946684321740427 295377618877420026482610641)
  ·
    refine ⟨221533214158065019861957981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 295377618877420026482610641 221533214158065019861957981)
    ·
      refine ⟨83074955309274382448234243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 221533214158065019861957981 83074955309274382448234243)
      ·
        refine ⟨124612432963911573672351365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83074955309274382448234243 124612432963911573672351365)
        ·
          refine ⟨23364831180733420063565881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 124612432963911573672351365 23364831180733420063565881)
          ·
            refine ⟨17523623385550065047674411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23364831180733420063565881 17523623385550065047674411)
            ·
              refine ⟨26285435078325097571511617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17523623385550065047674411 26285435078325097571511617)
              ·
                refine ⟨19714076308743823178633713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26285435078325097571511617 19714076308743823178633713)
                ·
                  refine ⟨14785557231557867383975285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19714076308743823178633713 14785557231557867383975285)
                  ·
                    refine ⟨1386145990458550067247683, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14785557231557867383975285 1386145990458550067247683)
                    ·
                      rfl

theorem cell23_8098529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 2, 1, 2, 2, 5].length) (baseStart_8098529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8098529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8098529 prefixEnd_8098529 := by exact prefixLift 8098529
  have htrace : WordTrace (prefixWord ++ tailWord_8098529) baseStart_8098529 baseEnd_8098529 := by
    simpa [prefixWord, tailWord_8098529, baseEnd_8098529] using wordTrace_append hprefix tailTrace_8098529
  have hstable : (prefixWord ++ tailWord_8098529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8098529).length < 2 ^ (prefixWord ++ tailWord_8098529).sum := by decide
  have hdescent : baseEnd_8098529 < baseStart_8098529 := by decide
  rcases family_descends (prefixWord ++ tailWord_8098529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8098569 : List Nat := [1, 2, 1, 1, 3, 2, 3, 3, 2, 2, 3]
def baseStart_8098569 : Nat := 118140960795 + 8098569 * 2 ^ 59
def prefixEnd_8098569 : Nat := 4983230072969 + 3 ^ 40 * 8098569 * 2
def baseEnd_8098569 : Nat := 4158458510601830045242865

theorem tailTrace_8098569 : CollatzResearch.WordTrace tailWord_8098569 prefixEnd_8098569 4158458510601830045242865 := by
  unfold tailWord_8098569
  simp only [CollatzResearch.WordTrace]
  refine ⟨295379077797275113314066761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196919385198183408876044507 295379077797275113314066761)
  ·
    refine ⟨221534308347956334985550071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 295379077797275113314066761 221534308347956334985550071)
    ·
      refine ⟨332301462521934502478325107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 221534308347956334985550071 332301462521934502478325107)
      ·
        refine ⟨498452193782901753717487661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 332301462521934502478325107 498452193782901753717487661)
        ·
          refine ⟨186919572668588157644057873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 498452193782901753717487661 186919572668588157644057873)
          ·
            refine ⟨140189679501441118233043405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 186919572668588157644057873 140189679501441118233043405)
            ·
              refine ⟨52571129813040419337391277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 140189679501441118233043405 52571129813040419337391277)
              ·
                refine ⟨19714173679890157251521729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52571129813040419337391277 19714173679890157251521729)
                ·
                  refine ⟨14785630259917617938641297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19714173679890157251521729 14785630259917617938641297)
                  ·
                    refine ⟨11089222694938213453980973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14785630259917617938641297 11089222694938213453980973)
                    ·
                      refine ⟨4158458510601830045242865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11089222694938213453980973 4158458510601830045242865)
                      ·
                        rfl

theorem cell23_8098569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 3, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 3, 3, 2, 2, 3].length) (baseStart_8098569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8098569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8098569 prefixEnd_8098569 := by exact prefixLift 8098569
  have htrace : WordTrace (prefixWord ++ tailWord_8098569) baseStart_8098569 baseEnd_8098569 := by
    simpa [prefixWord, tailWord_8098569, baseEnd_8098569] using wordTrace_append hprefix tailTrace_8098569
  have hstable : (prefixWord ++ tailWord_8098569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8098569).length < 2 ^ (prefixWord ++ tailWord_8098569).sum := by decide
  have hdescent : baseEnd_8098569 < baseStart_8098569 := by decide
  rcases family_descends (prefixWord ++ tailWord_8098569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8098606 : List Nat := [4, 1, 3, 2, 1, 1, 2, 3, 6]
def baseStart_8098606 : Nat := 118140960795 + 8098606 * 2 ^ 59
def prefixEnd_8098606 : Nat := 4983230072969 + 3 ^ 40 * 8098606 * 2
def baseEnd_8098606 : Nat := 462053056598449600053355

theorem tailTrace_8098606 : CollatzResearch.WordTrace tailWord_8098606 prefixEnd_8098606 462053056598449600053355 := by
  unfold tailWord_8098606
  simp only [CollatzResearch.WordTrace]
  refine ⟨36922553412267633579145459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 196920284865427379088775781 36922553412267633579145459)
  ·
    refine ⟨55383830118401450368718189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36922553412267633579145459 55383830118401450368718189)
    ·
      refine ⟨20768936294400543888269321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55383830118401450368718189 20768936294400543888269321)
      ·
        refine ⟨15576702220800407916201991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20768936294400543888269321 15576702220800407916201991)
        ·
          refine ⟨23365053331200611874302987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15576702220800407916201991 23365053331200611874302987)
          ·
            refine ⟨35047579996800917811454481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23365053331200611874302987 35047579996800917811454481)
            ·
              refine ⟨26285684997600688358590861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35047579996800917811454481 26285684997600688358590861)
              ·
                refine ⟨9857131874100258134471573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26285684997600688358590861 9857131874100258134471573)
                ·
                  refine ⟨462053056598449600053355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9857131874100258134471573 462053056598449600053355)
                  ·
                    rfl

theorem cell23_8098606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 2, 3, 6].length) (baseStart_8098606 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8098606 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8098606 prefixEnd_8098606 := by exact prefixLift 8098606
  have htrace : WordTrace (prefixWord ++ tailWord_8098606) baseStart_8098606 baseEnd_8098606 := by
    simpa [prefixWord, tailWord_8098606, baseEnd_8098606] using wordTrace_append hprefix tailTrace_8098606
  have hstable : (prefixWord ++ tailWord_8098606).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8098606).length < 2 ^ (prefixWord ++ tailWord_8098606).sum := by decide
  have hdescent : baseEnd_8098606 < baseStart_8098606 := by decide
  rcases family_descends (prefixWord ++ tailWord_8098606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8098616 : List Nat := [2, 1, 2, 1, 3, 2, 3, 2, 3, 1, 3]
def baseStart_8098616 : Nat := 118140960795 + 8098616 * 2 ^ 59
def prefixEnd_8098616 : Nat := 4983230072969 + 3 ^ 40 * 8098616 * 2
def baseEnd_8098616 : Nat := 4158482644192591361355149

theorem tailTrace_8098616 : CollatzResearch.WordTrace tailWord_8098616 prefixEnd_8098616 4158482644192591361355149 := by
  unfold tailWord_8098616
  simp only [CollatzResearch.WordTrace]
  refine ⟨147690396014052420170513851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196920528018736560227351801 147690396014052420170513851)
  ·
    refine ⟨221535594021078630255770777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147690396014052420170513851 221535594021078630255770777)
    ·
      refine ⟨166151695515808972691828083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 221535594021078630255770777 166151695515808972691828083)
      ·
        refine ⟨249227543273713459037742125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166151695515808972691828083 249227543273713459037742125)
        ·
          refine ⟨93460328727642547139153297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 249227543273713459037742125 93460328727642547139153297)
          ·
            refine ⟨70095246545731910354364973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 93460328727642547139153297 70095246545731910354364973)
            ·
              refine ⟨26285717454649466382886865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 70095246545731910354364973 26285717454649466382886865)
              ·
                refine ⟨19714288090987099787165149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26285717454649466382886865 19714288090987099787165149)
                ·
                  refine ⟨7392858034120162420186931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19714288090987099787165149 7392858034120162420186931)
                  ·
                    refine ⟨11089287051180243630280397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7392858034120162420186931 11089287051180243630280397)
                    ·
                      refine ⟨4158482644192591361355149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11089287051180243630280397 4158482644192591361355149)
                      ·
                        rfl

theorem cell23_8098616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 3, 2, 3, 1, 3].length) (baseStart_8098616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8098616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8098616 prefixEnd_8098616 := by exact prefixLift 8098616
  have htrace : WordTrace (prefixWord ++ tailWord_8098616) baseStart_8098616 baseEnd_8098616 := by
    simpa [prefixWord, tailWord_8098616, baseEnd_8098616] using wordTrace_append hprefix tailTrace_8098616
  have hstable : (prefixWord ++ tailWord_8098616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8098616).length < 2 ^ (prefixWord ++ tailWord_8098616).sum := by decide
  have hdescent : baseEnd_8098616 < baseStart_8098616 := by decide
  rcases family_descends (prefixWord ++ tailWord_8098616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8098633 : List Nat := [1, 2, 1, 1, 2, 5, 1, 5, 1, 1, 3]
def baseStart_8098633 : Nat := 118140960795 + 8098633 * 2 ^ 59
def prefixEnd_8098633 : Nat := 4983230072969 + 3 ^ 40 * 8098633 * 2
def baseEnd_8098633 : Nat := 4158491373363717794842571

theorem tailTrace_8098633 : CollatzResearch.WordTrace tailWord_8098633 prefixEnd_8098633 4158491373363717794842571 := by
  unfold tailWord_8098633
  simp only [CollatzResearch.WordTrace]
  refine ⟨295381412069043252244396553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196920941379362168162931035 295381412069043252244396553)
  ·
    refine ⟨221536059051782439183297415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 295381412069043252244396553 221536059051782439183297415)
    ·
      refine ⟨332304088577673658774946123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 221536059051782439183297415 332304088577673658774946123)
      ·
        refine ⟨498456132866510488162419185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 332304088577673658774946123 498456132866510488162419185)
        ·
          refine ⟨373842099649882866121814389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 498456132866510488162419185 373842099649882866121814389)
          ·
            refine ⟨35047696842176518698920099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 373842099649882866121814389 35047696842176518698920099)
            ·
              refine ⟨52571545263264778048380149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35047696842176518698920099 52571545263264778048380149)
              ·
                refine ⟨4928582368431072942035639, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 52571545263264778048380149 4928582368431072942035639)
                ·
                  refine ⟨7392873552646609413053459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4928582368431072942035639 7392873552646609413053459)
                  ·
                    refine ⟨11089310328969914119580189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7392873552646609413053459 11089310328969914119580189)
                    ·
                      refine ⟨4158491373363717794842571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11089310328969914119580189 4158491373363717794842571)
                      ·
                        rfl

theorem cell23_8098633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 1, 5, 1, 1, 3].length) (baseStart_8098633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8098633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8098633 prefixEnd_8098633 := by exact prefixLift 8098633
  have htrace : WordTrace (prefixWord ++ tailWord_8098633) baseStart_8098633 baseEnd_8098633 := by
    simpa [prefixWord, tailWord_8098633, baseEnd_8098633] using wordTrace_append hprefix tailTrace_8098633
  have hstable : (prefixWord ++ tailWord_8098633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8098633).length < 2 ^ (prefixWord ++ tailWord_8098633).sum := by decide
  have hdescent : baseEnd_8098633 < baseStart_8098633 := by decide
  rcases family_descends (prefixWord ++ tailWord_8098633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8098636 : List Nat := [2, 2, 1, 3, 3, 2, 1, 3, 1, 5]
def baseStart_8098636 : Nat := 118140960795 + 8098636 * 2 ^ 59
def prefixEnd_8098636 : Nat := 4983230072969 + 3 ^ 40 * 8098636 * 2
def baseEnd_8098636 : Nat := 1386164304601893761035019

theorem tailTrace_8098636 : CollatzResearch.WordTrace tailWord_8098636 prefixEnd_8098636 1386164304601893761035019 := by
  unfold tailWord_8098636
  simp only [CollatzResearch.WordTrace]
  refine ⟨147690760744016191878377881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196921014325354922504503841 147690760744016191878377881)
  ·
    refine ⟨110768070558012143908783411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147690760744016191878377881 110768070558012143908783411)
    ·
      refine ⟨166152105837018215863175117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110768070558012143908783411 166152105837018215863175117)
      ·
        refine ⟨62307039688881830948690669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 166152105837018215863175117 62307039688881830948690669)
        ·
          refine ⟨23365139883330686605759001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62307039688881830948690669 23365139883330686605759001)
          ·
            refine ⟨17523854912498014954319251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23365139883330686605759001 17523854912498014954319251)
            ·
              refine ⟨26285782368747022431478877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17523854912498014954319251 26285782368747022431478877)
              ·
                refine ⟨9857168388280133411804579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26285782368747022431478877 9857168388280133411804579)
                ·
                  refine ⟨14785752582420200117706869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9857168388280133411804579 14785752582420200117706869)
                  ·
                    refine ⟨1386164304601893761035019, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14785752582420200117706869 1386164304601893761035019)
                    ·
                      rfl

theorem cell23_8098636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 2, 1, 3, 1, 5].length) (baseStart_8098636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8098636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8098636 prefixEnd_8098636 := by exact prefixLift 8098636
  have htrace : WordTrace (prefixWord ++ tailWord_8098636) baseStart_8098636 baseEnd_8098636 := by
    simpa [prefixWord, tailWord_8098636, baseEnd_8098636] using wordTrace_append hprefix tailTrace_8098636
  have hstable : (prefixWord ++ tailWord_8098636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8098636).length < 2 ^ (prefixWord ++ tailWord_8098636).sum := by decide
  have hdescent : baseEnd_8098636 < baseStart_8098636 := by decide
  rcases family_descends (prefixWord ++ tailWord_8098636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8098639 : List Nat := [1, 1, 2, 1, 1, 2, 1, 1, 3, 8, 2]
def baseStart_8098639 : Nat := 118140960795 + 8098639 * 2 ^ 59
def prefixEnd_8098639 : Nat := 4983230072969 + 3 ^ 40 * 8098639 * 2
def baseEnd_8098639 : Nat := 4158494454247644771367543

theorem tailTrace_8098639 : CollatzResearch.WordTrace tailWord_8098639 prefixEnd_8098639 4158494454247644771367543 := by
  unfold tailWord_8098639
  simp only [CollatzResearch.WordTrace]
  refine ⟨295381630907021515269114971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196921087271347676846076647 295381630907021515269114971)
  ·
    refine ⟨443072446360532272903672457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 295381630907021515269114971 443072446360532272903672457)
    ·
      refine ⟨332304334770399204677754343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 443072446360532272903672457 332304334770399204677754343)
      ·
        refine ⟨498456502155598807016631515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 332304334770399204677754343 498456502155598807016631515)
        ·
          refine ⟨747684753233398210524947273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 498456502155598807016631515 747684753233398210524947273)
          ·
            refine ⟨560763564925048657893710455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 747684753233398210524947273 560763564925048657893710455)
            ·
              refine ⟨841145347387572986840565683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 560763564925048657893710455 841145347387572986840565683)
              ·
                refine ⟨1261718021081359480260848525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 841145347387572986840565683 1261718021081359480260848525)
                ·
                  refine ⟨473144257905509805097818197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1261718021081359480260848525 473144257905509805097818197)
                  ·
                    refine ⟨5544659272330193028490057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 473144257905509805097818197 5544659272330193028490057)
                    ·
                      refine ⟨4158494454247644771367543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5544659272330193028490057 4158494454247644771367543)
                      ·
                        rfl

theorem cell23_8098639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 1, 3, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 1, 3, 8, 2].length) (baseStart_8098639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8098639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8098639 prefixEnd_8098639 := by exact prefixLift 8098639
  have htrace : WordTrace (prefixWord ++ tailWord_8098639) baseStart_8098639 baseEnd_8098639 := by
    simpa [prefixWord, tailWord_8098639, baseEnd_8098639] using wordTrace_append hprefix tailTrace_8098639
  have hstable : (prefixWord ++ tailWord_8098639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8098639).length < 2 ^ (prefixWord ++ tailWord_8098639).sum := by decide
  have hdescent : baseEnd_8098639 < baseStart_8098639 := by decide
  rcases family_descends (prefixWord ++ tailWord_8098639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8098659 : List Nat := [1, 1, 1, 5, 3, 1, 1, 1, 3, 1, 5]
def baseStart_8098659 : Nat := 118140960795 + 8098659 * 2 ^ 59
def prefixEnd_8098659 : Nat := 4983230072969 + 3 ^ 40 * 8098659 * 2
def baseEnd_8098659 : Nat := 4158504723860734693117451

theorem tailTrace_8098659 : CollatzResearch.WordTrace tailWord_8098659 prefixEnd_8098659 4158504723860734693117451 := by
  unfold tailWord_8098659
  simp only [CollatzResearch.WordTrace]
  refine ⟨295382360366949058684843031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196921573577966039123228687 295382360366949058684843031)
  ·
    refine ⟨443073540550423588027264547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 295382360366949058684843031 443073540550423588027264547)
    ·
      refine ⟨664610310825635382040896821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 443073540550423588027264547 664610310825635382040896821)
      ·
        refine ⟨62307216639903317066334077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 664610310825635382040896821 62307216639903317066334077)
        ·
          refine ⟨23365206239963743899875279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62307216639903317066334077 23365206239963743899875279)
          ·
            refine ⟨35047809359945615849812919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23365206239963743899875279 35047809359945615849812919)
            ·
              refine ⟨52571714039918423774719379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35047809359945615849812919 52571714039918423774719379)
              ·
                refine ⟨78857571059877635662079069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52571714039918423774719379 78857571059877635662079069)
                ·
                  refine ⟨29571589147454113373279651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 78857571059877635662079069 29571589147454113373279651)
                  ·
                    refine ⟨44357383721181170059919477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29571589147454113373279651 44357383721181170059919477)
                    ·
                      refine ⟨4158504723860734693117451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44357383721181170059919477 4158504723860734693117451)
                      ·
                        rfl

theorem cell23_8098659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 1, 1, 3, 1, 5].length) (baseStart_8098659 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8098659 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8098659 prefixEnd_8098659 := by exact prefixLift 8098659
  have htrace : WordTrace (prefixWord ++ tailWord_8098659) baseStart_8098659 baseEnd_8098659 := by
    simpa [prefixWord, tailWord_8098659, baseEnd_8098659] using wordTrace_append hprefix tailTrace_8098659
  have hstable : (prefixWord ++ tailWord_8098659).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8098659).length < 2 ^ (prefixWord ++ tailWord_8098659).sum := by decide
  have hdescent : baseEnd_8098659 < baseStart_8098659 := by decide
  rcases family_descends (prefixWord ++ tailWord_8098659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8098673 : List Nat := [1, 2, 2, 2, 1, 4, 2, 2, 3, 2, 2]
def baseStart_8098673 : Nat := 118140960795 + 8098673 * 2 ^ 59
def prefixEnd_8098673 : Nat := 4983230072969 + 3 ^ 40 * 8098673 * 2
def baseEnd_8098673 : Nat := 4158511912589897638342387

theorem tailTrace_8098673 : CollatzResearch.WordTrace tailWord_8098673 prefixEnd_8098673 4158511912589897638342387 := by
  unfold tailWord_8098673
  simp only [CollatzResearch.WordTrace]
  refine ⟨295382870988898339075852673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196921913992598892717235115 295382870988898339075852673)
  ·
    refine ⟨221537153241673754306889505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 295382870988898339075852673 221537153241673754306889505)
    ·
      refine ⟨166152864931255315730167129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 221537153241673754306889505 166152864931255315730167129)
      ·
        refine ⟨124614648698441486797625347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 166152864931255315730167129 124614648698441486797625347)
        ·
          refine ⟨186921973047662230196438021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124614648698441486797625347 186921973047662230196438021)
          ·
            refine ⟨35047869946436668161832129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 186921973047662230196438021 35047869946436668161832129)
            ·
              refine ⟨26285902459827501121374097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35047869946436668161832129 26285902459827501121374097)
              ·
                refine ⟨19714426844870625841030573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26285902459827501121374097 19714426844870625841030573)
                ·
                  refine ⟨7392910066826484690386465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19714426844870625841030573 7392910066826484690386465)
                  ·
                    refine ⟨5544682550119863517789849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7392910066826484690386465 5544682550119863517789849)
                    ·
                      refine ⟨4158511912589897638342387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5544682550119863517789849 4158511912589897638342387)
                      ·
                        rfl

theorem cell23_8098673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 2, 2, 3, 2, 2].length) (baseStart_8098673 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8098673 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8098673 prefixEnd_8098673 := by exact prefixLift 8098673
  have htrace : WordTrace (prefixWord ++ tailWord_8098673) baseStart_8098673 baseEnd_8098673 := by
    simpa [prefixWord, tailWord_8098673, baseEnd_8098673] using wordTrace_append hprefix tailTrace_8098673
  have hstable : (prefixWord ++ tailWord_8098673).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8098673).length < 2 ^ (prefixWord ++ tailWord_8098673).sum := by decide
  have hdescent : baseEnd_8098673 < baseStart_8098673 := by decide
  rcases family_descends (prefixWord ++ tailWord_8098673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8098710 : List Nat := [5, 3, 1, 1, 1, 1, 2, 2, 1, 1, 5]
def baseStart_8098710 : Nat := 118140960795 + 8098710 * 2 ^ 59
def prefixEnd_8098710 : Nat := 4983230072969 + 3 ^ 40 * 8098710 * 2
def baseEnd_8098710 : Nat := 4158530911374113993579717

theorem tailTrace_8098710 : CollatzResearch.WordTrace tailWord_8098710 prefixEnd_8098710 4158530911374113993579717 := by
  unfold tailWord_8098710
  simp only [CollatzResearch.WordTrace]
  refine ⟨18461513780610268399684349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 196922813659842862929966389 18461513780610268399684349)
  ·
    refine ⟨6923067667728850649881631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18461513780610268399684349 6923067667728850649881631)
    ·
      refine ⟨10384601501593275974822447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6923067667728850649881631 10384601501593275974822447)
      ·
        refine ⟨15576902252389913962233671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10384601501593275974822447 15576902252389913962233671)
        ·
          refine ⟨23365353378584870943350507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15576902252389913962233671 23365353378584870943350507)
          ·
            refine ⟨35048030067877306415025761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23365353378584870943350507 35048030067877306415025761)
            ·
              refine ⟨26286022550907979811269321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35048030067877306415025761 26286022550907979811269321)
              ·
                refine ⟨19714516913180984858451991, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26286022550907979811269321 19714516913180984858451991)
                ·
                  refine ⟨29571775369771477287677987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19714516913180984858451991 29571775369771477287677987)
                  ·
                    refine ⟨44357663054657215931516981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29571775369771477287677987 44357663054657215931516981)
                    ·
                      refine ⟨4158530911374113993579717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44357663054657215931516981 4158530911374113993579717)
                      ·
                        rfl

theorem cell23_8098710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 2, 2, 1, 1, 5].length) (baseStart_8098710 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8098710 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8098710 prefixEnd_8098710 := by exact prefixLift 8098710
  have htrace : WordTrace (prefixWord ++ tailWord_8098710) baseStart_8098710 baseEnd_8098710 := by
    simpa [prefixWord, tailWord_8098710, baseEnd_8098710] using wordTrace_append hprefix tailTrace_8098710
  have hstable : (prefixWord ++ tailWord_8098710).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8098710).length < 2 ^ (prefixWord ++ tailWord_8098710).sum := by decide
  have hdescent : baseEnd_8098710 < baseStart_8098710 := by decide
  rcases family_descends (prefixWord ++ tailWord_8098710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8098727 : List Nat := [1, 1, 6, 1, 4, 1, 1, 2, 1, 2, 3]
def baseStart_8098727 : Nat := 118140960795 + 8098727 * 2 ^ 59
def prefixEnd_8098727 : Nat := 4983230072969 + 3 ^ 40 * 8098727 * 2
def baseEnd_8098727 : Nat := 4158539640545240427067139

theorem tailTrace_8098727 : CollatzResearch.WordTrace tailWord_8098727 prefixEnd_8098727 4158539640545240427067139 := by
  unfold tailWord_8098727
  simp only [CollatzResearch.WordTrace]
  refine ⟨295384840530702706298318435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196923227020468470865545623 295384840530702706298318435)
  ·
    refine ⟨443077260796054059447477653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 295384840530702706298318435 443077260796054059447477653)
    ·
      refine ⟨20769246599815034036600515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 443077260796054059447477653 20769246599815034036600515)
      ·
        refine ⟨31153869899722551054900773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20769246599815034036600515 31153869899722551054900773)
        ·
          refine ⟨5841350606197978322793895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31153869899722551054900773 5841350606197978322793895)
          ·
            refine ⟨8762025909296967484190843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5841350606197978322793895 8762025909296967484190843)
            ·
              refine ⟨13143038863945451226286265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8762025909296967484190843 13143038863945451226286265)
              ·
                refine ⟨9857279147959088419714699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13143038863945451226286265 9857279147959088419714699)
                ·
                  refine ⟨14785918721938632629572049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9857279147959088419714699 14785918721938632629572049)
                  ·
                    refine ⟨11089439041453974472179037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14785918721938632629572049 11089439041453974472179037)
                    ·
                      refine ⟨4158539640545240427067139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11089439041453974472179037 4158539640545240427067139)
                      ·
                        rfl

theorem cell23_8098727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 4, 1, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 4, 1, 1, 2, 1, 2, 3].length) (baseStart_8098727 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8098727 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8098727 prefixEnd_8098727 := by exact prefixLift 8098727
  have htrace : WordTrace (prefixWord ++ tailWord_8098727) baseStart_8098727 baseEnd_8098727 := by
    simpa [prefixWord, tailWord_8098727, baseEnd_8098727] using wordTrace_append hprefix tailTrace_8098727
  have hstable : (prefixWord ++ tailWord_8098727).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8098727).length < 2 ^ (prefixWord ++ tailWord_8098727).sum := by decide
  have hdescent : baseEnd_8098727 < baseStart_8098727 := by decide
  rcases family_descends (prefixWord ++ tailWord_8098727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8098740 : List Nat := [2, 5, 2, 1, 1, 2, 1, 2, 1, 3, 3]
def baseStart_8098740 : Nat := 118140960795 + 8098740 * 2 ^ 59
def prefixEnd_8098740 : Nat := 4983230072969 + 3 ^ 40 * 8098740 * 2
def baseEnd_8098740 : Nat := 4158546315793748876204579

theorem tailTrace_8098740 : CollatzResearch.WordTrace tailWord_8098740 prefixEnd_8098740 4158546315793748876204579 := by
  unfold tailWord_8098740
  simp only [CollatzResearch.WordTrace]
  refine ⟨147692657339827804759270837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196923543119770406345694449 147692657339827804759270837)
  ·
    refine ⟨13846186625608856696181641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 147692657339827804759270837 13846186625608856696181641)
    ·
      refine ⟨10384639969206642522136231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13846186625608856696181641 10384639969206642522136231)
      ·
        refine ⟨15576959953809963783204347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10384639969206642522136231 15576959953809963783204347)
        ·
          refine ⟨23365439930714945674806521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15576959953809963783204347 23365439930714945674806521)
          ·
            refine ⟨17524079948036209256104891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23365439930714945674806521 17524079948036209256104891)
            ·
              refine ⟨26286119922054313884157337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17524079948036209256104891 26286119922054313884157337)
              ·
                refine ⟨19714589941540735413118003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26286119922054313884157337 19714589941540735413118003)
                ·
                  refine ⟨29571884912311103119677005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19714589941540735413118003 29571884912311103119677005)
                  ·
                    refine ⟨11089456842116663669878877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29571884912311103119677005 11089456842116663669878877)
                    ·
                      refine ⟨4158546315793748876204579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11089456842116663669878877 4158546315793748876204579)
                      ·
                        rfl

theorem cell23_8098740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 2, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 2, 1, 2, 1, 3, 3].length) (baseStart_8098740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8098740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8098740 prefixEnd_8098740 := by exact prefixLift 8098740
  have htrace : WordTrace (prefixWord ++ tailWord_8098740) baseStart_8098740 baseEnd_8098740 := by
    simpa [prefixWord, tailWord_8098740, baseEnd_8098740] using wordTrace_append hprefix tailTrace_8098740
  have hstable : (prefixWord ++ tailWord_8098740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8098740).length < 2 ^ (prefixWord ++ tailWord_8098740).sum := by decide
  have hdescent : baseEnd_8098740 < baseStart_8098740 := by decide
  rcases family_descends (prefixWord ++ tailWord_8098740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8098766 : List Nat := [4, 1, 1, 1, 2, 3, 1, 1, 2, 4, 3]
def baseStart_8098766 : Nat := 118140960795 + 8098766 * 2 ^ 59
def prefixEnd_8098766 : Nat := 4983230072969 + 3 ^ 40 * 8098766 * 2
def baseEnd_8098766 : Nat := 4158559666290765774479459

theorem tailTrace_8098766 : CollatzResearch.WordTrace tailWord_8098766 prefixEnd_8098766 4158559666290765774479459 := by
  unfold tailWord_8098766
  simp only [CollatzResearch.WordTrace]
  refine ⟨36923282872195176994873519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 196924175318374277305992101 36923282872195176994873519)
  ·
    refine ⟨55384924308292765492310279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36923282872195176994873519 55384924308292765492310279)
    ·
      refine ⟨83077386462439148238465419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55384924308292765492310279 83077386462439148238465419)
      ·
        refine ⟨124616079693658722357698129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83077386462439148238465419 124616079693658722357698129)
        ·
          refine ⟨93462059770244041768273597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 124616079693658722357698129 93462059770244041768273597)
          ·
            refine ⟨35048272413841515663102599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 93462059770244041768273597 35048272413841515663102599)
            ·
              refine ⟨52572408620762273494653899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35048272413841515663102599 52572408620762273494653899)
              ·
                refine ⟨78858612931143410241980849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52572408620762273494653899 78858612931143410241980849)
                ·
                  refine ⟨59143959698357557681485637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 78858612931143410241980849 59143959698357557681485637)
                  ·
                    refine ⟨11089492443442042065278557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 59143959698357557681485637 11089492443442042065278557)
                    ·
                      refine ⟨4158559666290765774479459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11089492443442042065278557 4158559666290765774479459)
                      ·
                        rfl

theorem cell23_8098766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 1, 1, 2, 4, 3].length) (baseStart_8098766 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8098766 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8098766 prefixEnd_8098766 := by exact prefixLift 8098766
  have htrace : WordTrace (prefixWord ++ tailWord_8098766) baseStart_8098766 baseEnd_8098766 := by
    simpa [prefixWord, tailWord_8098766, baseEnd_8098766] using wordTrace_append hprefix tailTrace_8098766
  have hstable : (prefixWord ++ tailWord_8098766).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8098766).length < 2 ^ (prefixWord ++ tailWord_8098766).sum := by decide
  have hdescent : baseEnd_8098766 < baseStart_8098766 := by decide
  rcases family_descends (prefixWord ++ tailWord_8098766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8098769 : List Nat := [1, 2, 2, 1, 2, 1, 4, 3, 7]
def baseStart_8098769 : Nat := 118140960795 + 8098769 * 2 ^ 59
def prefixEnd_8098769 : Nat := 4983230072969 + 3 ^ 40 * 8098769 * 2
def baseEnd_8098769 : Nat := 462062356303636584749105

theorem tailTrace_8098769 : CollatzResearch.WordTrace tailWord_8098769 prefixEnd_8098769 462062356303636584749105 := by
  unfold tailWord_8098769
  simp only [CollatzResearch.WordTrace]
  refine ⟨295386372396550547471347361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196924248264367031647564907 295386372396550547471347361)
  ·
    refine ⟨221539779297412910603510521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 295386372396550547471347361 221539779297412910603510521)
    ·
      refine ⟨166154834473059682952632891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 221539779297412910603510521 166154834473059682952632891)
      ·
        refine ⟨249232251709589524428949337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166154834473059682952632891 249232251709589524428949337)
        ·
          refine ⟨186924188782192143321712003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 249232251709589524428949337 186924188782192143321712003)
          ·
            refine ⟨280386283173288214982568005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 186924188782192143321712003 280386283173288214982568005)
            ·
              refine ⟨52572428094991540309231501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 280386283173288214982568005 52572428094991540309231501)
              ·
                refine ⟨19714660535621827615961813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52572428094991540309231501 19714660535621827615961813)
                ·
                  refine ⟨462062356303636584749105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19714660535621827615961813 462062356303636584749105)
                  ·
                    rfl

theorem cell23_8098769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 4, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 4, 3, 7].length) (baseStart_8098769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8098769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8098769 prefixEnd_8098769 := by exact prefixLift 8098769
  have htrace : WordTrace (prefixWord ++ tailWord_8098769) baseStart_8098769 baseEnd_8098769 := by
    simpa [prefixWord, tailWord_8098769, baseEnd_8098769] using wordTrace_append hprefix tailTrace_8098769
  have hstable : (prefixWord ++ tailWord_8098769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8098769).length < 2 ^ (prefixWord ++ tailWord_8098769).sum := by decide
  have hdescent : baseEnd_8098769 < baseStart_8098769 := by decide
  rcases family_descends (prefixWord ++ tailWord_8098769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8098776 : List Nat := [2, 1, 2, 2, 2, 4, 1, 1, 2, 2, 4]
def baseStart_8098776 : Nat := 118140960795 + 8098776 * 2 ^ 59
def prefixEnd_8098776 : Nat := 4983230072969 + 3 ^ 40 * 8098776 * 2
def baseEnd_8098776 : Nat := 4158564801097310735354413

theorem tailTrace_8098776 : CollatzResearch.WordTrace tailWord_8098776 prefixEnd_8098776 4158564801097310735354413 := by
  unfold tailWord_8098776
  simp only [CollatzResearch.WordTrace]
  refine ⟨147693313853762593833426091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196924418471683458444568121 147693313853762593833426091)
  ·
    refine ⟨221539970780643890750139137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147693313853762593833426091 221539970780643890750139137)
    ·
      refine ⟨166154978085482918062604353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 221539970780643890750139137 166154978085482918062604353)
      ·
        refine ⟨124616233564112188546953265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 166154978085482918062604353 124616233564112188546953265)
        ·
          refine ⟨93462175173084141410214949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 124616233564112188546953265 93462175173084141410214949)
          ·
            refine ⟨17524157844953276514415303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 93462175173084141410214949 17524157844953276514415303)
            ·
              refine ⟨26286236767429914771622955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17524157844953276514415303 26286236767429914771622955)
              ·
                refine ⟨39429355151144872157434433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26286236767429914771622955 39429355151144872157434433)
                ·
                  refine ⟨29572016363358654118075825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39429355151144872157434433 29572016363358654118075825)
                  ·
                    refine ⟨22179012272518990588556869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29572016363358654118075825 22179012272518990588556869)
                    ·
                      refine ⟨4158564801097310735354413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22179012272518990588556869 4158564801097310735354413)
                      ·
                        rfl

theorem cell23_8098776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 4, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 4, 1, 1, 2, 2, 4].length) (baseStart_8098776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8098776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8098776 prefixEnd_8098776 := by exact prefixLift 8098776
  have htrace : WordTrace (prefixWord ++ tailWord_8098776) baseStart_8098776 baseEnd_8098776 := by
    simpa [prefixWord, tailWord_8098776, baseEnd_8098776] using wordTrace_append hprefix tailTrace_8098776
  have hstable : (prefixWord ++ tailWord_8098776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8098776).length < 2 ^ (prefixWord ++ tailWord_8098776).sum := by decide
  have hdescent : baseEnd_8098776 < baseStart_8098776 := by decide
  rcases family_descends (prefixWord ++ tailWord_8098776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8098859 : List Nat := [1, 1, 1, 1, 2, 1, 5, 1, 10]
def baseStart_8098859 : Nat := 118140960795 + 8098859 * 2 ^ 59
def prefixEnd_8098859 : Nat := 4983230072969 + 3 ^ 40 * 8098859 * 2
def baseEnd_8098859 : Nat := 462067491110181545624059

theorem tailTrace_8098859 : CollatzResearch.WordTrace tailWord_8098859 prefixEnd_8098859 462067491110181545624059 := by
  unfold tailWord_8098859
  simp only [CollatzResearch.WordTrace]
  refine ⟨295389654966224492842123631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196926436644149661894749087 295389654966224492842123631)
  ·
    refine ⟨443084482449336739263185447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 295389654966224492842123631 443084482449336739263185447)
    ·
      refine ⟨664626723674005108894778171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 443084482449336739263185447 664626723674005108894778171)
      ·
        refine ⟨996940085511007663342167257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 664626723674005108894778171 996940085511007663342167257)
        ·
          refine ⟨747705064133255747506625443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 996940085511007663342167257 747705064133255747506625443)
          ·
            refine ⟨1121557596199883621259938165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 747705064133255747506625443 1121557596199883621259938165)
            ·
              refine ⟨105146024643739089493119203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1121557596199883621259938165 105146024643739089493119203)
              ·
                refine ⟨157719036965608634239678805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 105146024643739089493119203 157719036965608634239678805)
                ·
                  refine ⟨462067491110181545624059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 157719036965608634239678805 462067491110181545624059)
                  ·
                    rfl

theorem cell23_8098859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 5, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 5, 1, 10].length) (baseStart_8098859 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8098859 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8098859 prefixEnd_8098859 := by exact prefixLift 8098859
  have htrace : WordTrace (prefixWord ++ tailWord_8098859) baseStart_8098859 baseEnd_8098859 := by
    simpa [prefixWord, tailWord_8098859, baseEnd_8098859] using wordTrace_append hprefix tailTrace_8098859
  have hstable : (prefixWord ++ tailWord_8098859).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8098859).length < 2 ^ (prefixWord ++ tailWord_8098859).sum := by decide
  have hdescent : baseEnd_8098859 < baseStart_8098859 := by decide
  rcases family_descends (prefixWord ++ tailWord_8098859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8098870 : List Nat := [5, 1, 2, 1, 1, 3, 1, 2, 2, 1, 4]
def baseStart_8098870 : Nat := 118140960795 + 8098870 * 2 ^ 59
def prefixEnd_8098870 : Nat := 4983230072969 + 3 ^ 40 * 8098870 * 2
def baseEnd_8098870 : Nat := 4158613068278833367578981

theorem tailTrace_8098870 : CollatzResearch.WordTrace tailWord_8098870 prefixEnd_8098870 4158613068278833367578981 := by
  unfold tailWord_8098870
  simp only [CollatzResearch.WordTrace]
  refine ⟨18461878510574040107548379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 196926704112789761147182709 18461878510574040107548379)
  ·
    refine ⟨27692817765861060161322569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18461878510574040107548379 27692817765861060161322569)
    ·
      refine ⟨20769613324395795120991927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27692817765861060161322569 20769613324395795120991927)
      ·
        refine ⟨31154419986593692681487891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20769613324395795120991927 31154419986593692681487891)
        ·
          refine ⟨46731629979890539022231837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31154419986593692681487891 46731629979890539022231837)
          ·
            refine ⟨17524361242458952133336939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46731629979890539022231837 17524361242458952133336939)
            ·
              refine ⟨26286541863688428200005409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17524361242458952133336939 26286541863688428200005409)
              ·
                refine ⟨19714906397766321150004057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26286541863688428200005409 19714906397766321150004057)
                ·
                  refine ⟨14786179798324740862503043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19714906397766321150004057 14786179798324740862503043)
                  ·
                    refine ⟨22179269697487111293754565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14786179798324740862503043 22179269697487111293754565)
                    ·
                      refine ⟨4158613068278833367578981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22179269697487111293754565 4158613068278833367578981)
                      ·
                        rfl

theorem cell23_8098870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 3, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 3, 1, 2, 2, 1, 4].length) (baseStart_8098870 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8098870 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8098870 prefixEnd_8098870 := by exact prefixLift 8098870
  have htrace : WordTrace (prefixWord ++ tailWord_8098870) baseStart_8098870 baseEnd_8098870 := by
    simpa [prefixWord, tailWord_8098870, baseEnd_8098870] using wordTrace_append hprefix tailTrace_8098870
  have hstable : (prefixWord ++ tailWord_8098870).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8098870).length < 2 ^ (prefixWord ++ tailWord_8098870).sum := by decide
  have hdescent : baseEnd_8098870 < baseStart_8098870 := by decide
  rcases family_descends (prefixWord ++ tailWord_8098870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8098873 : List Nat := [1, 2, 1, 5, 2, 1, 1, 1, 4, 2, 3]
def baseStart_8098873 : Nat := 118140960795 + 8098873 * 2 ^ 59
def prefixEnd_8098873 : Nat := 4983230072969 + 3 ^ 40 * 8098873 * 2
def baseEnd_8098873 : Nat := 4158614608720796855841467

theorem tailTrace_8098873 : CollatzResearch.WordTrace tailWord_8098873 prefixEnd_8098873 4158614608720796855841467 := by
  unfold tailWord_8098873
  simp only [CollatzResearch.WordTrace]
  refine ⟨295390165588173773233133273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196926777058782515488755515 295390165588173773233133273)
  ·
    refine ⟨221542624191130329924849955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 295390165588173773233133273 221542624191130329924849955)
    ·
      refine ⟨332313936286695494887274933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 221542624191130329924849955 332313936286695494887274933)
      ·
        refine ⟨31154431526877702645682025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 332313936286695494887274933 31154431526877702645682025)
        ·
          refine ⟨23365823645158276984261519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31154431526877702645682025 23365823645158276984261519)
          ·
            refine ⟨35048735467737415476392279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23365823645158276984261519 35048735467737415476392279)
            ·
              refine ⟨52573103201606123214588419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35048735467737415476392279 52573103201606123214588419)
              ·
                refine ⟨78859654802409184821882629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52573103201606123214588419 78859654802409184821882629)
                ·
                  refine ⟨14786185275451722154102993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 78859654802409184821882629 14786185275451722154102993)
                  ·
                    refine ⟨11089638956588791615577245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14786185275451722154102993 11089638956588791615577245)
                    ·
                      refine ⟨4158614608720796855841467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11089638956588791615577245 4158614608720796855841467)
                      ·
                        rfl

theorem cell23_8098873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 1, 1, 4, 2, 3].length) (baseStart_8098873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8098873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8098873 prefixEnd_8098873 := by exact prefixLift 8098873
  have htrace : WordTrace (prefixWord ++ tailWord_8098873) baseStart_8098873 baseEnd_8098873 := by
    simpa [prefixWord, tailWord_8098873, baseEnd_8098873] using wordTrace_append hprefix tailTrace_8098873
  have hstable : (prefixWord ++ tailWord_8098873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8098873).length < 2 ^ (prefixWord ++ tailWord_8098873).sum := by decide
  have hdescent : baseEnd_8098873 < baseStart_8098873 := by decide
  rcases family_descends (prefixWord ++ tailWord_8098873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8098876 : List Nat := [2, 2, 2, 2, 2, 2, 2, 1, 8]
def baseStart_8098876 : Nat := 118140960795 + 8098876 * 2 ^ 59
def prefixEnd_8098876 : Nat := 4983230072969 + 3 ^ 40 * 8098876 * 2
def baseEnd_8098876 : Nat := 462068461018084482678217

theorem tailTrace_8098876 : CollatzResearch.WordTrace tailWord_8098876 prefixEnd_8098876 462068461018084482678217 := by
  unfold tailWord_8098876
  simp only [CollatzResearch.WordTrace]
  refine ⟨147695137503581452372746241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196926850004775269830328321 147695137503581452372746241)
  ·
    refine ⟨110771353127686089279559681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147695137503581452372746241 110771353127686089279559681)
    ·
      refine ⟨83078514845764566959669761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110771353127686089279559681 83078514845764566959669761)
      ·
        refine ⟨62308886134323425219752321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83078514845764566959669761 62308886134323425219752321)
        ·
          refine ⟨46731664600742568914814241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62308886134323425219752321 46731664600742568914814241)
          ·
            refine ⟨35048748450556926686110681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46731664600742568914814241 35048748450556926686110681)
            ·
              refine ⟨26286561337917695014583011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35048748450556926686110681 26286561337917695014583011)
              ·
                refine ⟨39429842006876542521874517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26286561337917695014583011 39429842006876542521874517)
                ·
                  refine ⟨462068461018084482678217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 39429842006876542521874517 462068461018084482678217)
                  ·
                    rfl

theorem cell23_8098876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 2, 1, 8].length) (baseStart_8098876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8098876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8098876 prefixEnd_8098876 := by exact prefixLift 8098876
  have htrace : WordTrace (prefixWord ++ tailWord_8098876) baseStart_8098876 baseEnd_8098876 := by
    simpa [prefixWord, tailWord_8098876, baseEnd_8098876] using wordTrace_append hprefix tailTrace_8098876
  have hstable : (prefixWord ++ tailWord_8098876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8098876).length < 2 ^ (prefixWord ++ tailWord_8098876).sum := by decide
  have hdescent : baseEnd_8098876 < baseStart_8098876 := by decide
  rcases family_descends (prefixWord ++ tailWord_8098876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8098903 : List Nat := [1, 1, 3, 2, 2, 1, 1, 3, 5, 1, 3]
def baseStart_8098903 : Nat := 118140960795 + 8098903 * 2 ^ 59
def prefixEnd_8098903 : Nat := 4983230072969 + 3 ^ 40 * 8098903 * 2
def baseEnd_8098903 : Nat := 4158630013140431738466329

theorem tailTrace_8098903 : CollatzResearch.WordTrace tailWord_8098903 prefixEnd_8098903 4158630013140431738466329 := by
  unfold tailWord_8098903
  simp only [CollatzResearch.WordTrace]
  refine ⟨295391259778065088356725363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196927506518710058904483575 295391259778065088356725363)
  ·
    refine ⟨443086889667097632535088045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 295391259778065088356725363 443086889667097632535088045)
    ·
      refine ⟨166157583625161612200658017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 443086889667097632535088045 166157583625161612200658017)
      ·
        refine ⟨124618187718871209150493513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 166157583625161612200658017 124618187718871209150493513)
        ·
          refine ⟨93463640789153406862870135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 124618187718871209150493513 93463640789153406862870135)
          ·
            refine ⟨140195461183730110294305203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93463640789153406862870135 140195461183730110294305203)
            ·
              refine ⟨210293191775595165441457805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 140195461183730110294305203 210293191775595165441457805)
              ·
                refine ⟨78859946915848187040546677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 210293191775595165441457805 78859946915848187040546677)
                ·
                  refine ⟨7393120023360767535051251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 78859946915848187040546677 7393120023360767535051251)
                  ·
                    refine ⟨11089680035041151302576877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7393120023360767535051251 11089680035041151302576877)
                    ·
                      refine ⟨4158630013140431738466329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11089680035041151302576877 4158630013140431738466329)
                      ·
                        rfl

theorem cell23_8098903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 3, 5, 1, 3].length) (baseStart_8098903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8098903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8098903 prefixEnd_8098903 := by exact prefixLift 8098903
  have htrace : WordTrace (prefixWord ++ tailWord_8098903) baseStart_8098903 baseEnd_8098903 := by
    simpa [prefixWord, tailWord_8098903, baseEnd_8098903] using wordTrace_append hprefix tailTrace_8098903
  have hstable : (prefixWord ++ tailWord_8098903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8098903).length < 2 ^ (prefixWord ++ tailWord_8098903).sum := by decide
  have hdescent : baseEnd_8098903 < baseStart_8098903 := by decide
  rcases family_descends (prefixWord ++ tailWord_8098903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8098913 : List Nat := [1, 2, 3, 1, 1, 2, 2, 3, 1, 5, 2]
def baseStart_8098913 : Nat := 118140960795 + 8098913 * 2 ^ 59
def prefixEnd_8098913 : Nat := 4983230072969 + 3 ^ 40 * 8098913 * 2
def baseEnd_8098913 : Nat := 4158635147946976699341283

theorem tailTrace_8098913 : CollatzResearch.WordTrace tailWord_8098913 prefixEnd_8098913 4158635147946976699341283 := by
  unfold tailWord_8098913
  simp only [CollatzResearch.WordTrace]
  refine ⟨295391624508028860064589393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196927749672019240043059595 295391624508028860064589393)
  ·
    refine ⟨221543718381021645048442045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 295391624508028860064589393 221543718381021645048442045)
    ·
      refine ⟨83078894392883116893165767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 221543718381021645048442045 83078894392883116893165767)
      ·
        refine ⟨124618341589324675339748651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83078894392883116893165767 124618341589324675339748651)
        ·
          refine ⟨186927512383987013009622977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124618341589324675339748651 186927512383987013009622977)
          ·
            refine ⟨140195634287990259757217233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 186927512383987013009622977 140195634287990259757217233)
            ·
              refine ⟨105146725715992694817912925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 140195634287990259757217233 105146725715992694817912925)
              ·
                refine ⟨39430022143497260556717347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 105146725715992694817912925 39430022143497260556717347)
                ·
                  refine ⟨59145033215245890835076021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39430022143497260556717347 59145033215245890835076021)
                  ·
                    refine ⟨5544846863929302265788377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 59145033215245890835076021 5544846863929302265788377)
                    ·
                      refine ⟨4158635147946976699341283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5544846863929302265788377 4158635147946976699341283)
                      ·
                        rfl

theorem cell23_8098913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 2, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 2, 3, 1, 5, 2].length) (baseStart_8098913 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8098913 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8098913 prefixEnd_8098913 := by exact prefixLift 8098913
  have htrace : WordTrace (prefixWord ++ tailWord_8098913) baseStart_8098913 baseEnd_8098913 := by
    simpa [prefixWord, tailWord_8098913, baseEnd_8098913] using wordTrace_append hprefix tailTrace_8098913
  have hstable : (prefixWord ++ tailWord_8098913).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8098913).length < 2 ^ (prefixWord ++ tailWord_8098913).sum := by decide
  have hdescent : baseEnd_8098913 < baseStart_8098913 := by decide
  rcases family_descends (prefixWord ++ tailWord_8098913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8098930 : List Nat := [3, 2, 1, 2, 2, 1, 1, 4, 2, 3, 2]
def baseStart_8098930 : Nat := 118140960795 + 8098930 * 2 ^ 59
def prefixEnd_8098930 : Nat := 4983230072969 + 3 ^ 40 * 8098930 * 2
def baseEnd_8098930 : Nat := 4158643877118103132828705

theorem tailTrace_8098930 : CollatzResearch.WordTrace tailWord_8098930 prefixEnd_8098930 4158643877118103132828705 := by
  unfold tailWord_8098930
  simp only [CollatzResearch.WordTrace]
  refine ⟨73848061137241817991989561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 196928163032644847978638829 73848061137241817991989561)
  ·
    refine ⟨55386045852931363493992171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73848061137241817991989561 55386045852931363493992171)
    ·
      refine ⟨83079068779397045240988257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55386045852931363493992171 83079068779397045240988257)
      ·
        refine ⟨62309301584547783930741193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83079068779397045240988257 62309301584547783930741193)
        ·
          refine ⟨46731976188410837948055895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62309301584547783930741193 46731976188410837948055895)
          ·
            refine ⟨70097964282616256922083843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46731976188410837948055895 70097964282616256922083843)
            ·
              refine ⟨105146946423924385383125765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70097964282616256922083843 105146946423924385383125765)
              ·
                refine ⟨19715052454485822259336081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 105146946423924385383125765 19715052454485822259336081)
                ·
                  refine ⟨14786289340864366694502061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19715052454485822259336081 14786289340864366694502061)
                  ·
                    refine ⟨5544858502824137510438273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14786289340864366694502061 5544858502824137510438273)
                    ·
                      refine ⟨4158643877118103132828705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5544858502824137510438273 4158643877118103132828705)
                      ·
                        rfl

theorem cell23_8098930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 1, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 1, 4, 2, 3, 2].length) (baseStart_8098930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8098930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8098930 prefixEnd_8098930 := by exact prefixLift 8098930
  have htrace : WordTrace (prefixWord ++ tailWord_8098930) baseStart_8098930 baseEnd_8098930 := by
    simpa [prefixWord, tailWord_8098930, baseEnd_8098930] using wordTrace_append hprefix tailTrace_8098930
  have hstable : (prefixWord ++ tailWord_8098930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8098930).length < 2 ^ (prefixWord ++ tailWord_8098930).sum := by decide
  have hdescent : baseEnd_8098930 < baseStart_8098930 := by decide
  rcases family_descends (prefixWord ++ tailWord_8098930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8098953 : List Nat := [1, 2, 1, 1, 4, 4, 2, 1, 1, 6]
def baseStart_8098953 : Nat := 118140960795 + 8098953 * 2 ^ 59
def prefixEnd_8098953 : Nat := 4983230072969 + 3 ^ 40 * 8098953 * 2
def baseEnd_8098953 : Nat := 1386218562391052180947033

theorem tailTrace_8098953 : CollatzResearch.WordTrace tailWord_8098953 prefixEnd_8098953 1386218562391052180947033 := by
  unfold tailWord_8098953
  simp only [CollatzResearch.WordTrace]
  refine ⟨295393083427883946896045513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196928722285255964597363675 295393083427883946896045513)
  ·
    refine ⟨221544812570912960172034135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 295393083427883946896045513 221544812570912960172034135)
    ·
      refine ⟨332317218856369440258051203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 221544812570912960172034135 332317218856369440258051203)
      ·
        refine ⟨498475828284554160387076805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 332317218856369440258051203 498475828284554160387076805)
        ·
          refine ⟨93464217803353905072576901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 498475828284554160387076805 93464217803353905072576901)
          ·
            refine ⟨17524540838128857201108169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 93464217803353905072576901 17524540838128857201108169)
            ·
              refine ⟨13143405628596642900831127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17524540838128857201108169 13143405628596642900831127)
              ·
                refine ⟨19715108442894964351246691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13143405628596642900831127 19715108442894964351246691)
                ·
                  refine ⟨29572662664342446526870037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19715108442894964351246691 29572662664342446526870037)
                  ·
                    refine ⟨1386218562391052180947033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29572662664342446526870037 1386218562391052180947033)
                    ·
                      rfl

theorem cell23_8098953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 4, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 4, 2, 1, 1, 6].length) (baseStart_8098953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8098953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8098953 prefixEnd_8098953 := by exact prefixLift 8098953
  have htrace : WordTrace (prefixWord ++ tailWord_8098953) baseStart_8098953 baseEnd_8098953 := by
    simpa [prefixWord, tailWord_8098953, baseEnd_8098953] using wordTrace_append hprefix tailTrace_8098953
  have hstable : (prefixWord ++ tailWord_8098953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8098953).length < 2 ^ (prefixWord ++ tailWord_8098953).sum := by decide
  have hdescent : baseEnd_8098953 < baseStart_8098953 := by decide
  rcases family_descends (prefixWord ++ tailWord_8098953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8098956 : List Nat := [2, 2, 1, 2, 1, 1, 1, 5, 1, 1, 6]
def baseStart_8098956 : Nat := 118140960795 + 8098956 * 2 ^ 59
def prefixEnd_8098956 : Nat := 4983230072969 + 3 ^ 40 * 8098956 * 2
def baseEnd_8098956 : Nat := 4158657227615120031103585

theorem tailTrace_8098956 : CollatzResearch.WordTrace tailWord_8098956 prefixEnd_8098956 4158657227615120031103585 := by
  unfold tailWord_8098956
  simp only [CollatzResearch.WordTrace]
  refine ⟨147696596423436539204202361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196928795231248718938936481 147696596423436539204202361)
  ·
    refine ⟨110772447317577404403151771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147696596423436539204202361 110772447317577404403151771)
    ·
      refine ⟨166158670976366106604727657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110772447317577404403151771 166158670976366106604727657)
      ·
        refine ⟨124619003232274579953545743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 166158670976366106604727657 124619003232274579953545743)
        ·
          refine ⟨186928504848411869930318615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124619003232274579953545743 186928504848411869930318615)
          ·
            refine ⟨280392757272617804895477923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 186928504848411869930318615 280392757272617804895477923)
            ·
              refine ⟨420589135908926707343216885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 280392757272617804895477923 420589135908926707343216885)
              ·
                refine ⟨39430231491461878813426583, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 420589135908926707343216885 39430231491461878813426583)
                ·
                  refine ⟨59145347237192818220139875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39430231491461878813426583 59145347237192818220139875)
                  ·
                    refine ⟨88718020855789227330209813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 59145347237192818220139875 88718020855789227330209813)
                    ·
                      refine ⟨4158657227615120031103585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 88718020855789227330209813 4158657227615120031103585)
                      ·
                        rfl

theorem cell23_8098956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 5, 1, 1, 6].length) (baseStart_8098956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8098956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8098956 prefixEnd_8098956 := by exact prefixLift 8098956
  have htrace : WordTrace (prefixWord ++ tailWord_8098956) baseStart_8098956 baseEnd_8098956 := by
    simpa [prefixWord, tailWord_8098956, baseEnd_8098956] using wordTrace_append hprefix tailTrace_8098956
  have hstable : (prefixWord ++ tailWord_8098956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8098956).length < 2 ^ (prefixWord ++ tailWord_8098956).sum := by decide
  have hdescent : baseEnd_8098956 < baseStart_8098956 := by decide
  rcases family_descends (prefixWord ++ tailWord_8098956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8098963 : List Nat := [1, 1, 1, 2, 1, 2, 6, 1, 3, 2, 3]
def baseStart_8098963 : Nat := 118140960795 + 8098963 * 2 ^ 59
def prefixEnd_8098963 : Nat := 4983230072969 + 3 ^ 40 * 8098963 * 2
def baseEnd_8098963 : Nat := 4158660821979701503716053

theorem tailTrace_8098963 : CollatzResearch.WordTrace tailWord_8098963 prefixEnd_8098963 4158660821979701503716053 := by
  unfold tailWord_8098963
  simp only [CollatzResearch.WordTrace]
  refine ⟨295393448157847718603909543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196928965438565145735939695 295393448157847718603909543)
  ·
    refine ⟨443090172236771577905864315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 295393448157847718603909543 443090172236771577905864315)
    ·
      refine ⟨664635258355157366858796473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 443090172236771577905864315 664635258355157366858796473)
      ·
        refine ⟨498476443766368025144097355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 664635258355157366858796473 498476443766368025144097355)
        ·
          refine ⟨747714665649552037716146033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 498476443766368025144097355 747714665649552037716146033)
          ·
            refine ⟨560785999237164028287109525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 747714665649552037716146033 560785999237164028287109525)
            ·
              refine ⟨26286843714242063825958259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 560785999237164028287109525 26286843714242063825958259)
              ·
                refine ⟨39430265571363095738937389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26286843714242063825958259 39430265571363095738937389)
                ·
                  refine ⟨14786349589261160902101521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39430265571363095738937389 14786349589261160902101521)
                  ·
                    refine ⟨11089762191945870676576141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14786349589261160902101521 11089762191945870676576141)
                    ·
                      refine ⟨4158660821979701503716053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11089762191945870676576141 4158660821979701503716053)
                      ·
                        rfl

theorem cell23_8098963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 6, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 6, 1, 3, 2, 3].length) (baseStart_8098963 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8098963 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8098963 prefixEnd_8098963 := by exact prefixLift 8098963
  have htrace : WordTrace (prefixWord ++ tailWord_8098963) baseStart_8098963 baseEnd_8098963 := by
    simpa [prefixWord, tailWord_8098963, baseEnd_8098963] using wordTrace_append hprefix tailTrace_8098963
  have hstable : (prefixWord ++ tailWord_8098963).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8098963).length < 2 ^ (prefixWord ++ tailWord_8098963).sum := by decide
  have hdescent : baseEnd_8098963 < baseStart_8098963 := by decide
  rcases family_descends (prefixWord ++ tailWord_8098963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8098973 : List Nat := [1, 4, 2, 1, 1, 2, 1, 4, 1, 2, 4]
def baseStart_8098973 : Nat := 118140960795 + 8098973 * 2 ^ 59
def prefixEnd_8098973 : Nat := 4983230072969 + 3 ^ 40 * 8098973 * 2
def baseEnd_8098973 : Nat := 4158665956786246464591007

theorem tailTrace_8098973 : CollatzResearch.WordTrace tailWord_8098973 prefixEnd_8098973 4158665956786246464591007 := by
  unfold tailWord_8098973
  simp only [CollatzResearch.WordTrace]
  refine ⟨295393812887811490311773573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196929208591874326874515715 295393812887811490311773573)
  ·
    refine ⟨55386339916464654433457545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 295393812887811490311773573 55386339916464654433457545)
    ·
      refine ⟨41539754937348490825093159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55386339916464654433457545 41539754937348490825093159)
      ·
        refine ⟨62309632406022736237639739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41539754937348490825093159 62309632406022736237639739)
        ·
          refine ⟨93464448609034104356459609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62309632406022736237639739 93464448609034104356459609)
          ·
            refine ⟨70098336456775578267344707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 93464448609034104356459609 70098336456775578267344707)
            ·
              refine ⟨105147504685163367401017061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70098336456775578267344707 105147504685163367401017061)
              ·
                refine ⟨19715157128468131387690699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 105147504685163367401017061 19715157128468131387690699)
                ·
                  refine ⟨29572735692702197081536049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19715157128468131387690699 29572735692702197081536049)
                  ·
                    refine ⟨22179551769526647811152037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29572735692702197081536049 22179551769526647811152037)
                    ·
                      refine ⟨4158665956786246464591007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22179551769526647811152037 4158665956786246464591007)
                      ·
                        rfl

theorem cell23_8098973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 1, 4, 1, 2, 4].length) (baseStart_8098973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8098973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8098973 prefixEnd_8098973 := by exact prefixLift 8098973
  have htrace : WordTrace (prefixWord ++ tailWord_8098973) baseStart_8098973 baseEnd_8098973 := by
    simpa [prefixWord, tailWord_8098973, baseEnd_8098973] using wordTrace_append hprefix tailTrace_8098973
  have hstable : (prefixWord ++ tailWord_8098973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8098973).length < 2 ^ (prefixWord ++ tailWord_8098973).sum := by decide
  have hdescent : baseEnd_8098973 < baseStart_8098973 := by decide
  rcases family_descends (prefixWord ++ tailWord_8098973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8098974 : List Nat := [4, 3, 1, 1, 2, 3, 2, 1, 1, 5]
def baseStart_8098974 : Nat := 118140960795 + 8098974 * 2 ^ 59
def prefixEnd_8098974 : Nat := 4983230072969 + 3 ^ 40 * 8098974 * 2
def baseEnd_8098974 : Nat := 1386222156755633653559501

theorem tailTrace_8098974 : CollatzResearch.WordTrace tailWord_8098974 prefixEnd_8098974 1386222156755633653559501 := by
  unfold tailWord_8098974
  simp only [CollatzResearch.WordTrace]
  refine ⟨36924231170100983435319997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 196929232907205244988373317 36924231170100983435319997)
  ·
    refine ⟨13846586688787868788244999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36924231170100983435319997 13846586688787868788244999)
    ·
      refine ⟨20769880033181803182367499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13846586688787868788244999 20769880033181803182367499)
      ·
        refine ⟨31154820049772704773551249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20769880033181803182367499 31154820049772704773551249)
        ·
          refine ⟨23366115037329528580163437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31154820049772704773551249 23366115037329528580163437)
          ·
            refine ⟨8762293138998573217561289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23366115037329528580163437 8762293138998573217561289)
            ·
              refine ⟨6571719854248929913170967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8762293138998573217561289 6571719854248929913170967)
              ·
                refine ⟨9857579781373394869756451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6571719854248929913170967 9857579781373394869756451)
                ·
                  refine ⟨14786369672060092304634677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9857579781373394869756451 14786369672060092304634677)
                  ·
                    refine ⟨1386222156755633653559501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14786369672060092304634677 1386222156755633653559501)
                    ·
                      rfl

theorem cell23_8098974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 3, 2, 1, 1, 5].length) (baseStart_8098974 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8098974 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8098974 prefixEnd_8098974 := by exact prefixLift 8098974
  have htrace : WordTrace (prefixWord ++ tailWord_8098974) baseStart_8098974 baseEnd_8098974 := by
    simpa [prefixWord, tailWord_8098974, baseEnd_8098974] using wordTrace_append hprefix tailTrace_8098974
  have hstable : (prefixWord ++ tailWord_8098974).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8098974).length < 2 ^ (prefixWord ++ tailWord_8098974).sum := by decide
  have hdescent : baseEnd_8098974 < baseStart_8098974 := by decide
  rcases family_descends (prefixWord ++ tailWord_8098974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8098983 : List Nat := [1, 1, 6, 2, 1, 2, 10]
def baseStart_8098983 : Nat := 118140960795 + 8098983 * 2 ^ 59
def prefixEnd_8098983 : Nat := 4983230072969 + 3 ^ 40 * 8098983 * 2
def baseEnd_8098983 : Nat := 51341618414725820067481

theorem tailTrace_8098983 : CollatzResearch.WordTrace tailWord_8098983 prefixEnd_8098983 51341618414725820067481 := by
  unfold tailWord_8098983
  simp only [CollatzResearch.WordTrace]
  refine ⟨295394177617775262019637603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196929451745183508013091735 295394177617775262019637603)
  ·
    refine ⟨443091266426662893029456405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 295394177617775262019637603 443091266426662893029456405)
    ·
      refine ⟨20769903113749823110755769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 443091266426662893029456405 20769903113749823110755769)
      ·
        refine ⟨15577427335312367333066827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20769903113749823110755769 15577427335312367333066827)
        ·
          refine ⟨23366141002968550999600241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15577427335312367333066827 23366141002968550999600241)
          ·
            refine ⟨17524605752226413249700181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23366141002968550999600241 17524605752226413249700181)
            ·
              refine ⟨51341618414725820067481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 17524605752226413249700181 51341618414725820067481)
              ·
                rfl

theorem cell23_8098983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 2, 10].length) (baseStart_8098983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8098983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8098983 prefixEnd_8098983 := by exact prefixLift 8098983
  have htrace : WordTrace (prefixWord ++ tailWord_8098983) baseStart_8098983 baseEnd_8098983 := by
    simpa [prefixWord, tailWord_8098983, baseEnd_8098983] using wordTrace_append hprefix tailTrace_8098983
  have hstable : (prefixWord ++ tailWord_8098983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8098983).length < 2 ^ (prefixWord ++ tailWord_8098983).sum := by decide
  have hdescent : baseEnd_8098983 < baseStart_8098983 := by decide
  rcases family_descends (prefixWord ++ tailWord_8098983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8098994 : List Nat := [3, 2, 1, 1, 1, 4, 2, 4, 1, 2, 2]
def baseStart_8098994 : Nat := 118140960795 + 8098994 * 2 ^ 59
def prefixEnd_8098994 : Nat := 4983230072969 + 3 ^ 40 * 8098994 * 2
def baseEnd_8098994 : Nat := 4158676739879990882428411

theorem tailTrace_8098994 : CollatzResearch.WordTrace tailWord_8098994 prefixEnd_8098994 4158676739879990882428411 := by
  unfold tailWord_8098994
  simp only [CollatzResearch.WordTrace]
  refine ⟨73848644705183852724572009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 196929719213823607265525357 73848644705183852724572009)
  ·
    refine ⟨55386483528887889543429007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73848644705183852724572009 55386483528887889543429007)
    ·
      refine ⟨83079725293331834315143511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55386483528887889543429007 83079725293331834315143511)
      ·
        refine ⟨124619587939997751472715267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83079725293331834315143511 124619587939997751472715267)
        ·
          refine ⟨186929381909996627209072901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124619587939997751472715267 186929381909996627209072901)
          ·
            refine ⟨35049259108124367601701169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 186929381909996627209072901 35049259108124367601701169)
            ·
              refine ⟨26286944331093275701275877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35049259108124367601701169 26286944331093275701275877)
              ·
                refine ⟨4928802062079989193989227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26286944331093275701275877 4928802062079989193989227)
                ·
                  refine ⟨7393203093119983790983841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4928802062079989193989227 7393203093119983790983841)
                  ·
                    refine ⟨5544902319839987843237881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7393203093119983790983841 5544902319839987843237881)
                    ·
                      refine ⟨4158676739879990882428411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5544902319839987843237881 4158676739879990882428411)
                      ·
                        rfl

theorem cell23_8098994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 2, 4, 1, 2, 2].length) (baseStart_8098994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8098994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8098994 prefixEnd_8098994 := by exact prefixLift 8098994
  have htrace : WordTrace (prefixWord ++ tailWord_8098994) baseStart_8098994 baseEnd_8098994 := by
    simpa [prefixWord, tailWord_8098994, baseEnd_8098994] using wordTrace_append hprefix tailTrace_8098994
  have hstable : (prefixWord ++ tailWord_8098994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8098994).length < 2 ^ (prefixWord ++ tailWord_8098994).sum := by decide
  have hdescent : baseEnd_8098994 < baseStart_8098994 := by decide
  rcases family_descends (prefixWord ++ tailWord_8098994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8099003 : List Nat := [1, 1, 1, 1, 1, 2, 4, 1, 2, 7, 2]
def baseStart_8099003 : Nat := 118140960795 + 8099003 * 2 ^ 59
def prefixEnd_8099003 : Nat := 4983230072969 + 3 ^ 40 * 8099003 * 2
def baseEnd_8099003 : Nat := 4158681361205881347215869

theorem tailTrace_8099003 : CollatzResearch.WordTrace tailWord_8099003 prefixEnd_8099003 4158681361205881347215869 := by
  unfold tailWord_8099003
  simp only [CollatzResearch.WordTrace]
  refine ⟨295394907077702805435365663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196929938051801870290243775 295394907077702805435365663)
  ·
    refine ⟨443092360616554208153048495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 295394907077702805435365663 443092360616554208153048495)
    ·
      refine ⟨664638540924831312229572743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 443092360616554208153048495 664638540924831312229572743)
      ·
        refine ⟨996957811387246968344359115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 664638540924831312229572743 996957811387246968344359115)
        ·
          refine ⟨1495436717080870452516538673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 996957811387246968344359115 1495436717080870452516538673)
          ·
            refine ⟨1121577537810652839387404005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1495436717080870452516538673 1121577537810652839387404005)
            ·
              refine ⟨210295788339497407385138251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1121577537810652839387404005 210295788339497407385138251)
              ·
                refine ⟨315443682509246111077707377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 210295788339497407385138251 315443682509246111077707377)
                ·
                  refine ⟨236582761881934583308280533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 315443682509246111077707377 236582761881934583308280533)
                  ·
                    refine ⟨5544908481607841796287825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 236582761881934583308280533 5544908481607841796287825)
                    ·
                      refine ⟨4158681361205881347215869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5544908481607841796287825 4158681361205881347215869)
                      ·
                        rfl

theorem cell23_8099003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 1, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 1, 2, 7, 2].length) (baseStart_8099003 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8099003 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8099003 prefixEnd_8099003 := by exact prefixLift 8099003
  have htrace : WordTrace (prefixWord ++ tailWord_8099003) baseStart_8099003 baseEnd_8099003 := by
    simpa [prefixWord, tailWord_8099003, baseEnd_8099003] using wordTrace_append hprefix tailTrace_8099003
  have hstable : (prefixWord ++ tailWord_8099003).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8099003).length < 2 ^ (prefixWord ++ tailWord_8099003).sum := by decide
  have hdescent : baseEnd_8099003 < baseStart_8099003 := by decide
  rcases family_descends (prefixWord ++ tailWord_8099003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8099070 : List Nat := [4, 2, 2, 1, 1, 2, 1, 2, 2, 1, 5]
def baseStart_8099070 : Nat := 118140960795 + 8099070 * 2 ^ 59
def prefixEnd_8099070 : Nat := 4983230072969 + 3 ^ 40 * 8099070 * 2
def baseEnd_8099070 : Nat := 4158715764409732585078061

theorem tailTrace_8099070 : CollatzResearch.WordTrace tailWord_8099070 prefixEnd_8099070 4158715764409732585078061 := by
  unfold tailWord_8099070
  simp only [CollatzResearch.WordTrace]
  refine ⟨36924668846057509484756833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 196931567178973383918703109 36924668846057509484756833)
  ·
    refine ⟨27693501634543132113567625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36924668846057509484756833 27693501634543132113567625)
    ·
      refine ⟨20770126225907349085175719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27693501634543132113567625 20770126225907349085175719)
      ·
        refine ⟨31155189338861023627763579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20770126225907349085175719 31155189338861023627763579)
        ·
          refine ⟨46732784008291535441645369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31155189338861023627763579 46732784008291535441645369)
          ·
            refine ⟨35049588006218651581234027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46732784008291535441645369 35049588006218651581234027)
            ·
              refine ⟨52574382009327977371851041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35049588006218651581234027 52574382009327977371851041)
              ·
                refine ⟨39430786506995983028888281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52574382009327977371851041 39430786506995983028888281)
                ·
                  refine ⟨29573089880246987271666211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39430786506995983028888281 29573089880246987271666211)
                  ·
                    refine ⟨44359634820370480907499317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29573089880246987271666211 44359634820370480907499317)
                    ·
                      refine ⟨4158715764409732585078061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44359634820370480907499317 4158715764409732585078061)
                      ·
                        rfl

theorem cell23_8099070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 1, 2, 2, 1, 5].length) (baseStart_8099070 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8099070 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8099070 prefixEnd_8099070 := by exact prefixLift 8099070
  have htrace : WordTrace (prefixWord ++ tailWord_8099070) baseStart_8099070 baseEnd_8099070 := by
    simpa [prefixWord, tailWord_8099070, baseEnd_8099070] using wordTrace_append hprefix tailTrace_8099070
  have hstable : (prefixWord ++ tailWord_8099070).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8099070).length < 2 ^ (prefixWord ++ tailWord_8099070).sum := by decide
  have hdescent : baseEnd_8099070 < baseStart_8099070 := by decide
  rcases family_descends (prefixWord ++ tailWord_8099070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8099101 : List Nat := [1, 4, 2, 3, 1, 2, 2, 2, 2, 2, 2]
def baseStart_8099101 : Nat := 118140960795 + 8099101 * 2 ^ 59
def prefixEnd_8099101 : Nat := 4983230072969 + 3 ^ 40 * 8099101 * 2
def baseEnd_8099101 : Nat := 4158731682310021963790419

theorem tailTrace_8099101 : CollatzResearch.WordTrace tailWord_8099101 prefixEnd_8099101 4158731682310021963790419 := by
  unfold tailWord_8099101
  simp only [CollatzResearch.WordTrace]
  refine ⟨295398481431347768172433157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196932320954231845448288771 295398481431347768172433157)
  ·
    refine ⟨55387215268377706532331217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 295398481431347768172433157 55387215268377706532331217)
    ·
      refine ⟨41540411451283279899248413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55387215268377706532331217 41540411451283279899248413)
      ·
        refine ⟨15577654294231229962218155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41540411451283279899248413 15577654294231229962218155)
        ·
          refine ⟨23366481441346844943327233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15577654294231229962218155 23366481441346844943327233)
          ·
            refine ⟨17524861081010133707495425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23366481441346844943327233 17524861081010133707495425)
            ·
              refine ⟨13143645810757600280621569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17524861081010133707495425 13143645810757600280621569)
              ·
                refine ⟨9857734358068200210466177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13143645810757600280621569 9857734358068200210466177)
                ·
                  refine ⟨7393300768551150157849633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9857734358068200210466177 7393300768551150157849633)
                  ·
                    refine ⟨5544975576413362618387225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7393300768551150157849633 5544975576413362618387225)
                    ·
                      refine ⟨4158731682310021963790419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5544975576413362618387225 4158731682310021963790419)
                      ·
                        rfl

theorem cell23_8099101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 2, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 2, 2, 2, 2, 2, 2].length) (baseStart_8099101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8099101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8099101 prefixEnd_8099101 := by exact prefixLift 8099101
  have htrace : WordTrace (prefixWord ++ tailWord_8099101) baseStart_8099101 baseEnd_8099101 := by
    simpa [prefixWord, tailWord_8099101, baseEnd_8099101] using wordTrace_append hprefix tailTrace_8099101
  have hstable : (prefixWord ++ tailWord_8099101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8099101).length < 2 ^ (prefixWord ++ tailWord_8099101).sum := by decide
  have hdescent : baseEnd_8099101 < baseStart_8099101 := by decide
  rcases family_descends (prefixWord ++ tailWord_8099101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8099107 : List Nat := [1, 1, 1, 4, 2, 3, 4, 2, 5]
def baseStart_8099107 : Nat := 118140960795 + 8099107 * 2 ^ 59
def prefixEnd_8099107 : Nat := 4983230072969 + 3 ^ 40 * 8099107 * 2
def baseEnd_8099107 : Nat := 462081640354883215590599

theorem tailTrace_8099107 : CollatzResearch.WordTrace tailWord_8099107 prefixEnd_8099107 462081640354883215590599 := by
  unfold tailWord_8099107
  simp only [CollatzResearch.WordTrace]
  refine ⟨295398700269326031197151575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196932466846217354131434383 295398700269326031197151575)
  ·
    refine ⟨443098050403989046795727363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 295398700269326031197151575 443098050403989046795727363)
    ·
      refine ⟨664647075605983570193591045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 443098050403989046795727363 664647075605983570193591045)
      ·
        refine ⟨124621326676121919411298321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 664647075605983570193591045 124621326676121919411298321)
        ·
          refine ⟨93465995007091439558473741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 124621326676121919411298321 93465995007091439558473741)
          ·
            refine ⟨35049748127659289834427653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 93465995007091439558473741 35049748127659289834427653)
            ·
              refine ⟨6571827773936116843955185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35049748127659289834427653 6571827773936116843955185)
              ·
                refine ⟨4928870830452087632966389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6571827773936116843955185 4928870830452087632966389)
                ·
                  refine ⟨462081640354883215590599, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4928870830452087632966389 462081640354883215590599)
                  ·
                    rfl

theorem cell23_8099107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 4, 2, 5].length) (baseStart_8099107 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8099107 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8099107 prefixEnd_8099107 := by exact prefixLift 8099107
  have htrace : WordTrace (prefixWord ++ tailWord_8099107) baseStart_8099107 baseEnd_8099107 := by
    simpa [prefixWord, tailWord_8099107, baseEnd_8099107] using wordTrace_append hprefix tailTrace_8099107
  have hstable : (prefixWord ++ tailWord_8099107).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8099107).length < 2 ^ (prefixWord ++ tailWord_8099107).sum := by decide
  have hdescent : baseEnd_8099107 < baseStart_8099107 := by decide
  rcases family_descends (prefixWord ++ tailWord_8099107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8099117 : List Nat := [1, 5, 3, 1, 1, 1, 1, 1, 1, 5, 3]
def baseStart_8099117 : Nat := 118140960795 + 8099117 * 2 ^ 59
def prefixEnd_8099117 : Nat := 4983230072969 + 3 ^ 40 * 8099117 * 2
def baseEnd_8099117 : Nat := 4158739898000493901190345

theorem tailTrace_8099117 : CollatzResearch.WordTrace tailWord_8099117 prefixEnd_8099117 4158739898000493901190345 := by
  unfold tailWord_8099117
  simp only [CollatzResearch.WordTrace]
  refine ⟨295399064999289802905015605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196932709999526535270010403 295399064999289802905015605)
  ·
    refine ⟨27693662343683419022345213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 295399064999289802905015605 27693662343683419022345213)
    ·
      refine ⟨10385123378881282133379455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27693662343683419022345213 10385123378881282133379455)
      ·
        refine ⟨15577685068321923200069183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10385123378881282133379455 15577685068321923200069183)
        ·
          refine ⟨23366527602482884800103775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15577685068321923200069183 23366527602482884800103775)
          ·
            refine ⟨35049791403724327200155663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23366527602482884800103775 35049791403724327200155663)
            ·
              refine ⟨52574687105586490800233495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35049791403724327200155663 52574687105586490800233495)
              ·
                refine ⟨78862030658379736200350243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52574687105586490800233495 78862030658379736200350243)
                ·
                  refine ⟨118293045987569604300525365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 78862030658379736200350243 118293045987569604300525365)
                  ·
                    refine ⟨11089973061334650403174253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 118293045987569604300525365 11089973061334650403174253)
                    ·
                      refine ⟨4158739898000493901190345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11089973061334650403174253 4158739898000493901190345)
                      ·
                        rfl

theorem cell23_8099117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 1, 1, 1, 5, 3].length) (baseStart_8099117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8099117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8099117 prefixEnd_8099117 := by exact prefixLift 8099117
  have htrace : WordTrace (prefixWord ++ tailWord_8099117) baseStart_8099117 baseEnd_8099117 := by
    simpa [prefixWord, tailWord_8099117, baseEnd_8099117] using wordTrace_append hprefix tailTrace_8099117
  have hstable : (prefixWord ++ tailWord_8099117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8099117).length < 2 ^ (prefixWord ++ tailWord_8099117).sum := by decide
  have hdescent : baseEnd_8099117 < baseStart_8099117 := by decide
  rcases family_descends (prefixWord ++ tailWord_8099117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8099137 : List Nat := [1, 2, 5, 2, 1, 1, 3, 1, 2, 5]
def baseStart_8099137 : Nat := 118140960795 + 8099137 * 2 ^ 59
def prefixEnd_8099137 : Nat := 4983230072969 + 3 ^ 40 * 8099137 * 2
def baseEnd_8099137 : Nat := 1386250055871194607646751

theorem tailTrace_8099137 : CollatzResearch.WordTrace tailWord_8099137 prefixEnd_8099137 1386250055871194607646751 := by
  unfold tailWord_8099137
  simp only [CollatzResearch.WordTrace]
  refine ⟨295399794459217346320743665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196933196306144897547162443 295399794459217346320743665)
  ·
    refine ⟨221549845844413009740557749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 295399794459217346320743665 221549845844413009740557749)
    ·
      refine ⟨20770298047913719663177289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 221549845844413009740557749 20770298047913719663177289)
      ·
        refine ⟨15577723535935289747382967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20770298047913719663177289 15577723535935289747382967)
        ·
          refine ⟨23366585303902934621074451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15577723535935289747382967 23366585303902934621074451)
          ·
            refine ⟨35049877955854401931611677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23366585303902934621074451 35049877955854401931611677)
            ·
              refine ⟨13143704233445400724354379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35049877955854401931611677 13143704233445400724354379)
              ·
                refine ⟨19715556350168101086531569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13143704233445400724354379 19715556350168101086531569)
                ·
                  refine ⟨14786667262626075814898677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19715556350168101086531569 14786667262626075814898677)
                  ·
                    refine ⟨1386250055871194607646751, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14786667262626075814898677 1386250055871194607646751)
                    ·
                      rfl

theorem cell23_8099137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 3, 1, 2, 5].length) (baseStart_8099137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8099137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8099137 prefixEnd_8099137 := by exact prefixLift 8099137
  have htrace : WordTrace (prefixWord ++ tailWord_8099137) baseStart_8099137 baseEnd_8099137 := by
    simpa [prefixWord, tailWord_8099137, baseEnd_8099137] using wordTrace_append hprefix tailTrace_8099137
  have hstable : (prefixWord ++ tailWord_8099137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8099137).length < 2 ^ (prefixWord ++ tailWord_8099137).sum := by decide
  have hdescent : baseEnd_8099137 < baseStart_8099137 := by decide
  rcases family_descends (prefixWord ++ tailWord_8099137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8099150 : List Nat := [4, 1, 1, 1, 1, 1, 3, 2, 5, 4]
def baseStart_8099150 : Nat := 118140960795 + 8099150 * 2 ^ 59
def prefixEnd_8099150 : Nat := 4983230072969 + 3 ^ 40 * 8099150 * 2
def baseEnd_8099150 : Nat := 1386252280954030757359231

theorem tailTrace_8099150 : CollatzResearch.WordTrace tailWord_8099150 prefixEnd_8099150 1386252280954030757359231 := by
  unfold tailWord_8099150
  simp only [CollatzResearch.WordTrace]
  refine ⟨36925033576021281192620863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 196933512405446833027311269 36925033576021281192620863)
  ·
    refine ⟨55387550364031921788931295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36925033576021281192620863 55387550364031921788931295)
    ·
      refine ⟨83081325546047882683396943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55387550364031921788931295 83081325546047882683396943)
      ·
        refine ⟨124621988319071824025095415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83081325546047882683396943 124621988319071824025095415)
        ·
          refine ⟨186932982478607736037643123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124621988319071824025095415 186932982478607736037643123)
          ·
            refine ⟨280399473717911604056464685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 186932982478607736037643123 280399473717911604056464685)
            ·
              refine ⟨105149802644216851521174257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 280399473717911604056464685 105149802644216851521174257)
              ·
                refine ⟨78862351983162638640880693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 105149802644216851521174257 78862351983162638640880693)
                ·
                  refine ⟨7393345498421497372582565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 78862351983162638640880693 7393345498421497372582565)
                  ·
                    refine ⟨1386252280954030757359231, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7393345498421497372582565 1386252280954030757359231)
                    ·
                      rfl

theorem cell23_8099150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 3, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 3, 2, 5, 4].length) (baseStart_8099150 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8099150 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8099150 prefixEnd_8099150 := by exact prefixLift 8099150
  have htrace : WordTrace (prefixWord ++ tailWord_8099150) baseStart_8099150 baseEnd_8099150 := by
    simpa [prefixWord, tailWord_8099150, baseEnd_8099150] using wordTrace_append hprefix tailTrace_8099150
  have hstable : (prefixWord ++ tailWord_8099150).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8099150).length < 2 ^ (prefixWord ++ tailWord_8099150).sum := by decide
  have hdescent : baseEnd_8099150 < baseStart_8099150 := by decide
  rcases family_descends (prefixWord ++ tailWord_8099150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8099153 : List Nat := [1, 2, 2, 1, 4, 1, 1, 1, 1, 3, 6]
def baseStart_8099153 : Nat := 118140960795 + 8099153 * 2 ^ 59
def prefixEnd_8099153 : Nat := 4983230072969 + 3 ^ 40 * 8099153 * 2
def baseEnd_8099153 : Nat := 4158758383304055760340179

theorem tailTrace_8099153 : CollatzResearch.WordTrace tailWord_8099153 prefixEnd_8099153 4158758383304055760340179 := by
  unfold tailWord_8099153
  simp only [CollatzResearch.WordTrace]
  refine ⟨295400378027159381053326113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196933585351439587368884075 295400378027159381053326113)
  ·
    refine ⟨221550283520369535789994585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 295400378027159381053326113 221550283520369535789994585)
    ·
      refine ⟨166162712640277151842495939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 221550283520369535789994585 166162712640277151842495939)
      ·
        refine ⟨249244068960415727763743909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166162712640277151842495939 249244068960415727763743909)
        ·
          refine ⟨46733262930077948955701983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 249244068960415727763743909 46733262930077948955701983)
          ·
            refine ⟨70099894395116923433552975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46733262930077948955701983 70099894395116923433552975)
            ·
              refine ⟨105149841592675385150329463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70099894395116923433552975 105149841592675385150329463)
              ·
                refine ⟨157724762389013077725494195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 105149841592675385150329463 157724762389013077725494195)
                ·
                  refine ⟨236587143583519616588241293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 157724762389013077725494195 236587143583519616588241293)
                  ·
                    refine ⟨88720178843819856220590485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 236587143583519616588241293 88720178843819856220590485)
                    ·
                      refine ⟨4158758383304055760340179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 88720178843819856220590485 4158758383304055760340179)
                      ·
                        rfl

theorem cell23_8099153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 1, 1, 1, 3, 6].length) (baseStart_8099153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8099153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8099153 prefixEnd_8099153 := by exact prefixLift 8099153
  have htrace : WordTrace (prefixWord ++ tailWord_8099153) baseStart_8099153 baseEnd_8099153 := by
    simpa [prefixWord, tailWord_8099153, baseEnd_8099153] using wordTrace_append hprefix tailTrace_8099153
  have hstable : (prefixWord ++ tailWord_8099153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8099153).length < 2 ^ (prefixWord ++ tailWord_8099153).sum := by decide
  have hdescent : baseEnd_8099153 < baseStart_8099153 := by decide
  rcases family_descends (prefixWord ++ tailWord_8099153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8099157 : List Nat := [1, 3, 2, 2, 3, 1, 1, 2, 2, 4, 2]
def baseStart_8099157 : Nat := 118140960795 + 8099157 * 2 ^ 59
def prefixEnd_8099157 : Nat := 4983230072969 + 3 ^ 40 * 8099157 * 2
def baseEnd_8099157 : Nat := 4158760437226673744690161

theorem tailTrace_8099157 : CollatzResearch.WordTrace tailWord_8099157 prefixEnd_8099157 4158760437226673744690161 := by
  unfold tailWord_8099157
  simp only [CollatzResearch.WordTrace]
  refine ⟨295400523919144889736471725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196933682612763259824314483 295400523919144889736471725)
  ·
    refine ⟨110775196469679333651176897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 295400523919144889736471725 110775196469679333651176897)
    ·
      refine ⟨83081397352259500238382673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110775196469679333651176897 83081397352259500238382673)
      ·
        refine ⟨62311048014194625178787005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83081397352259500238382673 62311048014194625178787005)
        ·
          refine ⟨23366643005322984442045127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62311048014194625178787005 23366643005322984442045127)
          ·
            refine ⟨35049964507984476663067691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23366643005322984442045127 35049964507984476663067691)
            ·
              refine ⟨52574946761976714994601537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35049964507984476663067691 52574946761976714994601537)
              ·
                refine ⟨39431210071482536245951153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52574946761976714994601537 39431210071482536245951153)
                ·
                  refine ⟨29573407553611902184463365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39431210071482536245951153 29573407553611902184463365)
                  ·
                    refine ⟨5545013916302231659586881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29573407553611902184463365 5545013916302231659586881)
                    ·
                      refine ⟨4158760437226673744690161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5545013916302231659586881 4158760437226673744690161)
                      ·
                        rfl

theorem cell23_8099157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 1, 2, 2, 4, 2].length) (baseStart_8099157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8099157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8099157 prefixEnd_8099157 := by exact prefixLift 8099157
  have htrace : WordTrace (prefixWord ++ tailWord_8099157) baseStart_8099157 baseEnd_8099157 := by
    simpa [prefixWord, tailWord_8099157, baseEnd_8099157] using wordTrace_append hprefix tailTrace_8099157
  have hstable : (prefixWord ++ tailWord_8099157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8099157).length < 2 ^ (prefixWord ++ tailWord_8099157).sum := by decide
  have hdescent : baseEnd_8099157 < baseStart_8099157 := by decide
  rcases family_descends (prefixWord ++ tailWord_8099157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8099160 : List Nat := [2, 1, 2, 2, 1, 1, 4, 1, 4, 2, 3]
def baseStart_8099160 : Nat := 118140960795 + 8099160 * 2 ^ 59
def prefixEnd_8099160 : Nat := 4983230072969 + 3 ^ 40 * 8099160 * 2
def baseEnd_8099160 : Nat := 4158761977668637232952647

theorem tailTrace_8099160 : CollatzResearch.WordTrace tailWord_8099160 prefixEnd_8099160 4158761977668637232952647 := by
  unfold tailWord_8099160
  simp only [CollatzResearch.WordTrace]
  refine ⟨147700316669067010624415467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196933755558756014165887289 147700316669067010624415467)
  ·
    refine ⟨221550475003600515936623201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147700316669067010624415467 221550475003600515936623201)
    ·
      refine ⟨166162856252700386952467401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 221550475003600515936623201 166162856252700386952467401)
      ·
        refine ⟨124622142189525290214350551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 166162856252700386952467401 124622142189525290214350551)
        ·
          refine ⟨186933213284287935321525827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124622142189525290214350551 186933213284287935321525827)
          ·
            refine ⟨280399819926431902982288741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 186933213284287935321525827 280399819926431902982288741)
            ·
              refine ⟨52574966236205981809179139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 280399819926431902982288741 52574966236205981809179139)
              ·
                refine ⟨78862449354308972713768709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52574966236205981809179139 78862449354308972713768709)
                ·
                  refine ⟨14786709253932932383831633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 78862449354308972713768709 14786709253932932383831633)
                  ·
                    refine ⟨11090031940449699287873725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14786709253932932383831633 11090031940449699287873725)
                    ·
                      refine ⟨4158761977668637232952647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11090031940449699287873725 4158761977668637232952647)
                      ·
                        rfl

theorem cell23_8099160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 4, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 4, 1, 4, 2, 3].length) (baseStart_8099160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8099160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8099160 prefixEnd_8099160 := by exact prefixLift 8099160
  have htrace : WordTrace (prefixWord ++ tailWord_8099160) baseStart_8099160 baseEnd_8099160 := by
    simpa [prefixWord, tailWord_8099160, baseEnd_8099160] using wordTrace_append hprefix tailTrace_8099160
  have hstable : (prefixWord ++ tailWord_8099160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8099160).length < 2 ^ (prefixWord ++ tailWord_8099160).sum := by decide
  have hdescent : baseEnd_8099160 < baseStart_8099160 := by decide
  rcases family_descends (prefixWord ++ tailWord_8099160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8099170 : List Nat := [3, 3, 2, 1, 1, 1, 1, 2, 2, 1, 6]
def baseStart_8099170 : Nat := 118140960795 + 8099170 * 2 ^ 59
def prefixEnd_8099170 : Nat := 4983230072969 + 3 ^ 40 * 8099170 * 2
def baseEnd_8099170 : Nat := 4158767112475182193827601

theorem tailTrace_8099170 : CollatzResearch.WordTrace tailWord_8099170 prefixEnd_8099170 4158767112475182193827601 := by
  unfold tailWord_8099170
  simp only [CollatzResearch.WordTrace]
  refine ⟨73850249517024448239173741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 196933998712065195304463309 73850249517024448239173741)
  ·
    refine ⟨27693843568884168089690153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73850249517024448239173741 27693843568884168089690153)
    ·
      refine ⟨20770382676663126067267615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27693843568884168089690153 20770382676663126067267615)
      ·
        refine ⟨31155574014994689100901423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20770382676663126067267615 31155574014994689100901423)
        ·
          refine ⟨46733361022492033651352135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31155574014994689100901423 46733361022492033651352135)
          ·
            refine ⟨70100041533738050477028203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46733361022492033651352135 70100041533738050477028203)
            ·
              refine ⟨105150062300607075715542305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70100041533738050477028203 105150062300607075715542305)
              ·
                refine ⟨78862546725455306786656729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 105150062300607075715542305 78862546725455306786656729)
                ·
                  refine ⟨59146910044091480089992547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 78862546725455306786656729 59146910044091480089992547)
                  ·
                    refine ⟨88720365066137220134988821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 59146910044091480089992547 88720365066137220134988821)
                    ·
                      refine ⟨4158767112475182193827601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 88720365066137220134988821 4158767112475182193827601)
                      ·
                        rfl

theorem cell23_8099170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 1, 2, 2, 1, 6].length) (baseStart_8099170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8099170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8099170 prefixEnd_8099170 := by exact prefixLift 8099170
  have htrace : WordTrace (prefixWord ++ tailWord_8099170) baseStart_8099170 baseEnd_8099170 := by
    simpa [prefixWord, tailWord_8099170, baseEnd_8099170] using wordTrace_append hprefix tailTrace_8099170
  have hstable : (prefixWord ++ tailWord_8099170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8099170).length < 2 ^ (prefixWord ++ tailWord_8099170).sum := by decide
  have hdescent : baseEnd_8099170 < baseStart_8099170 := by decide
  rcases family_descends (prefixWord ++ tailWord_8099170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8099183 : List Nat := [1, 1, 2, 1, 3, 1, 3, 2, 1, 2, 6]
def baseStart_8099183 : Nat := 118140960795 + 8099183 * 2 ^ 59
def prefixEnd_8099183 : Nat := 4983230072969 + 3 ^ 40 * 8099183 * 2
def baseEnd_8099183 : Nat := 4158773787723690642965041

theorem tailTrace_8099183 : CollatzResearch.WordTrace tailWord_8099183 prefixEnd_8099183 4158773787723690642965041 := by
  unfold tailWord_8099183
  simp only [CollatzResearch.WordTrace]
  refine ⟨295401472217050696176918203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196934314811367130784612135 295401472217050696176918203)
  ·
    refine ⟨443102208325576044265377305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 295401472217050696176918203 443102208325576044265377305)
    ·
      refine ⟨332326656244182033199032979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 443102208325576044265377305 332326656244182033199032979)
      ·
        refine ⟨498489984366273049798549469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 332326656244182033199032979 498489984366273049798549469)
        ·
          refine ⟨186933744137352393674456051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 498489984366273049798549469 186933744137352393674456051)
          ·
            refine ⟨280400616206028590511684077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 186933744137352393674456051 280400616206028590511684077)
            ·
              refine ⟨105150231077260721441881529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 280400616206028590511684077 105150231077260721441881529)
              ·
                refine ⟨78862673307945541081411147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 105150231077260721441881529 78862673307945541081411147)
                ·
                  refine ⟨118294009961918311622116721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 78862673307945541081411147 118294009961918311622116721)
                  ·
                    refine ⟨88720507471438733716587541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 118294009961918311622116721 88720507471438733716587541)
                    ·
                      refine ⟨4158773787723690642965041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 88720507471438733716587541 4158773787723690642965041)
                      ·
                        rfl

theorem cell23_8099183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 3, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 3, 2, 1, 2, 6].length) (baseStart_8099183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8099183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8099183 prefixEnd_8099183 := by exact prefixLift 8099183
  have htrace : WordTrace (prefixWord ++ tailWord_8099183) baseStart_8099183 baseEnd_8099183 := by
    simpa [prefixWord, tailWord_8099183, baseEnd_8099183] using wordTrace_append hprefix tailTrace_8099183
  have hstable : (prefixWord ++ tailWord_8099183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8099183).length < 2 ^ (prefixWord ++ tailWord_8099183).sum := by decide
  have hdescent : baseEnd_8099183 < baseStart_8099183 := by decide
  rcases family_descends (prefixWord ++ tailWord_8099183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8099217 : List Nat := [1, 2, 2, 1, 1, 1, 2, 6, 2, 3, 2]
def baseStart_8099217 : Nat := 118140960795 + 8099217 * 2 ^ 59
def prefixEnd_8099217 : Nat := 4983230072969 + 3 ^ 40 * 8099217 * 2
def baseEnd_8099217 : Nat := 4158791246065943509939885

theorem tailTrace_8099217 : CollatzResearch.WordTrace tailWord_8099217 prefixEnd_8099217 4158791246065943509939885 := by
  unfold tailWord_8099217
  simp only [CollatzResearch.WordTrace]
  refine ⟨295402712298927519983655905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196935141532618346655770603 295402712298927519983655905)
  ·
    refine ⟨221552034224195639987741929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 295402712298927519983655905 221552034224195639987741929)
    ·
      refine ⟨166164025668146729990806447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 221552034224195639987741929 166164025668146729990806447)
      ·
        refine ⟨249246038502220094986209671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166164025668146729990806447 249246038502220094986209671)
        ·
          refine ⟨373869057753330142479314507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 249246038502220094986209671 373869057753330142479314507)
          ·
            refine ⟨560803586629995213718971761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 373869057753330142479314507 560803586629995213718971761)
            ·
              refine ⟨420602689972496410289228821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 560803586629995213718971761 420602689972496410289228821)
              ·
                refine ⟨19715751092460769232307601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 420602689972496410289228821 19715751092460769232307601)
                ·
                  refine ⟨14786813319345576924230701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19715751092460769232307601 14786813319345576924230701)
                  ·
                    refine ⟨5545054994754591346586513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14786813319345576924230701 5545054994754591346586513)
                    ·
                      refine ⟨4158791246065943509939885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5545054994754591346586513 4158791246065943509939885)
                      ·
                        rfl

theorem cell23_8099217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 3, 2].length) (baseStart_8099217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8099217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8099217 prefixEnd_8099217 := by exact prefixLift 8099217
  have htrace : WordTrace (prefixWord ++ tailWord_8099217) baseStart_8099217 baseEnd_8099217 := by
    simpa [prefixWord, tailWord_8099217, baseEnd_8099217] using wordTrace_append hprefix tailTrace_8099217
  have hstable : (prefixWord ++ tailWord_8099217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8099217).length < 2 ^ (prefixWord ++ tailWord_8099217).sum := by decide
  have hdescent : baseEnd_8099217 < baseStart_8099217 := by decide
  rcases family_descends (prefixWord ++ tailWord_8099217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8099218 : List Nat := [3, 2, 3, 3, 2, 1, 1, 1, 3, 4]
def baseStart_8099218 : Nat := 118140960795 + 8099218 * 2 ^ 59
def prefixEnd_8099218 : Nat := 4983230072969 + 3 ^ 40 * 8099218 * 2
def baseEnd_8099218 : Nat := 1386263919848866002009127

theorem tailTrace_8099218 : CollatzResearch.WordTrace tailWord_8099218 prefixEnd_8099218 1386263919848866002009127 := by
  unfold tailWord_8099218
  simp only [CollatzResearch.WordTrace]
  refine ⟨73850687192980974288610577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 196935165847949264769628205 73850687192980974288610577)
  ·
    refine ⟨55388015394735730716457933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73850687192980974288610577 55388015394735730716457933)
    ·
      refine ⟨20770505773025899018671725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55388015394735730716457933 20770505773025899018671725)
      ·
        refine ⟨7788939664884712132001897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20770505773025899018671725 7788939664884712132001897)
        ·
          refine ⟨5841704748663534099001423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7788939664884712132001897 5841704748663534099001423)
          ·
            refine ⟨8762557122995301148502135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5841704748663534099001423 8762557122995301148502135)
            ·
              refine ⟨13143835684492951722753203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8762557122995301148502135 13143835684492951722753203)
              ·
                refine ⟨19715753526739427584129805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13143835684492951722753203 19715753526739427584129805)
                ·
                  refine ⟨7393407572527285344048677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19715753526739427584129805 7393407572527285344048677)
                  ·
                    refine ⟨1386263919848866002009127, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7393407572527285344048677 1386263919848866002009127)
                    ·
                      rfl

theorem cell23_8099218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 2, 1, 1, 1, 3, 4].length) (baseStart_8099218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8099218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8099218 prefixEnd_8099218 := by exact prefixLift 8099218
  have htrace : WordTrace (prefixWord ++ tailWord_8099218) baseStart_8099218 baseEnd_8099218 := by
    simpa [prefixWord, tailWord_8099218, baseEnd_8099218] using wordTrace_append hprefix tailTrace_8099218
  have hstable : (prefixWord ++ tailWord_8099218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8099218).length < 2 ^ (prefixWord ++ tailWord_8099218).sum := by decide
  have hdescent : baseEnd_8099218 < baseStart_8099218 := by decide
  rcases family_descends (prefixWord ++ tailWord_8099218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8099257 : List Nat := [1, 2, 1, 4, 4, 1, 1, 2, 1, 6]
def baseStart_8099257 : Nat := 118140960795 + 8099257 * 2 ^ 59
def prefixEnd_8099257 : Nat := 4983230072969 + 3 ^ 40 * 8099257 * 2
def baseEnd_8099257 : Nat := 1386270595097374451146567

theorem tailTrace_8099257 : CollatzResearch.WordTrace tailWord_8099257 prefixEnd_8099257 1386270595097374451146567 := by
  unfold tailWord_8099257
  simp only [CollatzResearch.WordTrace]
  refine ⟨295404171218782606815112025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196936114145855071210074683 295404171218782606815112025)
  ·
    refine ⟨221553128414086955111334019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 295404171218782606815112025 221553128414086955111334019)
    ·
      refine ⟨332329692621130432667001029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 221553128414086955111334019 332329692621130432667001029)
      ·
        refine ⟨62311817366461956125062693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 332329692621130432667001029 62311817366461956125062693)
        ·
          refine ⟨11683465756211616773449255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 62311817366461956125062693 11683465756211616773449255)
          ·
            refine ⟨17525198634317425160173883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11683465756211616773449255 17525198634317425160173883)
            ·
              refine ⟨26287797951476137740260825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17525198634317425160173883 26287797951476137740260825)
              ·
                refine ⟨19715848463607103305195619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26287797951476137740260825 19715848463607103305195619)
                ·
                  refine ⟨29573772695410654957793429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19715848463607103305195619 29573772695410654957793429)
                  ·
                    refine ⟨1386270595097374451146567, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29573772695410654957793429 1386270595097374451146567)
                    ·
                      rfl

theorem cell23_8099257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 1, 1, 2, 1, 6].length) (baseStart_8099257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8099257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8099257 prefixEnd_8099257 := by exact prefixLift 8099257
  have htrace : WordTrace (prefixWord ++ tailWord_8099257) baseStart_8099257 baseEnd_8099257 := by
    simpa [prefixWord, tailWord_8099257, baseEnd_8099257] using wordTrace_append hprefix tailTrace_8099257
  have hstable : (prefixWord ++ tailWord_8099257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8099257).length < 2 ^ (prefixWord ++ tailWord_8099257).sum := by decide
  have hdescent : baseEnd_8099257 < baseStart_8099257 := by decide
  rcases family_descends (prefixWord ++ tailWord_8099257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8099267 : List Nat := [1, 1, 1, 3, 1, 1, 4, 5, 1, 2, 3]
def baseStart_8099267 : Nat := 118140960795 + 8099267 * 2 ^ 59
def prefixEnd_8099267 : Nat := 4983230072969 + 3 ^ 40 * 8099267 * 2
def baseEnd_8099267 : Nat := 4158816920098668314314655

theorem tailTrace_8099267 : CollatzResearch.WordTrace tailWord_8099267 prefixEnd_8099267 4158816920098668314314655 := by
  unfold tailWord_8099267
  simp only [CollatzResearch.WordTrace]
  refine ⟨295404535948746378522976055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196936357299164252348650703 295404535948746378522976055)
  ·
    refine ⟨443106803923119567784464083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 295404535948746378522976055 443106803923119567784464083)
    ·
      refine ⟨664660205884679351676696125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 443106803923119567784464083 664660205884679351676696125)
      ·
        refine ⟨249247577206754756878761047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 664660205884679351676696125 249247577206754756878761047)
        ·
          refine ⟨373871365810132135318141571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 249247577206754756878761047 373871365810132135318141571)
          ·
            refine ⟨560807048715198202977212357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 373871365810132135318141571 560807048715198202977212357)
            ·
              refine ⟨105151321634099663058227317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 560807048715198202977212357 105151321634099663058227317)
              ·
                refine ⟨9857936403196843411708811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 105151321634099663058227317 9857936403196843411708811)
                ·
                  refine ⟨14786904604795265117563217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9857936403196843411708811 14786904604795265117563217)
                  ·
                    refine ⟨11090178453596448838172413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14786904604795265117563217 11090178453596448838172413)
                    ·
                      refine ⟨4158816920098668314314655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11090178453596448838172413 4158816920098668314314655)
                      ·
                        rfl

theorem cell23_8099267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 4, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 4, 5, 1, 2, 3].length) (baseStart_8099267 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8099267 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8099267 prefixEnd_8099267 := by exact prefixLift 8099267
  have htrace : WordTrace (prefixWord ++ tailWord_8099267) baseStart_8099267 baseEnd_8099267 := by
    simpa [prefixWord, tailWord_8099267, baseEnd_8099267] using wordTrace_append hprefix tailTrace_8099267
  have hstable : (prefixWord ++ tailWord_8099267).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8099267).length < 2 ^ (prefixWord ++ tailWord_8099267).sum := by decide
  have hdescent : baseEnd_8099267 < baseStart_8099267 := by decide
  rcases family_descends (prefixWord ++ tailWord_8099267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8099274 : List Nat := [3, 1, 2, 1, 2, 4, 2, 2, 2, 4]
def baseStart_8099274 : Nat := 118140960795 + 8099274 * 2 ^ 59
def prefixEnd_8099274 : Nat := 4983230072969 + 3 ^ 40 * 8099274 * 2
def baseEnd_8099274 : Nat := 1386273504821083262309041

theorem tailTrace_8099274 : CollatzResearch.WordTrace tailWord_8099274 prefixEnd_8099274 1386273504821083262309041 := by
  unfold tailWord_8099274
  simp only [CollatzResearch.WordTrace]
  refine ⟨73851197814930254679620219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 196936527506480679145653917 73851197814930254679620219)
  ·
    refine ⟨110776796722395382019430329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73851197814930254679620219 110776796722395382019430329)
    ·
      refine ⟨83082597541796536514572747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110776796722395382019430329 83082597541796536514572747)
      ·
        refine ⟨124623896312694804771859121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83082597541796536514572747 124623896312694804771859121)
        ·
          refine ⟨93467922234521103578894341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 124623896312694804771859121 93467922234521103578894341)
          ·
            refine ⟨17525235418972706921042689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 93467922234521103578894341 17525235418972706921042689)
            ·
              refine ⟨13143926564229530190782017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17525235418972706921042689 13143926564229530190782017)
              ·
                refine ⟨9857944923172147643086513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13143926564229530190782017 9857944923172147643086513)
                ·
                  refine ⟨7393458692379110732314885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9857944923172147643086513 7393458692379110732314885)
                  ·
                    refine ⟨1386273504821083262309041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7393458692379110732314885 1386273504821083262309041)
                    ·
                      rfl

theorem cell23_8099274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 4, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 4, 2, 2, 2, 4].length) (baseStart_8099274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8099274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8099274 prefixEnd_8099274 := by exact prefixLift 8099274
  have htrace : WordTrace (prefixWord ++ tailWord_8099274) baseStart_8099274 baseEnd_8099274 := by
    simpa [prefixWord, tailWord_8099274, baseEnd_8099274] using wordTrace_append hprefix tailTrace_8099274
  have hstable : (prefixWord ++ tailWord_8099274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8099274).length < 2 ^ (prefixWord ++ tailWord_8099274).sum := by decide
  have hdescent : baseEnd_8099274 < baseStart_8099274 := by decide
  rcases family_descends (prefixWord ++ tailWord_8099274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8099297 : List Nat := [1, 2, 3, 1, 2, 3, 1, 3, 1, 3, 3]
def baseStart_8099297 : Nat := 118140960795 + 8099297 * 2 ^ 59
def prefixEnd_8099297 : Nat := 4983230072969 + 3 ^ 40 * 8099297 * 2
def baseEnd_8099297 : Nat := 4158832324518303196939517

theorem tailTrace_8099297 : CollatzResearch.WordTrace tailWord_8099297 prefixEnd_8099297 4158832324518303196939517 := by
  unfold tailWord_8099297
  simp only [CollatzResearch.WordTrace]
  refine ⟨295405630138637693646568145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196937086759091795764378763 295405630138637693646568145)
  ·
    refine ⟨221554222603978270234926109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 295405630138637693646568145 221554222603978270234926109)
    ·
      refine ⟨83082833476491851338097291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 221554222603978270234926109 83082833476491851338097291)
      ·
        refine ⟨124624250214737777007145937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83082833476491851338097291 124624250214737777007145937)
        ·
          refine ⟨93468187661053332755359453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 124624250214737777007145937 93468187661053332755359453)
          ·
            refine ⟨35050570372894999783259795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 93468187661053332755359453 35050570372894999783259795)
            ·
              refine ⟨52575855559342499674889693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35050570372894999783259795 52575855559342499674889693)
              ·
                refine ⟨19715945834753437378083635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52575855559342499674889693 19715945834753437378083635)
                ·
                  refine ⟨29573918752130156067125453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19715945834753437378083635 29573918752130156067125453)
                  ·
                    refine ⟨11090219532048808525172045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29573918752130156067125453 11090219532048808525172045)
                    ·
                      refine ⟨4158832324518303196939517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11090219532048808525172045 4158832324518303196939517)
                      ·
                        rfl

theorem cell23_8099297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 1, 3, 1, 3, 3].length) (baseStart_8099297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8099297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8099297 prefixEnd_8099297 := by exact prefixLift 8099297
  have htrace : WordTrace (prefixWord ++ tailWord_8099297) baseStart_8099297 baseEnd_8099297 := by
    simpa [prefixWord, tailWord_8099297, baseEnd_8099297] using wordTrace_append hprefix tailTrace_8099297
  have hstable : (prefixWord ++ tailWord_8099297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8099297).length < 2 ^ (prefixWord ++ tailWord_8099297).sum := by decide
  have hdescent : baseEnd_8099297 < baseStart_8099297 := by decide
  rcases family_descends (prefixWord ++ tailWord_8099297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8099314 : List Nat := [3, 2, 1, 4, 1, 1, 2, 2, 1, 3, 3]
def baseStart_8099314 : Nat := 118140960795 + 8099314 * 2 ^ 59
def prefixEnd_8099314 : Nat := 4983230072969 + 3 ^ 40 * 8099314 * 2
def baseEnd_8099314 : Nat := 4158841053689429630426939

theorem tailTrace_8099314 : CollatzResearch.WordTrace tailWord_8099314 prefixEnd_8099314 4158841053689429630426939 := by
  unfold tailWord_8099314
  simp only [CollatzResearch.WordTrace]
  refine ⟨73851562544894026387484249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 196937500119717403699957997 73851562544894026387484249)
  ·
    refine ⟨55388671908670519790613187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73851562544894026387484249 55388671908670519790613187)
    ·
      refine ⟨83083007863005779685919781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55388671908670519790613187 83083007863005779685919781)
      ·
        refine ⟨15578063974313583691109959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 83083007863005779685919781 15578063974313583691109959)
        ·
          refine ⟨23367095961470375536664939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15578063974313583691109959 23367095961470375536664939)
          ·
            refine ⟨35050643942205563304997409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23367095961470375536664939 35050643942205563304997409)
            ·
              refine ⟨26287982956654172478748057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35050643942205563304997409 26287982956654172478748057)
              ·
                refine ⟨19715987217490629359061043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26287982956654172478748057 19715987217490629359061043)
                ·
                  refine ⟨29573980826235944038591565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19715987217490629359061043 29573980826235944038591565)
                  ·
                    refine ⟨11090242809838479014471837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29573980826235944038591565 11090242809838479014471837)
                    ·
                      refine ⟨4158841053689429630426939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11090242809838479014471837 4158841053689429630426939)
                      ·
                        rfl

theorem cell23_8099314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 2, 2, 1, 3, 3].length) (baseStart_8099314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8099314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8099314 prefixEnd_8099314 := by exact prefixLift 8099314
  have htrace : WordTrace (prefixWord ++ tailWord_8099314) baseStart_8099314 baseEnd_8099314 := by
    simpa [prefixWord, tailWord_8099314, baseEnd_8099314] using wordTrace_append hprefix tailTrace_8099314
  have hstable : (prefixWord ++ tailWord_8099314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8099314).length < 2 ^ (prefixWord ++ tailWord_8099314).sum := by decide
  have hdescent : baseEnd_8099314 < baseStart_8099314 := by decide
  rcases family_descends (prefixWord ++ tailWord_8099314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8099318 : List Nat := [5, 1, 1, 1, 2, 4, 2, 1, 1, 2, 3]
def baseStart_8099318 : Nat := 118140960795 + 8099318 * 2 ^ 59
def prefixEnd_8099318 : Nat := 4983230072969 + 3 ^ 40 * 8099318 * 2
def baseEnd_8099318 : Nat := 4158843107612047614776921

theorem tailTrace_8099318 : CollatzResearch.WordTrace tailWord_8099318 prefixEnd_8099318 4158843107612047614776921 := by
  unfold tailWord_8099318
  simp only [CollatzResearch.WordTrace]
  refine ⟨18462899754472600889567663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 196937597381041076155388405 18462899754472600889567663)
  ·
    refine ⟨27694349631708901334351495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18462899754472600889567663 27694349631708901334351495)
    ·
      refine ⟨41541524447563352001527243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27694349631708901334351495 41541524447563352001527243)
      ·
        refine ⟨62312286671345028002290865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41541524447563352001527243 62312286671345028002290865)
        ·
          refine ⟨46734215003508771001718149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62312286671345028002290865 46734215003508771001718149)
          ·
            refine ⟨8762665313157894562822153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 46734215003508771001718149 8762665313157894562822153)
            ·
              refine ⟨6571998984868420922116615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8762665313157894562822153 6571998984868420922116615)
              ·
                refine ⟨9857998477302631383174923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6571998984868420922116615 9857998477302631383174923)
                ·
                  refine ⟨14786997715953947074762385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9857998477302631383174923 14786997715953947074762385)
                  ·
                    refine ⟨11090248286965460306071789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14786997715953947074762385 11090248286965460306071789)
                    ·
                      refine ⟨4158843107612047614776921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11090248286965460306071789 4158843107612047614776921)
                      ·
                        rfl

theorem cell23_8099318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 4, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 4, 2, 1, 1, 2, 3].length) (baseStart_8099318 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8099318 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8099318 prefixEnd_8099318 := by exact prefixLift 8099318
  have htrace : WordTrace (prefixWord ++ tailWord_8099318) baseStart_8099318 baseEnd_8099318 := by
    simpa [prefixWord, tailWord_8099318, baseEnd_8099318] using wordTrace_append hprefix tailTrace_8099318
  have hstable : (prefixWord ++ tailWord_8099318).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8099318).length < 2 ^ (prefixWord ++ tailWord_8099318).sum := by decide
  have hdescent : baseEnd_8099318 < baseStart_8099318 := by decide
  rcases family_descends (prefixWord ++ tailWord_8099318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8099348 : List Nat := [2, 4, 3, 1, 2, 2, 1, 1, 1, 3, 3]
def baseStart_8099348 : Nat := 118140960795 + 8099348 * 2 ^ 59
def prefixEnd_8099348 : Nat := 4983230072969 + 3 ^ 40 * 8099348 * 2
def baseEnd_8099348 : Nat := 4158858512031682497401783

theorem tailTrace_8099348 : CollatzResearch.WordTrace tailWord_8099348 prefixEnd_8099348 4158858512031682497401783 := by
  unfold tailWord_8099348
  simp only [CollatzResearch.WordTrace]
  refine ⟨147703745130726464678337349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196938326840968619571116465 147703745130726464678337349)
  ·
    refine ⟨27694452212011212127188253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 147703745130726464678337349 27694452212011212127188253)
    ·
      refine ⟨10385419579504204547695595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27694452212011212127188253 10385419579504204547695595)
      ·
        refine ⟨15578129369256306821543393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10385419579504204547695595 15578129369256306821543393)
        ·
          refine ⟨11683597026942230116157545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15578129369256306821543393 11683597026942230116157545)
          ·
            refine ⟨8762697770206672587118159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11683597026942230116157545 8762697770206672587118159)
            ·
              refine ⟨13144046655310008880677239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8762697770206672587118159 13144046655310008880677239)
              ·
                refine ⟨19716069982965013321015859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13144046655310008880677239 19716069982965013321015859)
                ·
                  refine ⟨29574104974447519981523789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19716069982965013321015859 29574104974447519981523789)
                  ·
                    refine ⟨11090289365417819993071421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29574104974447519981523789 11090289365417819993071421)
                    ·
                      refine ⟨4158858512031682497401783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11090289365417819993071421 4158858512031682497401783)
                      ·
                        rfl

theorem cell23_8099348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 2, 1, 1, 1, 3, 3].length) (baseStart_8099348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8099348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8099348 prefixEnd_8099348 := by exact prefixLift 8099348
  have htrace : WordTrace (prefixWord ++ tailWord_8099348) baseStart_8099348 baseEnd_8099348 := by
    simpa [prefixWord, tailWord_8099348, baseEnd_8099348] using wordTrace_append hprefix tailTrace_8099348
  have hstable : (prefixWord ++ tailWord_8099348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8099348).length < 2 ^ (prefixWord ++ tailWord_8099348).sum := by decide
  have hdescent : baseEnd_8099348 < baseStart_8099348 := by decide
  rcases family_descends (prefixWord ++ tailWord_8099348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8099357 : List Nat := [1, 4, 2, 2, 1, 1, 2, 2, 2, 1, 5]
def baseStart_8099357 : Nat := 118140960795 + 8099357 * 2 ^ 59
def prefixEnd_8099357 : Nat := 4983230072969 + 3 ^ 40 * 8099357 * 2
def baseEnd_8099357 : Nat := 4158863133357572962189241

theorem tailTrace_8099357 : CollatzResearch.WordTrace tailWord_8099357 prefixEnd_8099357 4158863133357572962189241 := by
  unfold tailWord_8099357
  simp only [CollatzResearch.WordTrace]
  refine ⟨295407818518420323893752325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196938545678946882595834883 295407818518420323893752325)
  ·
    refine ⟨55388965972203810730078561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 295407818518420323893752325 55388965972203810730078561)
    ·
      refine ⟨41541724479152858047558921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55388965972203810730078561 41541724479152858047558921)
      ·
        refine ⟨31156293359364643535669191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41541724479152858047558921 31156293359364643535669191)
        ·
          refine ⟨46734440039046965303503787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31156293359364643535669191 46734440039046965303503787)
          ·
            refine ⟨70101660058570447955255681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46734440039046965303503787 70101660058570447955255681)
            ·
              refine ⟨52576245043927835966441761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70101660058570447955255681 52576245043927835966441761)
              ·
                refine ⟨39432183782945876974831321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52576245043927835966441761 39432183782945876974831321)
                ·
                  refine ⟨29574137837209407731123491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39432183782945876974831321 29574137837209407731123491)
                  ·
                    refine ⟨44361206755814111596685237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29574137837209407731123491 44361206755814111596685237)
                    ·
                      refine ⟨4158863133357572962189241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44361206755814111596685237 4158863133357572962189241)
                      ·
                        rfl

theorem cell23_8099357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 2, 2, 2, 1, 5].length) (baseStart_8099357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8099357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8099357 prefixEnd_8099357 := by exact prefixLift 8099357
  have htrace : WordTrace (prefixWord ++ tailWord_8099357) baseStart_8099357 baseEnd_8099357 := by
    simpa [prefixWord, tailWord_8099357, baseEnd_8099357] using wordTrace_append hprefix tailTrace_8099357
  have hstable : (prefixWord ++ tailWord_8099357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8099357).length < 2 ^ (prefixWord ++ tailWord_8099357).sum := by decide
  have hdescent : baseEnd_8099357 < baseStart_8099357 := by decide
  rcases family_descends (prefixWord ++ tailWord_8099357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8099374 : List Nat := [4, 1, 3, 1, 2, 2, 1, 1, 2, 1, 5]
def baseStart_8099374 : Nat := 118140960795 + 8099374 * 2 ^ 59
def prefixEnd_8099374 : Nat := 4983230072969 + 3 ^ 40 * 8099374 * 2
def baseEnd_8099374 : Nat := 4158871862528699395676663

theorem tailTrace_8099374 : CollatzResearch.WordTrace tailWord_8099374 prefixEnd_8099374 4158871862528699395676663 := by
  unfold tailWord_8099374
  simp only [CollatzResearch.WordTrace]
  refine ⟨36926054819919841974640147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 196938959039572490531414117 36926054819919841974640147)
  ·
    refine ⟨55389082229879762961960221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36926054819919841974640147 55389082229879762961960221)
    ·
      refine ⟨20770905836204911110735083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55389082229879762961960221 20770905836204911110735083)
      ·
        refine ⟨31156358754307366666102625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20770905836204911110735083 31156358754307366666102625)
        ·
          refine ⟨23367269065730524999576969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31156358754307366666102625 23367269065730524999576969)
          ·
            refine ⟨17525451799297893749682727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23367269065730524999576969 17525451799297893749682727)
            ·
              refine ⟨26288177698946840624524091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17525451799297893749682727 26288177698946840624524091)
              ·
                refine ⟨39432266548420260936786137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26288177698946840624524091 39432266548420260936786137)
                ·
                  refine ⟨29574199911315195702589603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39432266548420260936786137 29574199911315195702589603)
                  ·
                    refine ⟨44361299866972793553884405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29574199911315195702589603 44361299866972793553884405)
                    ·
                      refine ⟨4158871862528699395676663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44361299866972793553884405 4158871862528699395676663)
                      ·
                        rfl

theorem cell23_8099374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 2, 1, 1, 2, 1, 5].length) (baseStart_8099374 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8099374 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8099374 prefixEnd_8099374 := by exact prefixLift 8099374
  have htrace : WordTrace (prefixWord ++ tailWord_8099374) baseStart_8099374 baseEnd_8099374 := by
    simpa [prefixWord, tailWord_8099374, baseEnd_8099374] using wordTrace_append hprefix tailTrace_8099374
  have hstable : (prefixWord ++ tailWord_8099374).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8099374).length < 2 ^ (prefixWord ++ tailWord_8099374).sum := by decide
  have hdescent : baseEnd_8099374 < baseStart_8099374 := by decide
  rcases family_descends (prefixWord ++ tailWord_8099374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8099405 : List Nat := [1, 6, 1, 1, 3, 1, 1, 3, 2, 2, 2]
def baseStart_8099405 : Nat := 118140960795 + 8099405 * 2 ^ 59
def prefixEnd_8099405 : Nat := 4983230072969 + 3 ^ 40 * 8099405 * 2
def baseEnd_8099405 : Nat := 4158887780428988774389021

theorem tailTrace_8099405 : CollatzResearch.WordTrace tailWord_8099405 prefixEnd_8099405 4158887780428988774389021 := by
  unfold tailWord_8099405
  simp only [CollatzResearch.WordTrace]
  refine ⟨295409569222246428091499669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196939712814830952060999779 295409569222246428091499669)
  ·
    refine ⟨13847323557292801316789047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 295409569222246428091499669 13847323557292801316789047)
    ·
      refine ⟨20770985335939201975183571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13847323557292801316789047 20770985335939201975183571)
      ·
        refine ⟨31156478003908802962775357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20770985335939201975183571 31156478003908802962775357)
        ·
          refine ⟨11683679251465801111040759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31156478003908802962775357 11683679251465801111040759)
          ·
            refine ⟨17525518877198701666561139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11683679251465801111040759 17525518877198701666561139)
            ·
              refine ⟨26288278315798052499841709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17525518877198701666561139 26288278315798052499841709)
              ·
                refine ⟨9858104368424269687440641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26288278315798052499841709 9858104368424269687440641)
                ·
                  refine ⟨7393578276318202265580481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9858104368424269687440641 7393578276318202265580481)
                  ·
                    refine ⟨5545183707238651699185361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7393578276318202265580481 5545183707238651699185361)
                    ·
                      refine ⟨4158887780428988774389021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5545183707238651699185361 4158887780428988774389021)
                      ·
                        rfl

theorem cell23_8099405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 1, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 1, 1, 3, 2, 2, 2].length) (baseStart_8099405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8099405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8099405 prefixEnd_8099405 := by exact prefixLift 8099405
  have htrace : WordTrace (prefixWord ++ tailWord_8099405) baseStart_8099405 baseEnd_8099405 := by
    simpa [prefixWord, tailWord_8099405, baseEnd_8099405] using wordTrace_append hprefix tailTrace_8099405
  have hstable : (prefixWord ++ tailWord_8099405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8099405).length < 2 ^ (prefixWord ++ tailWord_8099405).sum := by decide
  have hdescent : baseEnd_8099405 < baseStart_8099405 := by decide
  rcases family_descends (prefixWord ++ tailWord_8099405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8099447 : List Nat := [1, 1, 3, 1, 1, 3, 1, 2, 3, 4, 3]
def baseStart_8099447 : Nat := 118140960795 + 8099447 * 2 ^ 59
def prefixEnd_8099447 : Nat := 4983230072969 + 3 ^ 40 * 8099447 * 2
def baseEnd_8099447 : Nat := 4158909346616477610063827

theorem tailTrace_8099447 : CollatzResearch.WordTrace tailWord_8099447 prefixEnd_8099447 4158909346616477610063827 := by
  unfold tailWord_8099447
  simp only [CollatzResearch.WordTrace]
  refine ⟨295411101088094269264528595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196940734058729512843019063 295411101088094269264528595)
  ·
    refine ⟨443116651632141403896792893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 295411101088094269264528595 443116651632141403896792893)
    ·
      refine ⟨166168744362053026461297335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 443116651632141403896792893 166168744362053026461297335)
      ·
        refine ⟨249253116543079539691946003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166168744362053026461297335 249253116543079539691946003)
        ·
          refine ⟨373879674814619309537919005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 249253116543079539691946003 373879674814619309537919005)
          ·
            refine ⟨140204878055482241076719627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 373879674814619309537919005 140204878055482241076719627)
            ·
              refine ⟨210307317083223361615079441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 140204878055482241076719627 210307317083223361615079441)
              ·
                refine ⟨157730487812417521211309581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 210307317083223361615079441 157730487812417521211309581)
                ·
                  refine ⟨59148932929656570454241093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 157730487812417521211309581 59148932929656570454241093)
                  ·
                    refine ⟨11090424924310606960170205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 59148932929656570454241093 11090424924310606960170205)
                    ·
                      refine ⟨4158909346616477610063827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11090424924310606960170205 4158909346616477610063827)
                      ·
                        rfl

theorem cell23_8099447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 2, 3, 4, 3].length) (baseStart_8099447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8099447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8099447 prefixEnd_8099447 := by exact prefixLift 8099447
  have htrace : WordTrace (prefixWord ++ tailWord_8099447) baseStart_8099447 baseEnd_8099447 := by
    simpa [prefixWord, tailWord_8099447, baseEnd_8099447] using wordTrace_append hprefix tailTrace_8099447
  have hstable : (prefixWord ++ tailWord_8099447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8099447).length < 2 ^ (prefixWord ++ tailWord_8099447).sum := by decide
  have hdescent : baseEnd_8099447 < baseStart_8099447 := by decide
  rcases family_descends (prefixWord ++ tailWord_8099447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8099467 : List Nat := [1, 1, 1, 1, 4, 1, 3, 5, 6]
def baseStart_8099467 : Nat := 118140960795 + 8099467 * 2 ^ 59
def prefixEnd_8099467 : Nat := 4983230072969 + 3 ^ 40 * 8099467 * 2
def baseEnd_8099467 : Nat := 462102179581063059090415

theorem tailTrace_8099467 : CollatzResearch.WordTrace tailWord_8099467 prefixEnd_8099467 462102179581063059090415 := by
  unfold tailWord_8099467
  simp only [CollatzResearch.WordTrace]
  refine ⟨295411830548021812680256655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196941220365347875120171103 295411830548021812680256655)
  ·
    refine ⟨443117745822032719020384983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 295411830548021812680256655 443117745822032719020384983)
    ·
      refine ⟨664676618733049078530577475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 443117745822032719020384983 664676618733049078530577475)
      ·
        refine ⟨997014928099573617795866213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 664676618733049078530577475 997014928099573617795866213)
        ·
          refine ⟨186940299018670053336724915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 997014928099573617795866213 186940299018670053336724915)
          ·
            refine ⟨280410448528005080005087373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 186940299018670053336724915 280410448528005080005087373)
            ·
              refine ⟨105153918198001905001907765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 280410448528005080005087373 105153918198001905001907765)
              ·
                refine ⟨9858179831062678593928853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 105153918198001905001907765 9858179831062678593928853)
                ·
                  refine ⟨462102179581063059090415, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9858179831062678593928853 462102179581063059090415)
                  ·
                    rfl

theorem cell23_8099467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 3, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 3, 5, 6].length) (baseStart_8099467 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8099467 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8099467 prefixEnd_8099467 := by exact prefixLift 8099467
  have htrace : WordTrace (prefixWord ++ tailWord_8099467) baseStart_8099467 baseEnd_8099467 := by
    simpa [prefixWord, tailWord_8099467, baseEnd_8099467] using wordTrace_append hprefix tailTrace_8099467
  have hstable : (prefixWord ++ tailWord_8099467).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8099467).length < 2 ^ (prefixWord ++ tailWord_8099467).sum := by decide
  have hdescent : baseEnd_8099467 < baseStart_8099467 := by decide
  rcases family_descends (prefixWord ++ tailWord_8099467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8099488 : List Nat := [2, 1, 1, 4, 3, 2, 2, 3, 1, 4]
def baseStart_8099488 : Nat := 118140960795 + 8099488 * 2 ^ 59
def prefixEnd_8099488 : Nat := 4983230072969 + 3 ^ 40 * 8099488 * 2
def baseEnd_8099488 : Nat := 1386310133107770649883713

theorem tailTrace_8099488 : CollatzResearch.WordTrace tailWord_8099488 prefixEnd_8099488 1386310133107770649883713 := by
  unfold tailWord_8099488
  simp only [CollatzResearch.WordTrace]
  refine ⟨147706298240472866633385559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196941730987297155511180745 147706298240472866633385559)
  ·
    refine ⟨221559447360709299950078339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147706298240472866633385559 221559447360709299950078339)
    ·
      refine ⟨332339171041063949925117509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 221559447360709299950078339 332339171041063949925117509)
      ·
        refine ⟨62313594570199490610959533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 332339171041063949925117509 62313594570199490610959533)
        ·
          refine ⟨23367597963824808979109825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62313594570199490610959533 23367597963824808979109825)
          ·
            refine ⟨17525698472868606734332369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23367597963824808979109825 17525698472868606734332369)
            ·
              refine ⟨13144273854651455050749277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17525698472868606734332369 13144273854651455050749277)
              ·
                refine ⟨4929102695494295644030979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13144273854651455050749277 4929102695494295644030979)
                ·
                  refine ⟨7393654043241443466046469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4929102695494295644030979 7393654043241443466046469)
                  ·
                    refine ⟨1386310133107770649883713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7393654043241443466046469 1386310133107770649883713)
                    ·
                      rfl

theorem cell23_8099488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 2, 2, 3, 1, 4].length) (baseStart_8099488 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8099488 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8099488 prefixEnd_8099488 := by exact prefixLift 8099488
  have htrace : WordTrace (prefixWord ++ tailWord_8099488) baseStart_8099488 baseEnd_8099488 := by
    simpa [prefixWord, tailWord_8099488, baseEnd_8099488] using wordTrace_append hprefix tailTrace_8099488
  have hstable : (prefixWord ++ tailWord_8099488).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8099488).length < 2 ^ (prefixWord ++ tailWord_8099488).sum := by decide
  have hdescent : baseEnd_8099488 < baseStart_8099488 := by decide
  rcases family_descends (prefixWord ++ tailWord_8099488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8099511 : List Nat := [1, 1, 3, 1, 5, 1, 1, 3, 3, 1, 3]
def baseStart_8099511 : Nat := 118140960795 + 8099511 * 2 ^ 59
def prefixEnd_8099511 : Nat := 4983230072969 + 3 ^ 40 * 8099511 * 2
def baseEnd_8099511 : Nat := 4158942209378365359663533

theorem tailTrace_8099511 : CollatzResearch.WordTrace tailWord_8099511 prefixEnd_8099511 4158942209378365359663533 := by
  unfold tailWord_8099511
  simp only [CollatzResearch.WordTrace]
  refine ⟨295413435359862408194858387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196942290239908272129905591 295413435359862408194858387)
  ·
    refine ⟨443120153039793612292287581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 295413435359862408194858387 443120153039793612292287581)
    ·
      refine ⟨166170057389922604609607843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 443120153039793612292287581 166170057389922604609607843)
      ·
        refine ⟨249255086084883906914411765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166170057389922604609607843 249255086084883906914411765)
        ·
          refine ⟨23367664320457866273226103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 249255086084883906914411765 23367664320457866273226103)
          ·
            refine ⟨35051496480686799409839155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23367664320457866273226103 35051496480686799409839155)
            ·
              refine ⟨52577244721030199114758733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35051496480686799409839155 52577244721030199114758733)
              ·
                refine ⟨19716466770386324668034525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52577244721030199114758733 19716466770386324668034525)
                ·
                  refine ⟨7393675038894871750512947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19716466770386324668034525 7393675038894871750512947)
                  ·
                    refine ⟨11090512558342307625769421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7393675038894871750512947 11090512558342307625769421)
                    ·
                      refine ⟨4158942209378365359663533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11090512558342307625769421 4158942209378365359663533)
                      ·
                        rfl

theorem cell23_8099511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 1, 3, 3, 1, 3].length) (baseStart_8099511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8099511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8099511 prefixEnd_8099511 := by exact prefixLift 8099511
  have htrace : WordTrace (prefixWord ++ tailWord_8099511) baseStart_8099511 baseEnd_8099511 := by
    simpa [prefixWord, tailWord_8099511, baseEnd_8099511] using wordTrace_append hprefix tailTrace_8099511
  have hstable : (prefixWord ++ tailWord_8099511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8099511).length < 2 ^ (prefixWord ++ tailWord_8099511).sum := by decide
  have hdescent : baseEnd_8099511 < baseStart_8099511 := by decide
  rcases family_descends (prefixWord ++ tailWord_8099511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8099544 : List Nat := [2, 1, 2, 2, 3, 1, 1, 1, 6, 4]
def baseStart_8099544 : Nat := 118140960795 + 8099544 * 2 ^ 59
def prefixEnd_8099544 : Nat := 4983230072969 + 3 ^ 40 * 8099544 * 2
def baseEnd_8099544 : Nat := 1386319718079987910183627

theorem tailTrace_8099544 : CollatzResearch.WordTrace tailWord_8099544 prefixEnd_8099544 1386319718079987910183627 := by
  unfold tailWord_8099544
  simp only [CollatzResearch.WordTrace]
  refine ⟨147707319484371427415404843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196943092645828569887206457 147707319484371427415404843)
  ·
    refine ⟨221560979226557141123107265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147707319484371427415404843 221560979226557141123107265)
    ·
      refine ⟨166170734419917855842330449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 221560979226557141123107265 166170734419917855842330449)
      ·
        refine ⟨124628050814938391881747837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 166170734419917855842330449 124628050814938391881747837)
        ·
          refine ⟨46735519055601896955655439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 124628050814938391881747837 46735519055601896955655439)
          ·
            refine ⟨70103278583402845433483159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46735519055601896955655439 70103278583402845433483159)
            ·
              refine ⟨105154917875104268150224739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70103278583402845433483159 105154917875104268150224739)
              ·
                refine ⟨157732376812656402225337109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 105154917875104268150224739 157732376812656402225337109)
                ·
                  refine ⟨7393705163093268854312677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 157732376812656402225337109 7393705163093268854312677)
                  ·
                    refine ⟨1386319718079987910183627, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7393705163093268854312677 1386319718079987910183627)
                    ·
                      rfl

theorem cell23_8099544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 1, 1, 6, 4].length) (baseStart_8099544 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8099544 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8099544 prefixEnd_8099544 := by exact prefixLift 8099544
  have htrace : WordTrace (prefixWord ++ tailWord_8099544) baseStart_8099544 baseEnd_8099544 := by
    simpa [prefixWord, tailWord_8099544, baseEnd_8099544] using wordTrace_append hprefix tailTrace_8099544
  have hstable : (prefixWord ++ tailWord_8099544).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8099544).length < 2 ^ (prefixWord ++ tailWord_8099544).sum := by decide
  have hdescent : baseEnd_8099544 < baseStart_8099544 := by decide
  rcases family_descends (prefixWord ++ tailWord_8099544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8099545 : List Nat := [1, 2, 1, 2, 3, 5, 1, 3, 1, 1, 3]
def baseStart_8099545 : Nat := 118140960795 + 8099545 * 2 ^ 59
def prefixEnd_8099545 : Nat := 4983230072969 + 3 ^ 40 * 8099545 * 2
def baseEnd_8099545 : Nat := 4158959667720618226638377

theorem tailTrace_8099545 : CollatzResearch.WordTrace tailWord_8099545 prefixEnd_8099545 4158959667720618226638377 := by
  unfold tailWord_8099545
  simp only [CollatzResearch.WordTrace]
  refine ⟨295414675441739232001596089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196943116961159488001064059 295414675441739232001596089)
  ·
    refine ⟨221561006581304424001197067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 295414675441739232001596089 221561006581304424001197067)
    ·
      refine ⟨332341509871956636001795601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 221561006581304424001197067 332341509871956636001795601)
      ·
        refine ⟨249256132403967477001346701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 332341509871956636001795601 249256132403967477001346701)
        ·
          refine ⟨93471049651487803875505013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 249256132403967477001346701 93471049651487803875505013)
          ·
            refine ⟨8762910904826981613328595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 93471049651487803875505013 8762910904826981613328595)
            ·
              refine ⟨13144366357240472419992893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8762910904826981613328595 13144366357240472419992893)
              ·
                refine ⟨4929137383965177157497335, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13144366357240472419992893 4929137383965177157497335)
                ·
                  refine ⟨7393706075947765736246003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4929137383965177157497335 7393706075947765736246003)
                  ·
                    refine ⟨11090559113921648604369005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7393706075947765736246003 11090559113921648604369005)
                    ·
                      refine ⟨4158959667720618226638377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11090559113921648604369005 4158959667720618226638377)
                      ·
                        rfl

theorem cell23_8099545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 5, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 5, 1, 3, 1, 1, 3].length) (baseStart_8099545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8099545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8099545 prefixEnd_8099545 := by exact prefixLift 8099545
  have htrace : WordTrace (prefixWord ++ tailWord_8099545) baseStart_8099545 baseEnd_8099545 := by
    simpa [prefixWord, tailWord_8099545, baseEnd_8099545] using wordTrace_append hprefix tailTrace_8099545
  have hstable : (prefixWord ++ tailWord_8099545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8099545).length < 2 ^ (prefixWord ++ tailWord_8099545).sum := by decide
  have hdescent : baseEnd_8099545 < baseStart_8099545 := by decide
  rcases family_descends (prefixWord ++ tailWord_8099545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8099574 : List Nat := [5, 1, 1, 1, 1, 3, 1, 10]
def baseStart_8099574 : Nat := 118140960795 + 8099574 * 2 ^ 59
def prefixEnd_8099574 : Nat := 4983230072969 + 3 ^ 40 * 8099574 * 2
def baseEnd_8099574 : Nat := 154036094765170319006509

theorem tailTrace_8099574 : CollatzResearch.WordTrace tailWord_8099574 prefixEnd_8099574 154036094765170319006509 := by
  unfold tailWord_8099574
  simp only [CollatzResearch.WordTrace]
  refine ⟨18463483322414635622150111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 196943822105756113302934517 18463483322414635622150111)
  ·
    refine ⟨27695224983621953433225167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18463483322414635622150111 27695224983621953433225167)
    ·
      refine ⟨41542837475432930149837751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27695224983621953433225167 41542837475432930149837751)
      ·
        refine ⟨62314256213149395224756627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41542837475432930149837751 62314256213149395224756627)
        ·
          refine ⟨93471384319724092837134941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62314256213149395224756627 93471384319724092837134941)
          ·
            refine ⟨35051769119896534813925603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 93471384319724092837134941 35051769119896534813925603)
            ·
              refine ⟨52577653679844802220888405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35051769119896534813925603 52577653679844802220888405)
              ·
                refine ⟨154036094765170319006509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 52577653679844802220888405 154036094765170319006509)
                ·
                  rfl

theorem cell23_8099574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 1, 10].length) (baseStart_8099574 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8099574 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8099574 prefixEnd_8099574 := by exact prefixLift 8099574
  have htrace : WordTrace (prefixWord ++ tailWord_8099574) baseStart_8099574 baseEnd_8099574 := by
    simpa [prefixWord, tailWord_8099574, baseEnd_8099574] using wordTrace_append hprefix tailTrace_8099574
  have hstable : (prefixWord ++ tailWord_8099574).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8099574).length < 2 ^ (prefixWord ++ tailWord_8099574).sum := by decide
  have hdescent : baseEnd_8099574 < baseStart_8099574 := by decide
  rcases family_descends (prefixWord ++ tailWord_8099574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8099588 : List Nat := [2, 3, 2, 2, 1, 2, 3, 2, 1, 2, 3]
def baseStart_8099588 : Nat := 118140960795 + 8099588 * 2 ^ 59
def prefixEnd_8099588 : Nat := 4983230072969 + 3 ^ 40 * 8099588 * 2
def baseEnd_8099588 : Nat := 4158981747388761558400679

theorem tailTrace_8099588 : CollatzResearch.WordTrace tailWord_8099588 prefixEnd_8099588 4158981747388761558400679 := by
  unfold tailWord_8099588
  simp only [CollatzResearch.WordTrace]
  refine ⟨147708121890291725172705709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196944162520388966896940945 147708121890291725172705709)
  ·
    refine ⟨55390545708859396939764641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 147708121890291725172705709 55390545708859396939764641)
    ·
      refine ⟨41542909281644547704823481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55390545708859396939764641 41542909281644547704823481)
      ·
        refine ⟨31157181961233410778617611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41542909281644547704823481 31157181961233410778617611)
        ·
          refine ⟨46735772941850116167926417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31157181961233410778617611 46735772941850116167926417)
          ·
            refine ⟨35051829706387587125944813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46735772941850116167926417 35051829706387587125944813)
            ·
              refine ⟨13144436139895345172229305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35051829706387587125944813 13144436139895345172229305)
              ·
                refine ⟨9858327104921508879171979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13144436139895345172229305 9858327104921508879171979)
                ·
                  refine ⟨14787490657382263318757969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9858327104921508879171979 14787490657382263318757969)
                  ·
                    refine ⟨11090617993036697489068477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14787490657382263318757969 11090617993036697489068477)
                    ·
                      refine ⟨4158981747388761558400679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11090617993036697489068477 4158981747388761558400679)
                      ·
                        rfl

theorem cell23_8099588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 3, 2, 1, 2, 3].length) (baseStart_8099588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8099588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8099588 prefixEnd_8099588 := by exact prefixLift 8099588
  have htrace : WordTrace (prefixWord ++ tailWord_8099588) baseStart_8099588 baseEnd_8099588 := by
    simpa [prefixWord, tailWord_8099588, baseEnd_8099588] using wordTrace_append hprefix tailTrace_8099588
  have hstable : (prefixWord ++ tailWord_8099588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8099588).length < 2 ^ (prefixWord ++ tailWord_8099588).sum := by decide
  have hdescent : baseEnd_8099588 < baseStart_8099588 := by decide
  rcases family_descends (prefixWord ++ tailWord_8099588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8099634 : List Nat := [3, 2, 1, 1, 3, 2, 1, 1, 1, 8]
def baseStart_8099634 : Nat := 118140960795 + 8099634 * 2 ^ 59
def prefixEnd_8099634 : Nat := 4983230072969 + 3 ^ 40 * 8099634 * 2
def baseEnd_8099634 : Nat := 1386335122499622792808489

theorem tailTrace_8099634 : CollatzResearch.WordTrace tailWord_8099634 prefixEnd_8099634 1386335122499622792808489 := by
  unfold tailWord_8099634
  simp only [CollatzResearch.WordTrace]
  refine ⟨73854480384604200050396489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 196945281025611200134390637 73854480384604200050396489)
  ·
    refine ⟨55390860288453150037797367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73854480384604200050396489 55390860288453150037797367)
    ·
      refine ⟨83086290432679725056696051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55390860288453150037797367 83086290432679725056696051)
      ·
        refine ⟨124629435649019587585044077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83086290432679725056696051 124629435649019587585044077)
        ·
          refine ⟨46736038368382345344391529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 124629435649019587585044077 46736038368382345344391529)
          ·
            refine ⟨35052028776286759008293647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46736038368382345344391529 35052028776286759008293647)
            ·
              refine ⟨52578043164430138512440471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35052028776286759008293647 52578043164430138512440471)
              ·
                refine ⟨78867064746645207768660707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52578043164430138512440471 78867064746645207768660707)
                ·
                  refine ⟨118300597119967811652991061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 78867064746645207768660707 118300597119967811652991061)
                  ·
                    refine ⟨1386335122499622792808489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 118300597119967811652991061 1386335122499622792808489)
                    ·
                      rfl

theorem cell23_8099634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 1, 1, 1, 8].length) (baseStart_8099634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8099634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8099634 prefixEnd_8099634 := by exact prefixLift 8099634
  have htrace : WordTrace (prefixWord ++ tailWord_8099634) baseStart_8099634 baseEnd_8099634 := by
    simpa [prefixWord, tailWord_8099634, baseEnd_8099634] using wordTrace_append hprefix tailTrace_8099634
  have hstable : (prefixWord ++ tailWord_8099634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8099634).length < 2 ^ (prefixWord ++ tailWord_8099634).sum := by decide
  have hdescent : baseEnd_8099634 < baseStart_8099634 := by decide
  rcases family_descends (prefixWord ++ tailWord_8099634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8099644 : List Nat := [2, 2, 2, 2, 1, 1, 2, 1, 4, 1, 5]
def baseStart_8099644 : Nat := 118140960795 + 8099644 * 2 ^ 59
def prefixEnd_8099644 : Nat := 4983230072969 + 3 ^ 40 * 8099644 * 2
def baseEnd_8099644 : Nat := 4159010502305413339300421

theorem tailTrace_8099644 : CollatzResearch.WordTrace tailWord_8099644 prefixEnd_8099644 4159010502305413339300421 := by
  unfold tailWord_8099644
  simp only [CollatzResearch.WordTrace]
  refine ⟨147709143134190285954724993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196945524178920381272966657 147709143134190285954724993)
  ·
    refine ⟨110781857350642714466043745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147709143134190285954724993 110781857350642714466043745)
    ·
      refine ⟨83086393012982035849532809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110781857350642714466043745 83086393012982035849532809)
      ·
        refine ⟨62314794759736526887149607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83086393012982035849532809 62314794759736526887149607)
        ·
          refine ⟨93472192139604790330724411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62314794759736526887149607 93472192139604790330724411)
          ·
            refine ⟨140208288209407185496086617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93472192139604790330724411 140208288209407185496086617)
            ·
              refine ⟨105156216157055389122064963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 140208288209407185496086617 105156216157055389122064963)
              ·
                refine ⟨157734324235583083683097445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 105156216157055389122064963 157734324235583083683097445)
                ·
                  refine ⟨29575185794171828190580771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 157734324235583083683097445 29575185794171828190580771)
                  ·
                    refine ⟨44362778691257742285871157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29575185794171828190580771 44362778691257742285871157)
                    ·
                      refine ⟨4159010502305413339300421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44362778691257742285871157 4159010502305413339300421)
                      ·
                        rfl

theorem cell23_8099644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 2, 1, 4, 1, 5].length) (baseStart_8099644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8099644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8099644 prefixEnd_8099644 := by exact prefixLift 8099644
  have htrace : WordTrace (prefixWord ++ tailWord_8099644) baseStart_8099644 baseEnd_8099644 := by
    simpa [prefixWord, tailWord_8099644, baseEnd_8099644] using wordTrace_append hprefix tailTrace_8099644
  have hstable : (prefixWord ++ tailWord_8099644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8099644).length < 2 ^ (prefixWord ++ tailWord_8099644).sum := by decide
  have hdescent : baseEnd_8099644 < baseStart_8099644 := by decide
  rcases family_descends (prefixWord ++ tailWord_8099644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8099658 : List Nat := [3, 1, 2, 1, 1, 1, 4, 2, 4, 2, 2]
def baseStart_8099658 : Nat := 118140960795 + 8099658 * 2 ^ 59
def prefixEnd_8099658 : Nat := 4983230072969 + 3 ^ 40 * 8099658 * 2
def baseEnd_8099658 : Nat := 4159017691034576284525357

theorem tailTrace_8099658 : CollatzResearch.WordTrace tailWord_8099658 prefixEnd_8099658 4159017691034576284525357 := by
  unfold tailWord_8099658
  simp only [CollatzResearch.WordTrace]
  refine ⟨73854699222582463075114907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 196945864593553234866973085 73854699222582463075114907)
  ·
    refine ⟨110782048833873694612672361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73854699222582463075114907 110782048833873694612672361)
    ·
      refine ⟨83086536625405270959504271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110782048833873694612672361 83086536625405270959504271)
      ·
        refine ⟨124629804938107906439256407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83086536625405270959504271 124629804938107906439256407)
        ·
          refine ⟨186944707407161859658884611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124629804938107906439256407 186944707407161859658884611)
          ·
            refine ⟨280417061110742789488326917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 186944707407161859658884611 280417061110742789488326917)
            ·
              refine ⟨52578198958264273029061297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 280417061110742789488326917 52578198958264273029061297)
              ·
                refine ⟨39433649218698204771795973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52578198958264273029061297 39433649218698204771795973)
                ·
                  refine ⟨7393809228505913394711745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39433649218698204771795973 7393809228505913394711745)
                  ·
                    refine ⟨5545356921379435046033809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7393809228505913394711745 5545356921379435046033809)
                    ·
                      refine ⟨4159017691034576284525357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5545356921379435046033809 4159017691034576284525357)
                      ·
                        rfl

theorem cell23_8099658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 4, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 4, 2, 4, 2, 2].length) (baseStart_8099658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8099658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8099658 prefixEnd_8099658 := by exact prefixLift 8099658
  have htrace : WordTrace (prefixWord ++ tailWord_8099658) baseStart_8099658 baseEnd_8099658 := by
    simpa [prefixWord, tailWord_8099658, baseEnd_8099658] using wordTrace_append hprefix tailTrace_8099658
  have hstable : (prefixWord ++ tailWord_8099658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8099658).length < 2 ^ (prefixWord ++ tailWord_8099658).sum := by decide
  have hdescent : baseEnd_8099658 < baseStart_8099658 := by decide
  rcases family_descends (prefixWord ++ tailWord_8099658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8099681 : List Nat := [1, 2, 3, 1, 1, 1, 3, 6, 5]
def baseStart_8099681 : Nat := 118140960795 + 8099681 * 2 ^ 59
def prefixEnd_8099681 : Nat := 4983230072969 + 3 ^ 40 * 8099681 * 2
def baseEnd_8099681 : Nat := 462114389009958854948639

theorem tailTrace_8099681 : CollatzResearch.WordTrace tailWord_8099681 prefixEnd_8099681 462114389009958854948639 := by
  unfold tailWord_8099681
  simp only [CollatzResearch.WordTrace]
  refine ⟨295419635769246527228546897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196946423846164351485697931 295419635769246527228546897)
  ·
    refine ⟨221564726826934895421410173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 295419635769246527228546897 221564726826934895421410173)
    ·
      refine ⟨83086772560100585783028815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 221564726826934895421410173 83086772560100585783028815)
      ·
        refine ⟨124630158840150878674543223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83086772560100585783028815 124630158840150878674543223)
        ·
          refine ⟨186945238260226318011814835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124630158840150878674543223 186945238260226318011814835)
          ·
            refine ⟨280417857390339477017722253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 186945238260226318011814835 280417857390339477017722253)
            ·
              refine ⟨105156696521377303881645845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 280417857390339477017722253 105156696521377303881645845)
              ·
                refine ⟨4929220149439561119452149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 105156696521377303881645845 4929220149439561119452149)
                ·
                  refine ⟨462114389009958854948639, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4929220149439561119452149 462114389009958854948639)
                  ·
                    rfl

theorem cell23_8099681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 3, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 3, 6, 5].length) (baseStart_8099681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8099681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8099681 prefixEnd_8099681 := by exact prefixLift 8099681
  have htrace : WordTrace (prefixWord ++ tailWord_8099681) baseStart_8099681 baseEnd_8099681 := by
    simpa [prefixWord, tailWord_8099681, baseEnd_8099681] using wordTrace_append hprefix tailTrace_8099681
  have hstable : (prefixWord ++ tailWord_8099681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8099681).length < 2 ^ (prefixWord ++ tailWord_8099681).sum := by decide
  have hdescent : baseEnd_8099681 < baseStart_8099681 := by decide
  rcases family_descends (prefixWord ++ tailWord_8099681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8099692 : List Nat := [2, 2, 1, 1, 4, 3, 3, 1, 2, 2, 2]
def baseStart_8099692 : Nat := 118140960795 + 8099692 * 2 ^ 59
def prefixEnd_8099692 : Nat := 4983230072969 + 3 ^ 40 * 8099692 * 2
def baseEnd_8099692 : Nat := 4159035149376829151500201

theorem tailTrace_8099692 : CollatzResearch.WordTrace tailWord_8099692 prefixEnd_8099692 4159035149376829151500201 := by
  unfold tailWord_8099692
  simp only [CollatzResearch.WordTrace]
  refine ⟨147710018486103338053598665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196946691314804450738131553 147710018486103338053598665)
  ·
    refine ⟨110782513864577503540198999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147710018486103338053598665 110782513864577503540198999)
    ·
      refine ⟨166173770796866255310298499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110782513864577503540198999 166173770796866255310298499)
      ·
        refine ⟨249260656195299382965447749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166173770796866255310298499 249260656195299382965447749)
        ·
          refine ⟨46736373036618634306021453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 249260656195299382965447749 46736373036618634306021453)
          ·
            refine ⟨17526139888731987864758045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46736373036618634306021453 17526139888731987864758045)
            ·
              refine ⟨6572302458274495449284267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17526139888731987864758045 6572302458274495449284267)
              ·
                refine ⟨9858453687411743173926401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6572302458274495449284267 9858453687411743173926401)
                ·
                  refine ⟨7393840265558807380444801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9858453687411743173926401 7393840265558807380444801)
                  ·
                    refine ⟨5545380199169105535333601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7393840265558807380444801 5545380199169105535333601)
                    ·
                      refine ⟨4159035149376829151500201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5545380199169105535333601 4159035149376829151500201)
                      ·
                        rfl

theorem cell23_8099692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 2, 2, 2].length) (baseStart_8099692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8099692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8099692 prefixEnd_8099692 := by exact prefixLift 8099692
  have htrace : WordTrace (prefixWord ++ tailWord_8099692) baseStart_8099692 baseEnd_8099692 := by
    simpa [prefixWord, tailWord_8099692, baseEnd_8099692] using wordTrace_append hprefix tailTrace_8099692
  have hstable : (prefixWord ++ tailWord_8099692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8099692).length < 2 ^ (prefixWord ++ tailWord_8099692).sum := by decide
  have hdescent : baseEnd_8099692 < baseStart_8099692 := by decide
  rcases family_descends (prefixWord ++ tailWord_8099692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8099768 : List Nat := [2, 1, 2, 1, 2, 3, 4, 1, 2, 2, 3]
def baseStart_8099768 : Nat := 118140960795 + 8099768 * 2 ^ 59
def prefixEnd_8099768 : Nat := 4983230072969 + 3 ^ 40 * 8099768 * 2
def baseEnd_8099768 : Nat := 4159074173906570854149851

theorem tailTrace_8099768 : CollatzResearch.WordTrace tailWord_8099768 prefixEnd_8099768 4159074173906570854149851 := by
  unfold tailWord_8099768
  simp only [CollatzResearch.WordTrace]
  refine ⟨147711404459965670543481979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196948539279954227391309305 147711404459965670543481979)
  ·
    refine ⟨221567106689948505815222969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147711404459965670543481979 221567106689948505815222969)
    ·
      refine ⟨166175330017461379361417227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 221567106689948505815222969 166175330017461379361417227)
      ·
        refine ⟨249262995026192069042125841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166175330017461379361417227 249262995026192069042125841)
        ·
          refine ⟨186947246269644051781594381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 249262995026192069042125841 186947246269644051781594381)
          ·
            refine ⟨70105217351116519418097893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 186947246269644051781594381 70105217351116519418097893)
            ·
              refine ⟨13144728253334347390893355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 70105217351116519418097893 13144728253334347390893355)
              ·
                refine ⟨19717092380001521086340033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13144728253334347390893355 19717092380001521086340033)
                ·
                  refine ⟨14787819285001140814755025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19717092380001521086340033 14787819285001140814755025)
                  ·
                    refine ⟨11090864463750855611066269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14787819285001140814755025 11090864463750855611066269)
                    ·
                      refine ⟨4159074173906570854149851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11090864463750855611066269 4159074173906570854149851)
                      ·
                        rfl

theorem cell23_8099768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 4, 1, 2, 2, 3].length) (baseStart_8099768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8099768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8099768 prefixEnd_8099768 := by exact prefixLift 8099768
  have htrace : WordTrace (prefixWord ++ tailWord_8099768) baseStart_8099768 baseEnd_8099768 := by
    simpa [prefixWord, tailWord_8099768, baseEnd_8099768] using wordTrace_append hprefix tailTrace_8099768
  have hstable : (prefixWord ++ tailWord_8099768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8099768).length < 2 ^ (prefixWord ++ tailWord_8099768).sum := by decide
  have hdescent : baseEnd_8099768 < baseStart_8099768 := by decide
  rcases family_descends (prefixWord ++ tailWord_8099768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8099788 : List Nat := [2, 2, 1, 4, 1, 3, 2, 2, 6]
def baseStart_8099788 : Nat := 118140960795 + 8099788 * 2 ^ 59
def prefixEnd_8099788 : Nat := 4983230072969 + 3 ^ 40 * 8099788 * 2
def baseEnd_8099788 : Nat := 462120493724406752877751

theorem tailTrace_8099788 : CollatzResearch.WordTrace tailWord_8099788 prefixEnd_8099788 462120493724406752877751 := by
  unfold tailWord_8099788
  simp only [CollatzResearch.WordTrace]
  refine ⟨147711769189929442251346009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196949025586572589668461345 147711769189929442251346009)
  ·
    refine ⟨110783826892447081688509507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147711769189929442251346009 110783826892447081688509507)
    ·
      refine ⟨166175740338670622532764261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110783826892447081688509507 166175740338670622532764261)
      ·
        refine ⟨31157951313500741724893299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 166175740338670622532764261 31157951313500741724893299)
        ·
          refine ⟨46736926970251112587339949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31157951313500741724893299 46736926970251112587339949)
          ·
            refine ⟨17526347613844167220252481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46736926970251112587339949 17526347613844167220252481)
            ·
              refine ⟨13144760710383125415189361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17526347613844167220252481 13144760710383125415189361)
              ·
                refine ⟨9858570532787344061392021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13144760710383125415189361 9858570532787344061392021)
                ·
                  refine ⟨462120493724406752877751, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9858570532787344061392021 462120493724406752877751)
                  ·
                    rfl

theorem cell23_8099788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 3, 2, 2, 6].length) (baseStart_8099788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8099788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8099788 prefixEnd_8099788 := by exact prefixLift 8099788
  have htrace : WordTrace (prefixWord ++ tailWord_8099788) baseStart_8099788 baseEnd_8099788 := by
    simpa [prefixWord, tailWord_8099788, baseEnd_8099788] using wordTrace_append hprefix tailTrace_8099788
  have hstable : (prefixWord ++ tailWord_8099788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8099788).length < 2 ^ (prefixWord ++ tailWord_8099788).sum := by decide
  have hdescent : baseEnd_8099788 < baseStart_8099788 := by decide
  rcases family_descends (prefixWord ++ tailWord_8099788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8099808 : List Nat := [2, 1, 1, 3, 1, 1, 1, 4, 4, 3, 2]
def baseStart_8099808 : Nat := 118140960795 + 8099808 * 2 ^ 59
def prefixEnd_8099808 : Nat := 4983230072969 + 3 ^ 40 * 8099808 * 2
def baseEnd_8099808 : Nat := 4159094713132750697649667

theorem tailTrace_8099808 : CollatzResearch.WordTrace tailWord_8099808 prefixEnd_8099808 4159094713132750697649667 := by
  unfold tailWord_8099808
  simp only [CollatzResearch.WordTrace]
  refine ⟨147712133919893213959210039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196949511893190951945613385 147712133919893213959210039)
  ·
    refine ⟨221568200879839820938815059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147712133919893213959210039 221568200879839820938815059)
    ·
      refine ⟨332352301319759731408222589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 221568200879839820938815059 332352301319759731408222589)
      ·
        refine ⟨124632112994909899278083471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 332352301319759731408222589 124632112994909899278083471)
        ·
          refine ⟨186948169492364848917125207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124632112994909899278083471 186948169492364848917125207)
          ·
            refine ⟨280422254238547273375687811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 186948169492364848917125207 280422254238547273375687811)
            ·
              refine ⟨420633381357820910063531717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 280422254238547273375687811 420633381357820910063531717)
              ·
                refine ⟨78868759004591420636912197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 420633381357820910063531717 78868759004591420636912197)
                ·
                  refine ⟨14787892313360891369421037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 78868759004591420636912197 14787892313360891369421037)
                  ·
                    refine ⟨5545459617510334263532889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14787892313360891369421037 5545459617510334263532889)
                    ·
                      refine ⟨4159094713132750697649667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5545459617510334263532889 4159094713132750697649667)
                      ·
                        rfl

theorem cell23_8099808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 4, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 4, 4, 3, 2].length) (baseStart_8099808 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8099808 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8099808 prefixEnd_8099808 := by exact prefixLift 8099808
  have htrace : WordTrace (prefixWord ++ tailWord_8099808) baseStart_8099808 baseEnd_8099808 := by
    simpa [prefixWord, tailWord_8099808, baseEnd_8099808] using wordTrace_append hprefix tailTrace_8099808
  have hstable : (prefixWord ++ tailWord_8099808).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8099808).length < 2 ^ (prefixWord ++ tailWord_8099808).sum := by decide
  have hdescent : baseEnd_8099808 < baseStart_8099808 := by decide
  rcases family_descends (prefixWord ++ tailWord_8099808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8099818 : List Nat := [3, 1, 3, 1, 2, 1, 2, 4, 1, 5]
def baseStart_8099818 : Nat := 118140960795 + 8099818 * 2 ^ 59
def prefixEnd_8099818 : Nat := 4983230072969 + 3 ^ 40 * 8099818 * 2
def baseEnd_8099818 : Nat := 1386366615979765219508207

theorem tailTrace_8099818 : CollatzResearch.WordTrace tailWord_8099818 prefixEnd_8099818 1386366615979765219508207 := by
  unfold tailWord_8099818
  simp only [CollatzResearch.WordTrace]
  refine ⟨73856158142437549906571027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 196949755046500133084189405 73856158142437549906571027)
  ·
    refine ⟨110784237213656324859856541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73856158142437549906571027 110784237213656324859856541)
    ·
      refine ⟨41544088955121121822446203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 110784237213656324859856541 41544088955121121822446203)
      ·
        refine ⟨62316133432681682733669305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41544088955121121822446203 62316133432681682733669305)
        ·
          refine ⟨46737100074511262050251979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62316133432681682733669305 46737100074511262050251979)
          ·
            refine ⟨70105650111766893075377969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46737100074511262050251979 70105650111766893075377969)
            ·
              refine ⟨52579237583825169806533477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70105650111766893075377969 52579237583825169806533477)
              ·
                refine ⟨9858607046967219338725027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 52579237583825169806533477 9858607046967219338725027)
                ·
                  refine ⟨14787910570450829008087541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9858607046967219338725027 14787910570450829008087541)
                  ·
                    refine ⟨1386366615979765219508207, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14787910570450829008087541 1386366615979765219508207)
                    ·
                      rfl

theorem cell23_8099818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 2, 4, 1, 5].length) (baseStart_8099818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8099818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8099818 prefixEnd_8099818 := by exact prefixLift 8099818
  have htrace : WordTrace (prefixWord ++ tailWord_8099818) baseStart_8099818 baseEnd_8099818 := by
    simpa [prefixWord, tailWord_8099818, baseEnd_8099818] using wordTrace_append hprefix tailTrace_8099818
  have hstable : (prefixWord ++ tailWord_8099818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8099818).length < 2 ^ (prefixWord ++ tailWord_8099818).sum := by decide
  have hdescent : baseEnd_8099818 < baseStart_8099818 := by decide
  rcases family_descends (prefixWord ++ tailWord_8099818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8099825 : List Nat := [1, 2, 2, 2, 5, 1, 1, 1, 1, 5, 2]
def baseStart_8099825 : Nat := 118140960795 + 8099825 * 2 ^ 59
def prefixEnd_8099825 : Nat := 4983230072969 + 3 ^ 40 * 8099825 * 2
def baseEnd_8099825 : Nat := 4159103442303877131137089

theorem tailTrace_8099825 : CollatzResearch.WordTrace tailWord_8099825 prefixEnd_8099825 4159103442303877131137089 := by
  unfold tailWord_8099825
  simp only [CollatzResearch.WordTrace]
  refine ⟨295424887880724839821788929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196949925253816559881192619 295424887880724839821788929)
  ·
    refine ⟨221568665910543629866341697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 295424887880724839821788929 221568665910543629866341697)
    ·
      refine ⟨166176499432907722399756273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 221568665910543629866341697 166176499432907722399756273)
      ·
        refine ⟨124632374574680791799817205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 166176499432907722399756273 124632374574680791799817205)
        ·
          refine ⟨11684285116376324231232863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 124632374574680791799817205 11684285116376324231232863)
          ·
            refine ⟨17526427674564486346849295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11684285116376324231232863 17526427674564486346849295)
            ·
              refine ⟨26289641511846729520273943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17526427674564486346849295 26289641511846729520273943)
              ·
                refine ⟨39434462267770094280410915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26289641511846729520273943 39434462267770094280410915)
                ·
                  refine ⟨59151693401655141420616373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39434462267770094280410915 59151693401655141420616373)
                  ·
                    refine ⟨5545471256405169508182785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 59151693401655141420616373 5545471256405169508182785)
                    ·
                      refine ⟨4159103442303877131137089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5545471256405169508182785 4159103442303877131137089)
                      ·
                        rfl

theorem cell23_8099825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 1, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 1, 1, 1, 1, 5, 2].length) (baseStart_8099825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8099825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8099825 prefixEnd_8099825 := by exact prefixLift 8099825
  have htrace : WordTrace (prefixWord ++ tailWord_8099825) baseStart_8099825 baseEnd_8099825 := by
    simpa [prefixWord, tailWord_8099825, baseEnd_8099825] using wordTrace_append hprefix tailTrace_8099825
  have hstable : (prefixWord ++ tailWord_8099825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8099825).length < 2 ^ (prefixWord ++ tailWord_8099825).sum := by decide
  have hdescent : baseEnd_8099825 < baseStart_8099825 := by decide
  rcases family_descends (prefixWord ++ tailWord_8099825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8099848 : List Nat := [2, 1, 3, 2, 1, 2, 3, 1, 4, 4]
def baseStart_8099848 : Nat := 118140960795 + 8099848 * 2 ^ 59
def prefixEnd_8099848 : Nat := 4983230072969 + 3 ^ 40 * 8099848 * 2
def baseEnd_8099848 : Nat := 1386371750786310180383161

theorem tailTrace_8099848 : CollatzResearch.WordTrace tailWord_8099848 prefixEnd_8099848 1386371750786310180383161 := by
  unfold tailWord_8099848
  simp only [CollatzResearch.WordTrace]
  refine ⟨147712863379820757374938099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196950484506427676499917465 147712863379820757374938099)
  ·
    refine ⟨221569295069731136062407149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147712863379820757374938099 221569295069731136062407149)
    ·
      refine ⟨83088485651149176023402681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 221569295069731136062407149 83088485651149176023402681)
      ·
        refine ⟨62316364238361882017552011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83088485651149176023402681 62316364238361882017552011)
        ·
          refine ⟨93474546357542823026328017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62316364238361882017552011 93474546357542823026328017)
          ·
            refine ⟨70105909768157117269746013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 93474546357542823026328017 70105909768157117269746013)
            ·
              refine ⟨26289716163058918976154755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 70105909768157117269746013 26289716163058918976154755)
              ·
                refine ⟨39434574244588378464232133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26289716163058918976154755 39434574244588378464232133)
                ·
                  refine ⟨7393982670860320962043525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39434574244588378464232133 7393982670860320962043525)
                  ·
                    refine ⟨1386371750786310180383161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7393982670860320962043525 1386371750786310180383161)
                    ·
                      rfl

theorem cell23_8099848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 3, 1, 4, 4].length) (baseStart_8099848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8099848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8099848 prefixEnd_8099848 := by exact prefixLift 8099848
  have htrace : WordTrace (prefixWord ++ tailWord_8099848) baseStart_8099848 baseEnd_8099848 := by
    simpa [prefixWord, tailWord_8099848, baseEnd_8099848] using wordTrace_append hprefix tailTrace_8099848
  have hstable : (prefixWord ++ tailWord_8099848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8099848).length < 2 ^ (prefixWord ++ tailWord_8099848).sum := by decide
  have hdescent : baseEnd_8099848 < baseStart_8099848 := by decide
  rcases family_descends (prefixWord ++ tailWord_8099848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8099851 : List Nat := [1, 1, 1, 1, 6, 1, 2, 2, 1, 1, 6]
def baseStart_8099851 : Nat := 118140960795 + 8099851 * 2 ^ 59
def prefixEnd_8099851 : Nat := 4983230072969 + 3 ^ 40 * 8099851 * 2
def baseEnd_8099851 : Nat := 4159116792800894029411969

theorem tailTrace_8099851 : CollatzResearch.WordTrace tailWord_8099851 prefixEnd_8099851 4159116792800894029411969 := by
  unfold tailWord_8099851
  simp only [CollatzResearch.WordTrace]
  refine ⟨295425836178630646262235407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196950557452420430841490271 295425836178630646262235407)
  ·
    refine ⟨443138754267945969393353111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 295425836178630646262235407 443138754267945969393353111)
    ·
      refine ⟨664708131401918954090029667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 443138754267945969393353111 664708131401918954090029667)
      ·
        refine ⟨997062197102878431135044501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 664708131401918954090029667 997062197102878431135044501)
        ·
          refine ⟨46737290489197426459455211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 997062197102878431135044501 46737290489197426459455211)
          ·
            refine ⟨70105935733796139689182817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46737290489197426459455211 70105935733796139689182817)
            ·
              refine ⟨52579451800347104766887113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70105935733796139689182817 52579451800347104766887113)
              ·
                refine ⟨39434588850260328575165335, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52579451800347104766887113 39434588850260328575165335)
                ·
                  refine ⟨59151883275390492862748003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39434588850260328575165335 59151883275390492862748003)
                  ·
                    refine ⟨88727824913085739294122005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 59151883275390492862748003 88727824913085739294122005)
                    ·
                      refine ⟨4159116792800894029411969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 88727824913085739294122005 4159116792800894029411969)
                      ·
                        rfl

theorem cell23_8099851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 2, 2, 1, 1, 6].length) (baseStart_8099851 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8099851 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8099851 prefixEnd_8099851 := by exact prefixLift 8099851
  have htrace : WordTrace (prefixWord ++ tailWord_8099851) baseStart_8099851 baseEnd_8099851 := by
    simpa [prefixWord, tailWord_8099851, baseEnd_8099851] using wordTrace_append hprefix tailTrace_8099851
  have hstable : (prefixWord ++ tailWord_8099851).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8099851).length < 2 ^ (prefixWord ++ tailWord_8099851).sum := by decide
  have hdescent : baseEnd_8099851 < baseStart_8099851 := by decide
  rcases family_descends (prefixWord ++ tailWord_8099851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8099868 : List Nat := [2, 2, 3, 1, 3, 2, 1, 1, 1, 1, 6]
def baseStart_8099868 : Nat := 118140960795 + 8099868 * 2 ^ 59
def prefixEnd_8099868 : Nat := 4983230072969 + 3 ^ 40 * 8099868 * 2
def baseEnd_8099868 : Nat := 4159125521972020462899391

theorem tailTrace_8099868 : CollatzResearch.WordTrace tailWord_8099868 prefixEnd_8099868 4159125521972020462899391 := by
  unfold tailWord_8099868
  simp only [CollatzResearch.WordTrace]
  refine ⟨147713228109784529082802129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196950970813046038777069505 147713228109784529082802129)
  ·
    refine ⟨110784921082338396812101597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147713228109784529082802129 110784921082338396812101597)
    ·
      refine ⟨41544345405876898804538099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 110784921082338396812101597 41544345405876898804538099)
      ·
        refine ⟨62316518108815348206807149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41544345405876898804538099 62316518108815348206807149)
        ·
          refine ⟨23368694290805755577552681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62316518108815348206807149 23368694290805755577552681)
          ·
            refine ⟨17526520718104316683164511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23368694290805755577552681 17526520718104316683164511)
            ·
              refine ⟨26289781077156475024746767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17526520718104316683164511 26289781077156475024746767)
              ·
                refine ⟨39434671615734712537120151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26289781077156475024746767 39434671615734712537120151)
                ·
                  refine ⟨59152007423602068805680227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39434671615734712537120151 59152007423602068805680227)
                  ·
                    refine ⟨88728011135403103208520341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 59152007423602068805680227 88728011135403103208520341)
                    ·
                      refine ⟨4159125521972020462899391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 88728011135403103208520341 4159125521972020462899391)
                      ·
                        rfl

theorem cell23_8099868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 2, 1, 1, 1, 1, 6].length) (baseStart_8099868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8099868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8099868 prefixEnd_8099868 := by exact prefixLift 8099868
  have htrace : WordTrace (prefixWord ++ tailWord_8099868) baseStart_8099868 baseEnd_8099868 := by
    simpa [prefixWord, tailWord_8099868, baseEnd_8099868] using wordTrace_append hprefix tailTrace_8099868
  have hstable : (prefixWord ++ tailWord_8099868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8099868).length < 2 ^ (prefixWord ++ tailWord_8099868).sum := by decide
  have hdescent : baseEnd_8099868 < baseStart_8099868 := by decide
  rcases family_descends (prefixWord ++ tailWord_8099868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8099875 : List Nat := [1, 1, 1, 4, 3, 1, 4, 2, 1, 2, 3]
def baseStart_8099875 : Nat := 118140960795 + 8099875 * 2 ^ 59
def prefixEnd_8099875 : Nat := 4983230072969 + 3 ^ 40 * 8099875 * 2
def baseEnd_8099875 : Nat := 4159129116336601935511859

theorem tailTrace_8099875 : CollatzResearch.WordTrace tailWord_8099875 prefixEnd_8099875 4159129116336601935511859 := by
  unfold tailWord_8099875
  simp only [CollatzResearch.WordTrace]
  refine ⟨295426711530543698361109079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196951141020362465574072719 295426711530543698361109079)
  ·
    refine ⟨443140067295815547541663619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 295426711530543698361109079 443140067295815547541663619)
    ·
      refine ⟨664710100943723321312495429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 443140067295815547541663619 664710100943723321312495429)
      ·
        refine ⟨124633143926948122746092893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 664710100943723321312495429 124633143926948122746092893)
        ·
          refine ⟨46737428972605546029784835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 124633143926948122746092893 46737428972605546029784835)
          ·
            refine ⟨70106143458908319044677253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46737428972605546029784835 70106143458908319044677253)
            ·
              refine ⟨13144901898545309820876985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 70106143458908319044677253 13144901898545309820876985)
              ·
                refine ⟨9858676423908982365657739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13144901898545309820876985 9858676423908982365657739)
                ·
                  refine ⟨14788014635863473548486609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9858676423908982365657739 14788014635863473548486609)
                  ·
                    refine ⟨11091010976897605161364957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14788014635863473548486609 11091010976897605161364957)
                    ·
                      refine ⟨4159129116336601935511859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11091010976897605161364957 4159129116336601935511859)
                      ·
                        rfl

theorem cell23_8099875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 4, 2, 1, 2, 3].length) (baseStart_8099875 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8099875 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8099875 prefixEnd_8099875 := by exact prefixLift 8099875
  have htrace : WordTrace (prefixWord ++ tailWord_8099875) baseStart_8099875 baseEnd_8099875 := by
    simpa [prefixWord, tailWord_8099875, baseEnd_8099875] using wordTrace_append hprefix tailTrace_8099875
  have hstable : (prefixWord ++ tailWord_8099875).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8099875).length < 2 ^ (prefixWord ++ tailWord_8099875).sum := by decide
  have hdescent : baseEnd_8099875 < baseStart_8099875 := by decide
  rcases family_descends (prefixWord ++ tailWord_8099875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8099889 : List Nat := [1, 2, 2, 3, 1, 3, 3, 3, 1, 2, 2]
def baseStart_8099889 : Nat := 118140960795 + 8099889 * 2 ^ 59
def prefixEnd_8099889 : Nat := 4983230072969 + 3 ^ 40 * 8099889 * 2
def baseEnd_8099889 : Nat := 4159136305065764880736795

theorem tailTrace_8099889 : CollatzResearch.WordTrace tailWord_8099889 prefixEnd_8099889 4159136305065764880736795 := by
  unfold tailWord_8099889
  simp only [CollatzResearch.WordTrace]
  refine ⟨295427222152492978752118721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196951481434995319168079147 295427222152492978752118721)
  ·
    refine ⟨221570416614369734064089041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 295427222152492978752118721 221570416614369734064089041)
    ·
      refine ⟨166177812460777300548066781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 221570416614369734064089041 166177812460777300548066781)
      ·
        refine ⟨62316679672791487705525043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 166177812460777300548066781 62316679672791487705525043)
        ·
          refine ⟨93475019509187231558287565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62316679672791487705525043 93475019509187231558287565)
          ·
            refine ⟨35053132315945211834357837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 93475019509187231558287565 35053132315945211834357837)
            ·
              refine ⟨13144924618479454437884189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35053132315945211834357837 13144924618479454437884189)
              ·
                refine ⟨4929346731929795414206571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13144924618479454437884189 4929346731929795414206571)
                ·
                  refine ⟨7394020097894693121309857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4929346731929795414206571 7394020097894693121309857)
                  ·
                    refine ⟨5545515073421019840982393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7394020097894693121309857 5545515073421019840982393)
                    ·
                      refine ⟨4159136305065764880736795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5545515073421019840982393 4159136305065764880736795)
                      ·
                        rfl

theorem cell23_8099889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 3, 3, 1, 2, 2].length) (baseStart_8099889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8099889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8099889 prefixEnd_8099889 := by exact prefixLift 8099889
  have htrace : WordTrace (prefixWord ++ tailWord_8099889) baseStart_8099889 baseEnd_8099889 := by
    simpa [prefixWord, tailWord_8099889, baseEnd_8099889] using wordTrace_append hprefix tailTrace_8099889
  have hstable : (prefixWord ++ tailWord_8099889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8099889).length < 2 ^ (prefixWord ++ tailWord_8099889).sum := by decide
  have hdescent : baseEnd_8099889 < baseStart_8099889 := by decide
  rcases family_descends (prefixWord ++ tailWord_8099889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8099892 : List Nat := [2, 5, 1, 2, 2, 1, 2, 1, 1, 1, 5]
def baseStart_8099892 : Nat := 118140960795 + 8099892 * 2 ^ 59
def prefixEnd_8099892 : Nat := 4983230072969 + 3 ^ 40 * 8099892 * 2
def baseEnd_8099892 : Nat := 4159137845507728368999281

theorem tailTrace_8099892 : CollatzResearch.WordTrace tailWord_8099892 prefixEnd_8099892 4159137845507728368999281 := by
  unfold tailWord_8099892
  simp only [CollatzResearch.WordTrace]
  refine ⟨147713665785741055132238965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196951554380988073509651953 147713665785741055132238965)
  ·
    refine ⟨13848156167413223918647403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 147713665785741055132238965 13848156167413223918647403)
    ·
      refine ⟨20772234251119835877971105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13848156167413223918647403 20772234251119835877971105)
      ·
        refine ⟨15579175688339876908478329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20772234251119835877971105 15579175688339876908478329)
        ·
          refine ⟨11684381766254907681358747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15579175688339876908478329 11684381766254907681358747)
          ·
            refine ⟨17526572649382361522038121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11684381766254907681358747 17526572649382361522038121)
            ·
              refine ⟨13144929487036771141528591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17526572649382361522038121 13144929487036771141528591)
              ·
                refine ⟨19717394230555156712292887, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13144929487036771141528591 19717394230555156712292887)
                ·
                  refine ⟨29576091345832735068439331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19717394230555156712292887 29576091345832735068439331)
                  ·
                    refine ⟨44364137018749102602658997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29576091345832735068439331 44364137018749102602658997)
                    ·
                      refine ⟨4159137845507728368999281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44364137018749102602658997 4159137845507728368999281)
                      ·
                        rfl

theorem cell23_8099892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 1, 2, 1, 1, 1, 5].length) (baseStart_8099892 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8099892 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8099892 prefixEnd_8099892 := by exact prefixLift 8099892
  have htrace : WordTrace (prefixWord ++ tailWord_8099892) baseStart_8099892 baseEnd_8099892 := by
    simpa [prefixWord, tailWord_8099892, baseEnd_8099892] using wordTrace_append hprefix tailTrace_8099892
  have hstable : (prefixWord ++ tailWord_8099892).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8099892).length < 2 ^ (prefixWord ++ tailWord_8099892).sum := by decide
  have hdescent : baseEnd_8099892 < baseStart_8099892 := by decide
  rcases family_descends (prefixWord ++ tailWord_8099892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8099921 : List Nat := [1, 2, 2, 1, 3, 1, 1, 3, 1, 8]
def baseStart_8099921 : Nat := 118140960795 + 8099921 * 2 ^ 59
def prefixEnd_8099921 : Nat := 4983230072969 + 3 ^ 40 * 8099921 * 2
def baseEnd_8099921 : Nat := 1386384245482236251845549

theorem tailTrace_8099921 : CollatzResearch.WordTrace tailWord_8099921 prefixEnd_8099921 1386384245482236251845549 := by
  unfold tailWord_8099921
  simp only [CollatzResearch.WordTrace]
  refine ⟨295428389288377048217283617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196952259525584698811522411 295428389288377048217283617)
  ·
    refine ⟨221571291966282786162962713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 295428389288377048217283617 221571291966282786162962713)
    ·
      refine ⟨166178468974712089622222035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 221571291966282786162962713 166178468974712089622222035)
      ·
        refine ⟨249267703462068134433333053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166178468974712089622222035 249267703462068134433333053)
        ·
          refine ⟨93475388798275550412499895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 249267703462068134433333053 93475388798275550412499895)
          ·
            refine ⟨140213083197413325618749843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93475388798275550412499895 140213083197413325618749843)
            ·
              refine ⟨210319624796119988428124765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 140213083197413325618749843 210319624796119988428124765)
              ·
                refine ⟨78869859298544995660546787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 210319624796119988428124765 78869859298544995660546787)
                ·
                  refine ⟨118304788947817493490820181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 78869859298544995660546787 118304788947817493490820181)
                  ·
                    refine ⟨1386384245482236251845549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 118304788947817493490820181 1386384245482236251845549)
                    ·
                      rfl

theorem cell23_8099921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 3, 1, 8].length) (baseStart_8099921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8099921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8099921 prefixEnd_8099921 := by exact prefixLift 8099921
  have htrace : WordTrace (prefixWord ++ tailWord_8099921) baseStart_8099921 baseEnd_8099921 := by
    simpa [prefixWord, tailWord_8099921, baseEnd_8099921] using wordTrace_append hprefix tailTrace_8099921
  have hstable : (prefixWord ++ tailWord_8099921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8099921).length < 2 ^ (prefixWord ++ tailWord_8099921).sum := by decide
  have hdescent : baseEnd_8099921 < baseStart_8099921 := by decide
  rcases family_descends (prefixWord ++ tailWord_8099921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8099926 : List Nat := [5, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3]
def baseStart_8099926 : Nat := 118140960795 + 8099926 * 2 ^ 59
def prefixEnd_8099926 : Nat := 4983230072969 + 3 ^ 40 * 8099926 * 2
def baseEnd_8099926 : Nat := 4159155303849981235974125

theorem tailTrace_8099926 : CollatzResearch.WordTrace tailWord_8099926 prefixEnd_8099926 4159155303849981235974125 := by
  unfold tailWord_8099926
  simp only [CollatzResearch.WordTrace]
  refine ⟨18464285728334933379450977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 196952381102239289380810421 18464285728334933379450977)
  ·
    refine ⟨13848214296251200034588233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18464285728334933379450977 13848214296251200034588233)
    ·
      refine ⟨10386160722188400025941175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13848214296251200034588233 10386160722188400025941175)
      ·
        refine ⟨15579241083282600038911763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10386160722188400025941175 15579241083282600038911763)
        ·
          refine ⟨23368861624923900058367645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15579241083282600038911763 23368861624923900058367645)
          ·
            refine ⟨8763323109346462521887867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23368861624923900058367645 8763323109346462521887867)
            ·
              refine ⟨13144984664019693782831801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8763323109346462521887867 13144984664019693782831801)
              ·
                refine ⟨9858738498014770337123851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13144984664019693782831801 9858738498014770337123851)
                ·
                  refine ⟨14788107747022155505685777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9858738498014770337123851 14788107747022155505685777)
                  ·
                    refine ⟨11091080810266616629264333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14788107747022155505685777 11091080810266616629264333)
                    ·
                      refine ⟨4159155303849981235974125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11091080810266616629264333 4159155303849981235974125)
                      ·
                        rfl

theorem cell23_8099926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3].length) (baseStart_8099926 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8099926 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8099926 prefixEnd_8099926 := by exact prefixLift 8099926
  have htrace : WordTrace (prefixWord ++ tailWord_8099926) baseStart_8099926 baseEnd_8099926 := by
    simpa [prefixWord, tailWord_8099926, baseEnd_8099926] using wordTrace_append hprefix tailTrace_8099926
  have hstable : (prefixWord ++ tailWord_8099926).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8099926).length < 2 ^ (prefixWord ++ tailWord_8099926).sum := by decide
  have hdescent : baseEnd_8099926 < baseStart_8099926 := by decide
  rcases family_descends (prefixWord ++ tailWord_8099926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8099932 : List Nat := [2, 2, 4, 1, 1, 3, 1, 1, 3, 3, 2]
def baseStart_8099932 : Nat := 118140960795 + 8099932 * 2 ^ 59
def prefixEnd_8099932 : Nat := 4983230072969 + 3 ^ 40 * 8099932 * 2
def baseEnd_8099932 : Nat := 4159158384733908212499097

theorem tailTrace_8099932 : CollatzResearch.WordTrace tailWord_8099932 prefixEnd_8099932 4159158384733908212499097 := by
  unfold tailWord_8099932
  simp only [CollatzResearch.WordTrace]
  refine ⟨147714395245668598547967025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196952526994224798063956033 147714395245668598547967025)
  ·
    refine ⟨110785796434251448910975269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147714395245668598547967025 110785796434251448910975269)
    ·
      refine ⟨20772336831422146670807863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 110785796434251448910975269 20772336831422146670807863)
      ·
        refine ⟨31158505247133220006211795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20772336831422146670807863 31158505247133220006211795)
        ·
          refine ⟨46737757870699830009317693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31158505247133220006211795 46737757870699830009317693)
          ·
            refine ⟨17526659201512436253494135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46737757870699830009317693 17526659201512436253494135)
            ·
              refine ⟨26289988802268654380241203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17526659201512436253494135 26289988802268654380241203)
              ·
                refine ⟨39434983203402981570361805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26289988802268654380241203 39434983203402981570361805)
                ·
                  refine ⟨14788118701276118088885677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39434983203402981570361805 14788118701276118088885677)
                  ·
                    refine ⟨5545544512978544283332129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14788118701276118088885677 5545544512978544283332129)
                    ·
                      refine ⟨4159158384733908212499097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5545544512978544283332129 4159158384733908212499097)
                      ·
                        rfl

theorem cell23_8099932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 3, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 3, 1, 1, 3, 3, 2].length) (baseStart_8099932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8099932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8099932 prefixEnd_8099932 := by exact prefixLift 8099932
  have htrace : WordTrace (prefixWord ++ tailWord_8099932) baseStart_8099932 baseEnd_8099932 := by
    simpa [prefixWord, tailWord_8099932, baseEnd_8099932] using wordTrace_append hprefix tailTrace_8099932
  have hstable : (prefixWord ++ tailWord_8099932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8099932).length < 2 ^ (prefixWord ++ tailWord_8099932).sum := by decide
  have hdescent : baseEnd_8099932 < baseStart_8099932 := by decide
  rcases family_descends (prefixWord ++ tailWord_8099932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8099945 : List Nat := [1, 2, 1, 1, 1, 5, 3, 2, 1, 4, 2]
def baseStart_8099945 : Nat := 118140960795 + 8099945 * 2 ^ 59
def prefixEnd_8099945 : Nat := 4983230072969 + 3 ^ 40 * 8099945 * 2
def baseEnd_8099945 : Nat := 4159165059982416661636537

theorem tailTrace_8099945 : CollatzResearch.WordTrace tailWord_8099945 prefixEnd_8099945 4159165059982416661636537 := by
  unfold tailWord_8099945
  simp only [CollatzResearch.WordTrace]
  refine ⟨295429264640290100316157289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196952843093526733544104859 295429264640290100316157289)
  ·
    refine ⟨221571948480217575237117967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 295429264640290100316157289 221571948480217575237117967)
    ·
      refine ⟨332357922720326362855676951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 221571948480217575237117967 332357922720326362855676951)
      ·
        refine ⟨498536884080489544283515427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 332357922720326362855676951 498536884080489544283515427)
        ·
          refine ⟨747805326120734316425273141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 498536884080489544283515427 747805326120734316425273141)
          ·
            refine ⟨70106749323818842164869357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 747805326120734316425273141 70106749323818842164869357)
            ·
              refine ⟨26290030996432065811826009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 70106749323818842164869357 26290030996432065811826009)
              ·
                refine ⟨19717523247324049358869507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26290030996432065811826009 19717523247324049358869507)
                ·
                  refine ⟨29576284870986074038304261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19717523247324049358869507 29576284870986074038304261)
                  ·
                    refine ⟨5545553413309888882182049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29576284870986074038304261 5545553413309888882182049)
                    ·
                      refine ⟨4159165059982416661636537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5545553413309888882182049 4159165059982416661636537)
                      ·
                        rfl

theorem cell23_8099945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 3, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 3, 2, 1, 4, 2].length) (baseStart_8099945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8099945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8099945 prefixEnd_8099945 := by exact prefixLift 8099945
  have htrace : WordTrace (prefixWord ++ tailWord_8099945) baseStart_8099945 baseEnd_8099945 := by
    simpa [prefixWord, tailWord_8099945, baseEnd_8099945] using wordTrace_append hprefix tailTrace_8099945
  have hstable : (prefixWord ++ tailWord_8099945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8099945).length < 2 ^ (prefixWord ++ tailWord_8099945).sum := by decide
  have hdescent : baseEnd_8099945 < baseStart_8099945 := by decide
  rcases family_descends (prefixWord ++ tailWord_8099945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8099948 : List Nat := [2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 5]
def baseStart_8099948 : Nat := 118140960795 + 8099948 * 2 ^ 59
def prefixEnd_8099948 : Nat := 4983230072969 + 3 ^ 40 * 8099948 * 2
def baseEnd_8099948 : Nat := 4159166600424380149899023

theorem tailTrace_8099948 : CollatzResearch.WordTrace tailWord_8099948 prefixEnd_8099948 4159166600424380149899023 := by
  unfold tailWord_8099948
  simp only [CollatzResearch.WordTrace]
  refine ⟨147714687029639615914258249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196952916039519487885677665 147714687029639615914258249)
  ·
    refine ⟨110786015272229711935693687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147714687029639615914258249 110786015272229711935693687)
    ·
      refine ⟨166179022908344567903540531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110786015272229711935693687 166179022908344567903540531)
      ·
        refine ⟨249268534362516851855310797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166179022908344567903540531 249268534362516851855310797)
        ·
          refine ⟨93475700385943819445741549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 249268534362516851855310797 93475700385943819445741549)
          ·
            refine ⟨35053387644728932292153081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 93475700385943819445741549 35053387644728932292153081)
            ·
              refine ⟨26290040733546699219114811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35053387644728932292153081 26290040733546699219114811)
              ·
                refine ⟨39435061100320048828672217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26290040733546699219114811 39435061100320048828672217)
                ·
                  refine ⟨29576295825240036621504163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39435061100320048828672217 29576295825240036621504163)
                  ·
                    refine ⟨44364443737860054932256245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29576295825240036621504163 44364443737860054932256245)
                    ·
                      refine ⟨4159166600424380149899023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44364443737860054932256245 4159166600424380149899023)
                      ·
                        rfl

theorem cell23_8099948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 5].length) (baseStart_8099948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8099948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8099948 prefixEnd_8099948 := by exact prefixLift 8099948
  have htrace : WordTrace (prefixWord ++ tailWord_8099948) baseStart_8099948 baseEnd_8099948 := by
    simpa [prefixWord, tailWord_8099948, baseEnd_8099948] using wordTrace_append hprefix tailTrace_8099948
  have hstable : (prefixWord ++ tailWord_8099948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8099948).length < 2 ^ (prefixWord ++ tailWord_8099948).sum := by decide
  have hdescent : baseEnd_8099948 < baseStart_8099948 := by decide
  rcases family_descends (prefixWord ++ tailWord_8099948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8099949 : List Nat := [1, 5, 1, 1, 2, 1, 5, 1, 1, 3, 2]
def baseStart_8099949 : Nat := 118140960795 + 8099949 * 2 ^ 59
def prefixEnd_8099949 : Nat := 4983230072969 + 3 ^ 40 * 8099949 * 2
def baseEnd_8099949 : Nat := 4159167113905034645986519

theorem tailTrace_8099949 : CollatzResearch.WordTrace tailWord_8099949 prefixEnd_8099949 4159167113905034645986519 := by
  unfold tailWord_8099949
  simp only [CollatzResearch.WordTrace]
  refine ⟨295429410532275608999302901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196952940354850405999535267 295429410532275608999302901)
  ·
    refine ⟨27696507237400838343684647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 295429410532275608999302901 27696507237400838343684647)
    ·
      refine ⟨41544760856101257515526971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27696507237400838343684647 41544760856101257515526971)
      ·
        refine ⟨62317141284151886273290457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41544760856101257515526971 62317141284151886273290457)
        ·
          refine ⟨46737855963113914704967843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62317141284151886273290457 46737855963113914704967843)
          ·
            refine ⟨70106783944670872057451765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46737855963113914704967843 70106783944670872057451765)
            ·
              refine ⟨6572510994812894255386103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 70106783944670872057451765 6572510994812894255386103)
              ·
                refine ⟨9858766492219341383079155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6572510994812894255386103 9858766492219341383079155)
                ·
                  refine ⟨14788149738329012074618733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9858766492219341383079155 14788149738329012074618733)
                  ·
                    refine ⟨5545556151873379527982025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14788149738329012074618733 5545556151873379527982025)
                    ·
                      refine ⟨4159167113905034645986519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5545556151873379527982025 4159167113905034645986519)
                      ·
                        rfl

theorem cell23_8099949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 5, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 5, 1, 1, 3, 2].length) (baseStart_8099949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8099949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8099949 prefixEnd_8099949 := by exact prefixLift 8099949
  have htrace : WordTrace (prefixWord ++ tailWord_8099949) baseStart_8099949 baseEnd_8099949 := by
    simpa [prefixWord, tailWord_8099949, baseEnd_8099949] using wordTrace_append hprefix tailTrace_8099949
  have hstable : (prefixWord ++ tailWord_8099949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8099949).length < 2 ^ (prefixWord ++ tailWord_8099949).sum := by decide
  have hdescent : baseEnd_8099949 < baseStart_8099949 := by decide
  rcases family_descends (prefixWord ++ tailWord_8099949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8100002 : List Nat := [3, 3, 1, 3, 1, 1, 1, 5, 5]
def baseStart_8100002 : Nat := 118140960795 + 8100002 * 2 ^ 59
def prefixEnd_8100002 : Nat := 4983230072969 + 3 ^ 40 * 8100002 * 2
def baseEnd_8100002 : Nat := 462132703153302548735975

theorem tailTrace_8100002 : CollatzResearch.WordTrace tailWord_8100002 prefixEnd_8100002 462132703153302548735975 := by
  unfold tailWord_8100002
  simp only [CollatzResearch.WordTrace]
  refine ⟨73857835900270899762745565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 196954229067389066033988173 73857835900270899762745565)
  ·
    refine ⟨27696688462601587411029587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73857835900270899762745565 27696688462601587411029587)
    ·
      refine ⟨41545032693902381116544381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27696688462601587411029587 41545032693902381116544381)
      ·
        refine ⟨15579387260213392918704143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41545032693902381116544381 15579387260213392918704143)
        ·
          refine ⟨23369080890320089378056215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15579387260213392918704143 23369080890320089378056215)
          ·
            refine ⟨35053621335480134067084323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23369080890320089378056215 35053621335480134067084323)
            ·
              refine ⟨52580432003220201100626485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35053621335480134067084323 52580432003220201100626485)
              ·
                refine ⟨4929415500301893853183733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 52580432003220201100626485 4929415500301893853183733)
                ·
                  refine ⟨462132703153302548735975, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4929415500301893853183733 462132703153302548735975)
                  ·
                    rfl

theorem cell23_8100002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 1, 5, 5].length) (baseStart_8100002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8100002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8100002 prefixEnd_8100002 := by exact prefixLift 8100002
  have htrace : WordTrace (prefixWord ++ tailWord_8100002) baseStart_8100002 baseEnd_8100002 := by
    simpa [prefixWord, tailWord_8100002, baseEnd_8100002] using wordTrace_append hprefix tailTrace_8100002
  have hstable : (prefixWord ++ tailWord_8100002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8100002).length < 2 ^ (prefixWord ++ tailWord_8100002).sum := by decide
  have hdescent : baseEnd_8100002 < baseStart_8100002 := by decide
  rcases family_descends (prefixWord ++ tailWord_8100002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8100055 : List Nat := [1, 1, 3, 2, 1, 2, 1, 5, 2, 2, 3]
def baseStart_8100055 : Nat := 118140960795 + 8100055 * 2 ^ 59
def prefixEnd_8100055 : Nat := 4983230072969 + 3 ^ 40 * 8100055 * 2
def baseEnd_8100055 : Nat := 4159221542854411231261031

theorem tailTrace_8100055 : CollatzResearch.WordTrace tailWord_8100055 prefixEnd_8100055 4159221542854411231261031 := by
  unfold tailWord_8100055
  simp only [CollatzResearch.WordTrace]
  refine ⟨295433276669891589102661619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196955517779927726068441079 295433276669891589102661619)
  ·
    refine ⟨443149915004837383653992429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 295433276669891589102661619 443149915004837383653992429)
    ·
      refine ⟨166181218126814018870247161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 443149915004837383653992429 166181218126814018870247161)
      ·
        refine ⟨124635913595110514152685371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 166181218126814018870247161 124635913595110514152685371)
        ·
          refine ⟨186953870392665771229028057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124635913595110514152685371 186953870392665771229028057)
          ·
            refine ⟨140215402794499328421771043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 186953870392665771229028057 140215402794499328421771043)
            ·
              refine ⟨210323104191748992632656565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 140215402794499328421771043 210323104191748992632656565)
              ·
                refine ⟨19717791017976468059311553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 210323104191748992632656565 19717791017976468059311553)
                ·
                  refine ⟨14788343263482351044483665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19717791017976468059311553 14788343263482351044483665)
                  ·
                    refine ⟨11091257447611763283362749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14788343263482351044483665 11091257447611763283362749)
                    ·
                      refine ⟨4159221542854411231261031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11091257447611763283362749 4159221542854411231261031)
                      ·
                        rfl

theorem cell23_8100055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 5, 2, 2, 3].length) (baseStart_8100055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8100055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8100055 prefixEnd_8100055 := by exact prefixLift 8100055
  have htrace : WordTrace (prefixWord ++ tailWord_8100055) baseStart_8100055 baseEnd_8100055 := by
    simpa [prefixWord, tailWord_8100055, baseEnd_8100055] using wordTrace_append hprefix tailTrace_8100055
  have hstable : (prefixWord ++ tailWord_8100055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8100055).length < 2 ^ (prefixWord ++ tailWord_8100055).sum := by decide
  have hdescent : baseEnd_8100055 < baseStart_8100055 := by decide
  rcases family_descends (prefixWord ++ tailWord_8100055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8100058 : List Nat := [3, 1, 1, 2, 2, 1, 3, 2, 8]
def baseStart_8100058 : Nat := 118140960795 + 8100058 * 2 ^ 59
def prefixEnd_8100058 : Nat := 4983230072969 + 3 ^ 40 * 8100058 * 2
def baseEnd_8100058 : Nat := 462135898144041635502613

theorem tailTrace_8100058 : CollatzResearch.WordTrace tailWord_8100058 prefixEnd_8100058 462135898144041635502613 := by
  unfold tailWord_8100058
  simp only [CollatzResearch.WordTrace]
  refine ⟨73858346522220180153755207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 196955590725920480410013885 73858346522220180153755207)
  ·
    refine ⟨110787519783330270230632811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73858346522220180153755207 110787519783330270230632811)
    ·
      refine ⟨166181279674995405345949217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110787519783330270230632811 166181279674995405345949217)
      ·
        refine ⟨124635959756246554009461913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 166181279674995405345949217 124635959756246554009461913)
        ·
          refine ⟨93476969817184915507096435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 124635959756246554009461913 93476969817184915507096435)
          ·
            refine ⟨140215454725777373260644653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93476969817184915507096435 140215454725777373260644653)
            ·
              refine ⟨52580795522166514972741745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 140215454725777373260644653 52580795522166514972741745)
              ·
                refine ⟨39435596641624886229556309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52580795522166514972741745 39435596641624886229556309)
                ·
                  refine ⟨462135898144041635502613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 39435596641624886229556309 462135898144041635502613)
                  ·
                    rfl

theorem cell23_8100058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 3, 2, 8].length) (baseStart_8100058 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8100058 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8100058 prefixEnd_8100058 := by exact prefixLift 8100058
  have htrace : WordTrace (prefixWord ++ tailWord_8100058) baseStart_8100058 baseEnd_8100058 := by
    simpa [prefixWord, tailWord_8100058, baseEnd_8100058] using wordTrace_append hprefix tailTrace_8100058
  have hstable : (prefixWord ++ tailWord_8100058).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8100058).length < 2 ^ (prefixWord ++ tailWord_8100058).sum := by decide
  have hdescent : baseEnd_8100058 < baseStart_8100058 := by decide
  rcases family_descends (prefixWord ++ tailWord_8100058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8100066 : List Nat := [3, 3, 4, 1, 1, 1, 1, 2, 2, 5]
def baseStart_8100066 : Nat := 118140960795 + 8100066 * 2 ^ 59
def prefixEnd_8100066 : Nat := 4983230072969 + 3 ^ 40 * 8100066 * 2
def baseEnd_8100066 : Nat := 1386409063713870229407827

theorem tailTrace_8100066 : CollatzResearch.WordTrace tailWord_8100066 prefixEnd_8100066 1386409063713870229407827 := by
  unfold tailWord_8100066
  simp only [CollatzResearch.WordTrace]
  refine ⟨73858419468212934495328013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 196955785248567825320874701 73858419468212934495328013)
  ·
    refine ⟨27696907300579850435748005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73858419468212934495328013 27696907300579850435748005)
    ·
      refine ⟨5193170118858721956702751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 27696907300579850435748005 5193170118858721956702751)
      ·
        refine ⟨7789755178288082935054127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5193170118858721956702751 7789755178288082935054127)
        ·
          refine ⟨11684632767432124402581191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7789755178288082935054127 11684632767432124402581191)
          ·
            refine ⟨17526949151148186603871787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11684632767432124402581191 17526949151148186603871787)
            ·
              refine ⟨26290423726722279905807681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17526949151148186603871787 26290423726722279905807681)
              ·
                refine ⟨19717817795041709929355761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26290423726722279905807681 19717817795041709929355761)
                ·
                  refine ⟨14788363346281282447016821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19717817795041709929355761 14788363346281282447016821)
                  ·
                    refine ⟨1386409063713870229407827, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14788363346281282447016821 1386409063713870229407827)
                    ·
                      rfl

theorem cell23_8100066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 1, 1, 2, 2, 5].length) (baseStart_8100066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8100066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8100066 prefixEnd_8100066 := by exact prefixLift 8100066
  have htrace : WordTrace (prefixWord ++ tailWord_8100066) baseStart_8100066 baseEnd_8100066 := by
    simpa [prefixWord, tailWord_8100066, baseEnd_8100066] using wordTrace_append hprefix tailTrace_8100066
  have hstable : (prefixWord ++ tailWord_8100066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8100066).length < 2 ^ (prefixWord ++ tailWord_8100066).sum := by decide
  have hdescent : baseEnd_8100066 < baseStart_8100066 := by decide
  rcases family_descends (prefixWord ++ tailWord_8100066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8100072 : List Nat := [2, 1, 4, 1, 2, 3, 1, 2, 2, 2, 3]
def baseStart_8100072 : Nat := 118140960795 + 8100072 * 2 ^ 59
def prefixEnd_8100072 : Nat := 4983230072969 + 3 ^ 40 * 8100072 * 2
def baseEnd_8100072 : Nat := 4159230272025537664748453

theorem tailTrace_8100072 : CollatzResearch.WordTrace tailWord_8100072 prefixEnd_8100072 4159230272025537664748453 := by
  unfold tailWord_8100072
  simp only [CollatzResearch.WordTrace]
  refine ⟨147716948355415000503015235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196955931140553334004020313 147716948355415000503015235)
  ·
    refine ⟨221575422533122500754522853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147716948355415000503015235 221575422533122500754522853)
    ·
      refine ⟨41545391724960468891473035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 221575422533122500754522853 41545391724960468891473035)
      ·
        refine ⟨62318087587440703337209553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41545391724960468891473035 62318087587440703337209553)
        ·
          refine ⟨46738565690580527502907165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62318087587440703337209553 46738565690580527502907165)
          ·
            refine ⟨17526962133967697813590187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46738565690580527502907165 17526962133967697813590187)
            ·
              refine ⟨26290443200951546720385281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17526962133967697813590187 26290443200951546720385281)
              ·
                refine ⟨19717832400713660040288961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26290443200951546720385281 19717832400713660040288961)
                ·
                  refine ⟨14788374300535245030216721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19717832400713660040288961 14788374300535245030216721)
                  ·
                    refine ⟨11091280725401433772662541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14788374300535245030216721 11091280725401433772662541)
                    ·
                      refine ⟨4159230272025537664748453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11091280725401433772662541 4159230272025537664748453)
                      ·
                        rfl

theorem cell23_8100072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 3, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 3, 1, 2, 2, 2, 3].length) (baseStart_8100072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8100072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8100072 prefixEnd_8100072 := by exact prefixLift 8100072
  have htrace : WordTrace (prefixWord ++ tailWord_8100072) baseStart_8100072 baseEnd_8100072 := by
    simpa [prefixWord, tailWord_8100072, baseEnd_8100072] using wordTrace_append hprefix tailTrace_8100072
  have hstable : (prefixWord ++ tailWord_8100072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8100072).length < 2 ^ (prefixWord ++ tailWord_8100072).sum := by decide
  have hdescent : baseEnd_8100072 < baseStart_8100072 := by decide
  rcases family_descends (prefixWord ++ tailWord_8100072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8100092 : List Nat := [2, 2, 2, 1, 4, 1, 4, 1, 6]
def baseStart_8100092 : Nat := 118140960795 + 8100092 * 2 ^ 59
def prefixEnd_8100092 : Nat := 4983230072969 + 3 ^ 40 * 8100092 * 2
def baseEnd_8100092 : Nat := 462137837959847509610929

theorem tailTrace_8100092 : CollatzResearch.WordTrace tailWord_8100092 prefixEnd_8100092 462137837959847509610929 := by
  unfold tailWord_8100092
  simp only [CollatzResearch.WordTrace]
  refine ⟨147717313085378772210879265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196956417447171696281172353 147717313085378772210879265)
  ·
    refine ⟨110787984814034079158159449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147717313085378772210879265 110787984814034079158159449)
    ·
      refine ⟨83090988610525559368619587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110787984814034079158159449 83090988610525559368619587)
      ·
        refine ⟨124636482915788339052929381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83090988610525559368619587 124636482915788339052929381)
        ·
          refine ⟨23369340546710313572424259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 124636482915788339052929381 23369340546710313572424259)
          ·
            refine ⟨35054010820065470358636389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23369340546710313572424259 35054010820065470358636389)
            ·
              refine ⟨6572627028762275692244323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35054010820065470358636389 6572627028762275692244323)
              ·
                refine ⟨9858940543143413538366485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6572627028762275692244323 9858940543143413538366485)
                ·
                  refine ⟨462137837959847509610929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9858940543143413538366485 462137837959847509610929)
                  ·
                    rfl

theorem cell23_8100092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 4, 1, 6].length) (baseStart_8100092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8100092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8100092 prefixEnd_8100092 := by exact prefixLift 8100092
  have htrace : WordTrace (prefixWord ++ tailWord_8100092) baseStart_8100092 baseEnd_8100092 := by
    simpa [prefixWord, tailWord_8100092, baseEnd_8100092] using wordTrace_append hprefix tailTrace_8100092
  have hstable : (prefixWord ++ tailWord_8100092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8100092).length < 2 ^ (prefixWord ++ tailWord_8100092).sum := by decide
  have hdescent : baseEnd_8100092 < baseStart_8100092 := by decide
  rcases family_descends (prefixWord ++ tailWord_8100092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8100105 : List Nat := [1, 2, 1, 1, 3, 5, 1, 1, 3, 5]
def baseStart_8100105 : Nat := 118140960795 + 8100105 * 2 ^ 59
def prefixEnd_8100105 : Nat := 4983230072969 + 3 ^ 40 * 8100105 * 2
def baseEnd_8100105 : Nat := 1386415738962378678545267

theorem tailTrace_8100105 : CollatzResearch.WordTrace tailWord_8100105 prefixEnd_8100105 1386415738962378678545267 := by
  unfold tailWord_8100105
  simp only [CollatzResearch.WordTrace]
  refine ⟨295435100319710447641981769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196956733546473631761321179 295435100319710447641981769)
  ·
    refine ⟨221576325239782835731486327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 295435100319710447641981769 221576325239782835731486327)
    ·
      refine ⟨332364487859674253597229491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 221576325239782835731486327 332364487859674253597229491)
      ·
        refine ⟨498546731789511380395844237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 332364487859674253597229491 498546731789511380395844237)
        ·
          refine ⟨186955024421066767648441589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 498546731789511380395844237 186955024421066767648441589)
          ·
            refine ⟨17527033539475009467041399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 186955024421066767648441589 17527033539475009467041399)
            ·
              refine ⟨26290550309212514200562099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17527033539475009467041399 26290550309212514200562099)
              ·
                refine ⟨39435825463818771300843149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26290550309212514200562099 39435825463818771300843149)
                ·
                  refine ⟨14788434548932039237816181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39435825463818771300843149 14788434548932039237816181)
                  ·
                    refine ⟨1386415738962378678545267, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14788434548932039237816181 1386415738962378678545267)
                    ·
                      rfl

theorem cell23_8100105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 5, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 5, 1, 1, 3, 5].length) (baseStart_8100105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8100105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8100105 prefixEnd_8100105 := by exact prefixLift 8100105
  have htrace : WordTrace (prefixWord ++ tailWord_8100105) baseStart_8100105 baseEnd_8100105 := by
    simpa [prefixWord, tailWord_8100105, baseEnd_8100105] using wordTrace_append hprefix tailTrace_8100105
  have hstable : (prefixWord ++ tailWord_8100105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8100105).length < 2 ^ (prefixWord ++ tailWord_8100105).sum := by decide
  have hdescent : baseEnd_8100105 < baseStart_8100105 := by decide
  rcases family_descends (prefixWord ++ tailWord_8100105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8100152 : List Nat := [2, 1, 2, 1, 3, 1, 4, 3, 2, 4]
def baseStart_8100152 : Nat := 118140960795 + 8100152 * 2 ^ 59
def prefixEnd_8100152 : Nat := 4983230072969 + 3 ^ 40 * 8100152 * 2
def baseEnd_8100152 : Nat := 1386423783492632450582695

theorem tailTrace_8100152 : CollatzResearch.WordTrace tailWord_8100152 prefixEnd_8100152 1386423783492632450582695 := by
  unfold tailWord_8100152
  simp only [CollatzResearch.WordTrace]
  refine ⟨147718407275270087334471355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196957876367026783112628473 147718407275270087334471355)
  ·
    refine ⟨221577610912905131001707033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147718407275270087334471355 221577610912905131001707033)
    ·
      refine ⟨166183208184678848251280275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 221577610912905131001707033 166183208184678848251280275)
      ·
        refine ⟨249274812277018272376920413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166183208184678848251280275 249274812277018272376920413)
        ·
          refine ⟨93478054603881852141345155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 249274812277018272376920413 93478054603881852141345155)
          ·
            refine ⟨140217081905822778212017733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93478054603881852141345155 140217081905822778212017733)
            ·
              refine ⟨26290702857341770914753325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 140217081905822778212017733 26290702857341770914753325)
              ·
                refine ⟨9859013571503164093032497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26290702857341770914753325 9859013571503164093032497)
                ·
                  refine ⟨7394260178627373069774373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9859013571503164093032497 7394260178627373069774373)
                  ·
                    refine ⟨1386423783492632450582695, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7394260178627373069774373 1386423783492632450582695)
                    ·
                      rfl

theorem cell23_8100152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 4, 3, 2, 4].length) (baseStart_8100152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8100152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8100152 prefixEnd_8100152 := by exact prefixLift 8100152
  have htrace : WordTrace (prefixWord ++ tailWord_8100152) baseStart_8100152 baseEnd_8100152 := by
    simpa [prefixWord, tailWord_8100152, baseEnd_8100152] using wordTrace_append hprefix tailTrace_8100152
  have hstable : (prefixWord ++ tailWord_8100152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8100152).length < 2 ^ (prefixWord ++ tailWord_8100152).sum := by decide
  have hdescent : baseEnd_8100152 < baseStart_8100152 := by decide
  rcases family_descends (prefixWord ++ tailWord_8100152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8100159 : List Nat := [1, 1, 2, 2, 4, 1, 3, 2, 3, 2, 2]
def baseStart_8100159 : Nat := 118140960795 + 8100159 * 2 ^ 59
def prefixEnd_8100159 : Nat := 4983230072969 + 3 ^ 40 * 8100159 * 2
def baseEnd_8100159 : Nat := 4159274944842478824360553

theorem tailTrace_8100159 : CollatzResearch.WordTrace tailWord_8100159 prefixEnd_8100159 4159274944842478824360553 := by
  unfold tailWord_8100159
  simp only [CollatzResearch.WordTrace]
  refine ⟨295437069861514814864447531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196958046574343209909631687 295437069861514814864447531)
  ·
    refine ⟨443155604792272222296671297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 295437069861514814864447531 443155604792272222296671297)
    ·
      refine ⟨332366703594204166722503473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 443155604792272222296671297 332366703594204166722503473)
      ·
        refine ⟨249275027695653125041877605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 332366703594204166722503473 249275027695653125041877605)
        ·
          refine ⟨46739067692934960945352051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 249275027695653125041877605 46739067692934960945352051)
          ·
            refine ⟨70108601539402441418028077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46739067692934960945352051 70108601539402441418028077)
            ·
              refine ⟨26290725577275915531760529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 70108601539402441418028077 26290725577275915531760529)
              ·
                refine ⟨19718044182956936648820397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26290725577275915531760529 19718044182956936648820397)
                ·
                  refine ⟨7394266568608851243307649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19718044182956936648820397 7394266568608851243307649)
                  ·
                    refine ⟨5545699926456638432480737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7394266568608851243307649 5545699926456638432480737)
                    ·
                      refine ⟨4159274944842478824360553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5545699926456638432480737 4159274944842478824360553)
                      ·
                        rfl

theorem cell23_8100159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 3, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 3, 2, 3, 2, 2].length) (baseStart_8100159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8100159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8100159 prefixEnd_8100159 := by exact prefixLift 8100159
  have htrace : WordTrace (prefixWord ++ tailWord_8100159) baseStart_8100159 baseEnd_8100159 := by
    simpa [prefixWord, tailWord_8100159, baseEnd_8100159] using wordTrace_append hprefix tailTrace_8100159
  have hstable : (prefixWord ++ tailWord_8100159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8100159).length < 2 ^ (prefixWord ++ tailWord_8100159).sum := by decide
  have hdescent : baseEnd_8100159 < baseStart_8100159 := by decide
  rcases family_descends (prefixWord ++ tailWord_8100159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8100175 : List Nat := [1, 1, 2, 1, 1, 2, 1, 5, 3, 3, 3]
def baseStart_8100175 : Nat := 118140960795 + 8100175 * 2 ^ 59
def prefixEnd_8100175 : Nat := 4983230072969 + 3 ^ 40 * 8100175 * 2
def baseEnd_8100175 : Nat := 4159283160532950761760479

theorem tailTrace_8100175 : CollatzResearch.WordTrace tailWord_8100175 prefixEnd_8100175 4159283160532950761760479 := by
  unfold tailWord_8100175
  simp only [CollatzResearch.WordTrace]
  refine ⟨295437653429456849597029979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196958435619637899731353319 295437653429456849597029979)
  ·
    refine ⟨443156480144185274395544969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 295437653429456849597029979 443156480144185274395544969)
    ·
      refine ⟨332367360108138955796658727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 443156480144185274395544969 332367360108138955796658727)
      ·
        refine ⟨498551040162208433694988091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 332367360108138955796658727 498551040162208433694988091)
        ·
          refine ⟨747826560243312650542482137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 498551040162208433694988091 747826560243312650542482137)
          ·
            refine ⟨560869920182484487906861603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 747826560243312650542482137 560869920182484487906861603)
            ·
              refine ⟨841304880273726731860292405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 560869920182484487906861603 841304880273726731860292405)
              ·
                refine ⟨78872332525661881111902413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 841304880273726731860292405 78872332525661881111902413)
                ·
                  refine ⟨29577124697123205416963405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 78872332525661881111902413 29577124697123205416963405)
                  ·
                    refine ⟨11091421761421202031361277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29577124697123205416963405 11091421761421202031361277)
                    ·
                      refine ⟨4159283160532950761760479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11091421761421202031361277 4159283160532950761760479)
                      ·
                        rfl

theorem cell23_8100175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 5, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 5, 3, 3, 3].length) (baseStart_8100175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8100175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8100175 prefixEnd_8100175 := by exact prefixLift 8100175
  have htrace : WordTrace (prefixWord ++ tailWord_8100175) baseStart_8100175 baseEnd_8100175 := by
    simpa [prefixWord, tailWord_8100175, baseEnd_8100175] using wordTrace_append hprefix tailTrace_8100175
  have hstable : (prefixWord ++ tailWord_8100175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8100175).length < 2 ^ (prefixWord ++ tailWord_8100175).sum := by decide
  have hdescent : baseEnd_8100175 < baseStart_8100175 := by decide
  rcases family_descends (prefixWord ++ tailWord_8100175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8100176 : List Nat := [2, 1, 1, 1, 1, 6, 1, 5, 1, 2, 2]
def baseStart_8100176 : Nat := 118140960795 + 8100176 * 2 ^ 59
def prefixEnd_8100176 : Nat := 4983230072969 + 3 ^ 40 * 8100176 * 2
def baseEnd_8100176 : Nat := 4159283674013605257847975

theorem tailTrace_8100176 : CollatzResearch.WordTrace tailWord_8100176 prefixEnd_8100176 4159283674013605257847975 := by
  unfold tailWord_8100176
  simp only [CollatzResearch.WordTrace]
  refine ⟨147718844951226613383908191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196958459934968817845210921 147718844951226613383908191)
  ·
    refine ⟨221578267426839920075862287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147718844951226613383908191 221578267426839920075862287)
    ·
      refine ⟨332367401140259880113793431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 221578267426839920075862287 332367401140259880113793431)
      ·
        refine ⟨498551101710389820170690147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 332367401140259880113793431 498551101710389820170690147)
        ·
          refine ⟨747826652565584730256035221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 498551101710389820170690147 747826652565584730256035221)
          ·
            refine ⟨35054374339011784230751651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 747826652565584730256035221 35054374339011784230751651)
            ·
              refine ⟨52581561508517676346127477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35054374339011784230751651 52581561508517676346127477)
              ·
                refine ⟨4929521391423532157449451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 52581561508517676346127477 4929521391423532157449451)
                ·
                  refine ⟨7394282087135298236174177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4929521391423532157449451 7394282087135298236174177)
                  ·
                    refine ⟨5545711565351473677130633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7394282087135298236174177 5545711565351473677130633)
                    ·
                      refine ⟨4159283674013605257847975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5545711565351473677130633 4159283674013605257847975)
                      ·
                        rfl

theorem cell23_8100176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 1, 5, 1, 2, 2].length) (baseStart_8100176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8100176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8100176 prefixEnd_8100176 := by exact prefixLift 8100176
  have htrace : WordTrace (prefixWord ++ tailWord_8100176) baseStart_8100176 baseEnd_8100176 := by
    simpa [prefixWord, tailWord_8100176, baseEnd_8100176] using wordTrace_append hprefix tailTrace_8100176
  have hstable : (prefixWord ++ tailWord_8100176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8100176).length < 2 ^ (prefixWord ++ tailWord_8100176).sum := by decide
  have hdescent : baseEnd_8100176 < baseStart_8100176 := by decide
  rcases family_descends (prefixWord ++ tailWord_8100176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8100219 : List Nat := [1, 1, 1, 1, 1, 7, 1, 4, 1, 3, 2]
def baseStart_8100219 : Nat := 118140960795 + 8100219 * 2 ^ 59
def prefixEnd_8100219 : Nat := 4983230072969 + 3 ^ 40 * 8100219 * 2
def baseEnd_8100219 : Nat := 4159305753681748589610277

theorem tailTrace_8100219 : CollatzResearch.WordTrace tailWord_8100219 prefixEnd_8100219 4159305753681748589610277 := by
  unfold tailWord_8100219
  simp only [CollatzResearch.WordTrace]
  refine ⟨295439258241297445111631711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196959505494198296741087807 295439258241297445111631711)
  ·
    refine ⟨443158887361946167667447567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 295439258241297445111631711 443158887361946167667447567)
    ·
      refine ⟨664738331042919251501171351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 443158887361946167667447567 664738331042919251501171351)
      ·
        refine ⟨997107496564378877251757027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 664738331042919251501171351 997107496564378877251757027)
        ·
          refine ⟨1495661244846568315877635541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 997107496564378877251757027 1495661244846568315877635541)
          ·
            refine ⟨35054560426091444903382083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 1495661244846568315877635541 35054560426091444903382083)
            ·
              refine ⟨52581840639137167355073125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35054560426091444903382083 52581840639137167355073125)
              ·
                refine ⟨9859095119838218879076211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 52581840639137167355073125 9859095119838218879076211)
                ·
                  refine ⟨14788642679757328318614317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9859095119838218879076211 14788642679757328318614317)
                  ·
                    refine ⟨5545741004908998119480369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14788642679757328318614317 5545741004908998119480369)
                    ·
                      refine ⟨4159305753681748589610277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5545741004908998119480369 4159305753681748589610277)
                      ·
                        rfl

theorem cell23_8100219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 1, 4, 1, 3, 2].length) (baseStart_8100219 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8100219 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8100219 prefixEnd_8100219 := by exact prefixLift 8100219
  have htrace : WordTrace (prefixWord ++ tailWord_8100219) baseStart_8100219 baseEnd_8100219 := by
    simpa [prefixWord, tailWord_8100219, baseEnd_8100219] using wordTrace_append hprefix tailTrace_8100219
  have hstable : (prefixWord ++ tailWord_8100219).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8100219).length < 2 ^ (prefixWord ++ tailWord_8100219).sum := by decide
  have hdescent : baseEnd_8100219 < baseStart_8100219 := by decide
  rcases family_descends (prefixWord ++ tailWord_8100219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8100235 : List Nat := [1, 1, 1, 1, 4, 4, 1, 1, 1, 3, 5]
def baseStart_8100235 : Nat := 118140960795 + 8100235 * 2 ^ 59
def prefixEnd_8100235 : Nat := 4983230072969 + 3 ^ 40 * 8100235 * 2
def baseEnd_8100235 : Nat := 4159313969372220527010203

theorem tailTrace_8100235 : CollatzResearch.WordTrace tailWord_8100235 prefixEnd_8100235 4159313969372220527010203 := by
  unfold tailWord_8100235
  simp only [CollatzResearch.WordTrace]
  refine ⟨295439841809239479844214159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196959894539492986562809439 295439841809239479844214159)
  ·
    refine ⟨443159762713859219766321239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 295439841809239479844214159 443159762713859219766321239)
    ·
      refine ⟨664739644070788829649481859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 443159762713859219766321239 664739644070788829649481859)
      ·
        refine ⟨997109466106183244474222789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 664739644070788829649481859 997109466106183244474222789)
        ·
          refine ⟨186958024894909358338916773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 997109466106183244474222789 186958024894909358338916773)
          ·
            refine ⟨35054629667795504688546895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 186958024894909358338916773 35054629667795504688546895)
            ·
              refine ⟨52581944501693257032820343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35054629667795504688546895 52581944501693257032820343)
              ·
                refine ⟨78872916752539885549230515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52581944501693257032820343 78872916752539885549230515)
                ·
                  refine ⟨118309375128809828323845773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 78872916752539885549230515 118309375128809828323845773)
                  ·
                    refine ⟨44366015673303685621442165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 118309375128809828323845773 44366015673303685621442165)
                    ·
                      refine ⟨4159313969372220527010203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44366015673303685621442165 4159313969372220527010203)
                      ·
                        rfl

theorem cell23_8100235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 1, 1, 1, 3, 5].length) (baseStart_8100235 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8100235 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8100235 prefixEnd_8100235 := by exact prefixLift 8100235
  have htrace : WordTrace (prefixWord ++ tailWord_8100235) baseStart_8100235 baseEnd_8100235 := by
    simpa [prefixWord, tailWord_8100235, baseEnd_8100235] using wordTrace_append hprefix tailTrace_8100235
  have hstable : (prefixWord ++ tailWord_8100235).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8100235).length < 2 ^ (prefixWord ++ tailWord_8100235).sum := by decide
  have hdescent : baseEnd_8100235 < baseStart_8100235 := by decide
  rcases family_descends (prefixWord ++ tailWord_8100235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8100249 : List Nat := [1, 2, 1, 2, 1, 4, 1, 3, 4, 2, 2]
def baseStart_8100249 : Nat := 118140960795 + 8100249 * 2 ^ 59
def prefixEnd_8100249 : Nat := 4983230072969 + 3 ^ 40 * 8100249 * 2
def baseEnd_8100249 : Nat := 4159321158101383472235139

theorem tailTrace_8100249 : CollatzResearch.WordTrace tailWord_8100249 prefixEnd_8100249 4159321158101383472235139 := by
  unfold tailWord_8100249
  simp only [CollatzResearch.WordTrace]
  refine ⟨295440352431188760235223801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196960234954125840156815867 295440352431188760235223801)
  ·
    refine ⟨221580264323391570176417851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 295440352431188760235223801 221580264323391570176417851)
    ·
      refine ⟨332370396485087355264626777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 221580264323391570176417851 332370396485087355264626777)
      ·
        refine ⟨249277797363815516448470083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 332370396485087355264626777 249277797363815516448470083)
        ·
          refine ⟨373916696045723274672705125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 249277797363815516448470083 373916696045723274672705125)
          ·
            refine ⟨70109380508573114001132211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 373916696045723274672705125 70109380508573114001132211)
            ·
              refine ⟨105164070762859671001698317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70109380508573114001132211 105164070762859671001698317)
              ·
                refine ⟨39436526536072376625636869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 105164070762859671001698317 39436526536072376625636869)
                ·
                  refine ⟨7394348725513570617306913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39436526536072376625636869 7394348725513570617306913)
                  ·
                    refine ⟨5545761544135177962980185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7394348725513570617306913 5545761544135177962980185)
                    ·
                      refine ⟨4159321158101383472235139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5545761544135177962980185 4159321158101383472235139)
                      ·
                        rfl

theorem cell23_8100249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 1, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 1, 3, 4, 2, 2].length) (baseStart_8100249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8100249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8100249 prefixEnd_8100249 := by exact prefixLift 8100249
  have htrace : WordTrace (prefixWord ++ tailWord_8100249) baseStart_8100249 baseEnd_8100249 := by
    simpa [prefixWord, tailWord_8100249, baseEnd_8100249] using wordTrace_append hprefix tailTrace_8100249
  have hstable : (prefixWord ++ tailWord_8100249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8100249).length < 2 ^ (prefixWord ++ tailWord_8100249).sum := by decide
  have hdescent : baseEnd_8100249 < baseStart_8100249 := by decide
  rcases family_descends (prefixWord ++ tailWord_8100249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8100309 : List Nat := [1, 3, 2, 3, 1, 2, 1, 1, 2, 5, 2]
def baseStart_8100309 : Nat := 118140960795 + 8100309 * 2 ^ 59
def prefixEnd_8100309 : Nat := 4983230072969 + 3 ^ 40 * 8100309 * 2
def baseEnd_8100309 : Nat := 4159351966940653237484863

theorem tailTrace_8100309 : CollatzResearch.WordTrace tailWord_8100309 prefixEnd_8100309 4159351966940653237484863 := by
  unfold tailWord_8100309
  simp only [CollatzResearch.WordTrace]
  refine ⟨295442540810971390482407981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196961693873980926988271987 295442540810971390482407981)
  ·
    refine ⟨110790952804114271430902993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 295442540810971390482407981 110790952804114271430902993)
    ·
      refine ⟨83093214603085703573177245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110790952804114271430902993 83093214603085703573177245)
      ·
        refine ⟨31159955476157138839941467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 83093214603085703573177245 31159955476157138839941467)
        ·
          refine ⟨46739933214235708259912201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31159955476157138839941467 46739933214235708259912201)
          ·
            refine ⟨35054949910676781194934151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46739933214235708259912201 35054949910676781194934151)
            ·
              refine ⟨52582424866015171792401227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35054949910676781194934151 52582424866015171792401227)
              ·
                refine ⟨78873637299022757688601841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52582424866015171792401227 78873637299022757688601841)
                ·
                  refine ⟨59155227974267068266451381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 78873637299022757688601841 59155227974267068266451381)
                  ·
                    refine ⟨5545802622587537649979817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 59155227974267068266451381 5545802622587537649979817)
                    ·
                      refine ⟨4159351966940653237484863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5545802622587537649979817 4159351966940653237484863)
                      ·
                        rfl

theorem cell23_8100309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 1, 1, 2, 5, 2].length) (baseStart_8100309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8100309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8100309 prefixEnd_8100309 := by exact prefixLift 8100309
  have htrace : WordTrace (prefixWord ++ tailWord_8100309) baseStart_8100309 baseEnd_8100309 := by
    simpa [prefixWord, tailWord_8100309, baseEnd_8100309] using wordTrace_append hprefix tailTrace_8100309
  have hstable : (prefixWord ++ tailWord_8100309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8100309).length < 2 ^ (prefixWord ++ tailWord_8100309).sum := by decide
  have hdescent : baseEnd_8100309 < baseStart_8100309 := by decide
  rcases family_descends (prefixWord ++ tailWord_8100309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8100356 : List Nat := [2, 3, 2, 3, 1, 1, 1, 2, 2, 4, 2]
def baseStart_8100356 : Nat := 118140960795 + 8100356 * 2 ^ 59
def prefixEnd_8100356 : Nat := 4983230072969 + 3 ^ 40 * 8100356 * 2
def baseEnd_8100356 : Nat := 4159376100531414553597147

theorem tailTrace_8100356 : CollatzResearch.WordTrace tailWord_8100356 prefixEnd_8100356 4159376100531414553597147 := by
  unfold tailWord_8100356
  simp only [CollatzResearch.WordTrace]
  refine ⟨147722127520900558754684461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196962836694534078339579281 147722127520900558754684461)
  ·
    refine ⟨55395797820337709533006673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 147722127520900558754684461 55395797820337709533006673)
    ·
      refine ⟨41546848365253282149755005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55395797820337709533006673 41546848365253282149755005)
      ·
        refine ⟨15580068136969980806158127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41546848365253282149755005 15580068136969980806158127)
        ·
          refine ⟨23370102205454971209237191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15580068136969980806158127 23370102205454971209237191)
          ·
            refine ⟨35055153308182456813855787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23370102205454971209237191 35055153308182456813855787)
            ·
              refine ⟨52582729962273685220783681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35055153308182456813855787 52582729962273685220783681)
              ·
                refine ⟨39437047471705263915587761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52582729962273685220783681 39437047471705263915587761)
                ·
                  refine ⟨29577785603778947936690821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39437047471705263915587761 29577785603778947936690821)
                  ·
                    refine ⟨5545834800708552738129529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29577785603778947936690821 5545834800708552738129529)
                    ·
                      refine ⟨4159376100531414553597147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5545834800708552738129529 4159376100531414553597147)
                      ·
                        rfl

theorem cell23_8100356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 1, 2, 2, 4, 2].length) (baseStart_8100356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8100356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8100356 prefixEnd_8100356 := by exact prefixLift 8100356
  have htrace : WordTrace (prefixWord ++ tailWord_8100356) baseStart_8100356 baseEnd_8100356 := by
    simpa [prefixWord, tailWord_8100356, baseEnd_8100356] using wordTrace_append hprefix tailTrace_8100356
  have hstable : (prefixWord ++ tailWord_8100356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8100356).length < 2 ^ (prefixWord ++ tailWord_8100356).sum := by decide
  have hdescent : baseEnd_8100356 < baseStart_8100356 := by decide
  rcases family_descends (prefixWord ++ tailWord_8100356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8100362 : List Nat := [3, 1, 2, 2, 2, 1, 3, 1, 8]
def baseStart_8100362 : Nat := 118140960795 + 8100362 * 2 ^ 59
def prefixEnd_8100362 : Nat := 4983230072969 + 3 ^ 40 * 8100362 * 2
def baseEnd_8100362 : Nat := 462153242379482392235791

theorem tailTrace_8100362 : CollatzResearch.WordTrace tailWord_8100362 prefixEnd_8100362 462153242379482392235791 := by
  unfold tailWord_8100362
  simp only [CollatzResearch.WordTrace]
  refine ⟨73861118469944845133521835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 196962982586519587022724893 73861118469944845133521835)
  ·
    refine ⟨110791677704917267700282753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73861118469944845133521835 110791677704917267700282753)
    ·
      refine ⟨83093758278687950775212065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110791677704917267700282753 83093758278687950775212065)
      ·
        refine ⟨62320318709015963081409049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83093758278687950775212065 62320318709015963081409049)
        ·
          refine ⟨46740239031761972311056787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62320318709015963081409049 46740239031761972311056787)
          ·
            refine ⟨70110358547642958466585181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46740239031761972311056787 70110358547642958466585181)
            ·
              refine ⟨26291384455366109424969443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 70110358547642958466585181 26291384455366109424969443)
              ·
                refine ⟨39437076683049164137454165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26291384455366109424969443 39437076683049164137454165)
                ·
                  refine ⟨462153242379482392235791, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 39437076683049164137454165 462153242379482392235791)
                  ·
                    rfl

theorem cell23_8100362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 3, 1, 8].length) (baseStart_8100362 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8100362 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8100362 prefixEnd_8100362 := by exact prefixLift 8100362
  have htrace : WordTrace (prefixWord ++ tailWord_8100362) baseStart_8100362 baseEnd_8100362 := by
    simpa [prefixWord, tailWord_8100362, baseEnd_8100362] using wordTrace_append hprefix tailTrace_8100362
  have hstable : (prefixWord ++ tailWord_8100362).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8100362).length < 2 ^ (prefixWord ++ tailWord_8100362).sum := by decide
  have hdescent : baseEnd_8100362 < baseStart_8100362 := by decide
  rcases family_descends (prefixWord ++ tailWord_8100362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8100366 : List Nat := [4, 1, 1, 2, 3, 2, 2, 1, 3, 4]
def baseStart_8100366 : Nat := 118140960795 + 8100366 * 2 ^ 59
def prefixEnd_8100366 : Nat := 4983230072969 + 3 ^ 40 * 8100366 * 2
def baseEnd_8100366 : Nat := 1386460411779319838157367

theorem tailTrace_8100366 : CollatzResearch.WordTrace tailWord_8100366 prefixEnd_8100366 1386460411779319838157367 := by
  unfold tailWord_8100366
  simp only [CollatzResearch.WordTrace]
  refine ⟨36930577471470611152154119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 196963079847843259478155301 36930577471470611152154119)
  ·
    refine ⟨55395866207205916728231179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36930577471470611152154119 55395866207205916728231179)
    ·
      refine ⟨83093799310808875092346769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55395866207205916728231179 83093799310808875092346769)
      ·
        refine ⟨62320349483106656319260077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83093799310808875092346769 62320349483106656319260077)
        ·
          refine ⟨23370131056164996119722529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62320349483106656319260077 23370131056164996119722529)
          ·
            refine ⟨17527598292123747089791897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23370131056164996119722529 17527598292123747089791897)
            ·
              refine ⟨13145698719092810317343923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17527598292123747089791897 13145698719092810317343923)
              ·
                refine ⟨19718548078639215476015885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13145698719092810317343923 19718548078639215476015885)
                ·
                  refine ⟨7394455529489705803505957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19718548078639215476015885 7394455529489705803505957)
                  ·
                    refine ⟨1386460411779319838157367, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7394455529489705803505957 1386460411779319838157367)
                    ·
                      rfl

theorem cell23_8100366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 2, 2, 1, 3, 4].length) (baseStart_8100366 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8100366 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8100366 prefixEnd_8100366 := by exact prefixLift 8100366
  have htrace : WordTrace (prefixWord ++ tailWord_8100366) baseStart_8100366 baseEnd_8100366 := by
    simpa [prefixWord, tailWord_8100366, baseEnd_8100366] using wordTrace_append hprefix tailTrace_8100366
  have hstable : (prefixWord ++ tailWord_8100366).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8100366).length < 2 ^ (prefixWord ++ tailWord_8100366).sum := by decide
  have hdescent : baseEnd_8100366 < baseStart_8100366 := by decide
  rcases family_descends (prefixWord ++ tailWord_8100366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8100399 : List Nat := [1, 1, 2, 1, 2, 1, 1, 1, 8, 3, 2]
def baseStart_8100399 : Nat := 118140960795 + 8100399 * 2 ^ 59
def prefixEnd_8100399 : Nat := 4983230072969 + 3 ^ 40 * 8100399 * 2
def baseEnd_8100399 : Nat := 4159398180199557885359449

theorem tailTrace_8100399 : CollatzResearch.WordTrace tailWord_8100399 prefixEnd_8100399 4159398180199557885359449 := by
  unfold tailWord_8100399
  simp only [CollatzResearch.WordTrace]
  refine ⟨295445823380645335853184251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196963882253763557235456167 295445823380645335853184251)
  ·
    refine ⟨443168735070968003779776377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 295445823380645335853184251 443168735070968003779776377)
    ·
      refine ⟨332376551303226002834832283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 443168735070968003779776377 332376551303226002834832283)
      ·
        refine ⟨498564826954839004252248425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 332376551303226002834832283 498564826954839004252248425)
        ·
          refine ⟨373923620216129253189186319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 498564826954839004252248425 373923620216129253189186319)
          ·
            refine ⟨560885430324193879783779479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 373923620216129253189186319 560885430324193879783779479)
            ·
              refine ⟨841328145486290819675669219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 560885430324193879783779479 841328145486290819675669219)
              ·
                refine ⟨1261992218229436229513503829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 841328145486290819675669219 1261992218229436229513503829)
                ·
                  refine ⟨14788971307376205814611373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 1261992218229436229513503829 14788971307376205814611373)
                  ·
                    refine ⟨5545864240266077180479265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14788971307376205814611373 5545864240266077180479265)
                    ·
                      refine ⟨4159398180199557885359449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5545864240266077180479265 4159398180199557885359449)
                      ·
                        rfl

theorem cell23_8100399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 1, 8, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 1, 8, 3, 2].length) (baseStart_8100399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8100399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8100399 prefixEnd_8100399 := by exact prefixLift 8100399
  have htrace : WordTrace (prefixWord ++ tailWord_8100399) baseStart_8100399 baseEnd_8100399 := by
    simpa [prefixWord, tailWord_8100399, baseEnd_8100399] using wordTrace_append hprefix tailTrace_8100399
  have hstable : (prefixWord ++ tailWord_8100399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8100399).length < 2 ^ (prefixWord ++ tailWord_8100399).sum := by decide
  have hdescent : baseEnd_8100399 < baseStart_8100399 := by decide
  rcases family_descends (prefixWord ++ tailWord_8100399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8100409 : List Nat := [1, 2, 1, 5, 1, 1, 1, 5, 1, 5]
def baseStart_8100409 : Nat := 118140960795 + 8100409 * 2 ^ 59
def prefixEnd_8100409 : Nat := 4983230072969 + 3 ^ 40 * 8100409 * 2
def baseEnd_8100409 : Nat := 1386467771668700948744801

theorem tailTrace_8100409 : CollatzResearch.WordTrace tailWord_8100409 prefixEnd_8100409 1386467771668700948744801 := by
  unfold tailWord_8100409
  simp only [CollatzResearch.WordTrace]
  refine ⟨295446188110609107561048281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196964125407072738374032187 295446188110609107561048281)
  ·
    refine ⟨221584641082956830670786211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 295446188110609107561048281 221584641082956830670786211)
    ·
      refine ⟨332376961624435246006179317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 221584641082956830670786211 332376961624435246006179317)
      ·
        refine ⟨31160340152290804313079311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 332376961624435246006179317 31160340152290804313079311)
        ·
          refine ⟨46740510228436206469618967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31160340152290804313079311 46740510228436206469618967)
          ·
            refine ⟨70110765342654309704428451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46740510228436206469618967 70110765342654309704428451)
            ·
              refine ⟨105166148013981464556642677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70110765342654309704428451 105166148013981464556642677)
              ·
                refine ⟨9859326376310762302185251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 105166148013981464556642677 9859326376310762302185251)
                ·
                  refine ⟨14788989564466143453277877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9859326376310762302185251 14788989564466143453277877)
                  ·
                    refine ⟨1386467771668700948744801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14788989564466143453277877 1386467771668700948744801)
                    ·
                      rfl

theorem cell23_8100409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 1, 5, 1, 5].length) (baseStart_8100409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8100409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8100409 prefixEnd_8100409 := by exact prefixLift 8100409
  have htrace : WordTrace (prefixWord ++ tailWord_8100409) baseStart_8100409 baseEnd_8100409 := by
    simpa [prefixWord, tailWord_8100409, baseEnd_8100409] using wordTrace_append hprefix tailTrace_8100409
  have hstable : (prefixWord ++ tailWord_8100409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8100409).length < 2 ^ (prefixWord ++ tailWord_8100409).sum := by decide
  have hdescent : baseEnd_8100409 < baseStart_8100409 := by decide
  rcases family_descends (prefixWord ++ tailWord_8100409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8100423 : List Nat := [1, 1, 4, 1, 4, 3, 1, 1, 3, 1, 3]
def baseStart_8100423 : Nat := 118140960795 + 8100423 * 2 ^ 59
def prefixEnd_8100423 : Nat := 4983230072969 + 3 ^ 40 * 8100423 * 2
def baseEnd_8100423 : Nat := 4159410503735265791459339

theorem tailTrace_8100423 : CollatzResearch.WordTrace tailWord_8100423 prefixEnd_8100423 4159410503735265791459339 := by
  unfold tailWord_8100423
  simp only [CollatzResearch.WordTrace]
  refine ⟨295446698732558387952057923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196964465821705591968038615 295446698732558387952057923)
  ·
    refine ⟨443170048098837581928086885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 295446698732558387952057923 443170048098837581928086885)
    ·
      refine ⟨83094384018532046611516291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 443170048098837581928086885 83094384018532046611516291)
      ·
        refine ⟨124641576027798069917274437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83094384018532046611516291 124641576027798069917274437)
        ·
          refine ⟨23370295505212138109488957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 124641576027798069917274437 23370295505212138109488957)
          ·
            refine ⟨8763860814454551791058359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23370295505212138109488957 8763860814454551791058359)
            ·
              refine ⟨13145791221681827686587539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8763860814454551791058359 13145791221681827686587539)
              ·
                refine ⟨19718686832522741529881309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13145791221681827686587539 19718686832522741529881309)
                ·
                  refine ⟨7394507562196028073705491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19718686832522741529881309 7394507562196028073705491)
                  ·
                    refine ⟨11091761343294042110558237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7394507562196028073705491 11091761343294042110558237)
                    ·
                      refine ⟨4159410503735265791459339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11091761343294042110558237 4159410503735265791459339)
                      ·
                        rfl

theorem cell23_8100423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 3, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 3, 1, 1, 3, 1, 3].length) (baseStart_8100423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8100423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8100423 prefixEnd_8100423 := by exact prefixLift 8100423
  have htrace : WordTrace (prefixWord ++ tailWord_8100423) baseStart_8100423 baseEnd_8100423 := by
    simpa [prefixWord, tailWord_8100423, baseEnd_8100423] using wordTrace_append hprefix tailTrace_8100423
  have hstable : (prefixWord ++ tailWord_8100423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8100423).length < 2 ^ (prefixWord ++ tailWord_8100423).sum := by decide
  have hdescent : baseEnd_8100423 < baseStart_8100423 := by decide
  rcases family_descends (prefixWord ++ tailWord_8100423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8100432 : List Nat := [2, 1, 1, 1, 1, 3, 2, 3, 3, 1, 5]
def baseStart_8100432 : Nat := 118140960795 + 8100432 * 2 ^ 59
def prefixEnd_8100432 : Nat := 4983230072969 + 3 ^ 40 * 8100432 * 2
def baseEnd_8100432 : Nat := 4159415125061156256246797

theorem tailTrace_8100432 : CollatzResearch.WordTrace tailWord_8100432 prefixEnd_8100432 4159415125061156256246797 := by
  unfold tailWord_8100432
  simp only [CollatzResearch.WordTrace]
  refine ⟨147723513494762891244567775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196964684659683854992757033 147723513494762891244567775)
  ·
    refine ⟨221585270242144336866851663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147723513494762891244567775 221585270242144336866851663)
    ·
      refine ⟨332377905363216505300277495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 221585270242144336866851663 332377905363216505300277495)
      ·
        refine ⟨498566858044824757950416243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 332377905363216505300277495 498566858044824757950416243)
        ·
          refine ⟨747850287067237136925624365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 498566858044824757950416243 747850287067237136925624365)
          ·
            refine ⟨280443857650213926347109137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 747850287067237136925624365 280443857650213926347109137)
            ·
              refine ⟨210332893237660444760331853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 280443857650213926347109137 210332893237660444760331853)
              ·
                refine ⟨78874834964122666785124445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 210332893237660444760331853 78874834964122666785124445)
                ·
                  refine ⟨29578063111546000044421667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 78874834964122666785124445 29578063111546000044421667)
                  ·
                    refine ⟨44367094667319000066632501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29578063111546000044421667 44367094667319000066632501)
                    ·
                      refine ⟨4159415125061156256246797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44367094667319000066632501 4159415125061156256246797)
                      ·
                        rfl

theorem cell23_8100432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 3, 3, 1, 5].length) (baseStart_8100432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8100432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8100432 prefixEnd_8100432 := by exact prefixLift 8100432
  have htrace : WordTrace (prefixWord ++ tailWord_8100432) baseStart_8100432 baseEnd_8100432 := by
    simpa [prefixWord, tailWord_8100432, baseEnd_8100432] using wordTrace_append hprefix tailTrace_8100432
  have hstable : (prefixWord ++ tailWord_8100432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8100432).length < 2 ^ (prefixWord ++ tailWord_8100432).sum := by decide
  have hdescent : baseEnd_8100432 < baseStart_8100432 := by decide
  rcases family_descends (prefixWord ++ tailWord_8100432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8100452 : List Nat := [2, 3, 1, 1, 2, 2, 1, 11]
def baseStart_8100452 : Nat := 118140960795 + 8100452 * 2 ^ 59
def prefixEnd_8100452 : Nat := 4983230072969 + 3 ^ 40 * 8100452 * 2
def baseEnd_8100452 : Nat := 154052792395342451036915

theorem tailTrace_8100452 : CollatzResearch.WordTrace tailWord_8100452 prefixEnd_8100452 154052792395342451036915 := by
  unfold tailWord_8100452
  simp only [CollatzResearch.WordTrace]
  refine ⟨147723878224726662952431805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196965170966302217269909073 147723878224726662952431805)
  ·
    refine ⟨55396454334272498607161927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 147723878224726662952431805 55396454334272498607161927)
    ·
      refine ⟨83094681501408747910742891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55396454334272498607161927 83094681501408747910742891)
      ·
        refine ⟨124642022252113121866114337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83094681501408747910742891 124642022252113121866114337)
        ·
          refine ⟨93481516689084841399585753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 124642022252113121866114337 93481516689084841399585753)
          ·
            refine ⟨70111137516813631049689315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 93481516689084841399585753 70111137516813631049689315)
            ·
              refine ⟨105166706275220446574533973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70111137516813631049689315 105166706275220446574533973)
              ·
                refine ⟨154052792395342451036915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 105166706275220446574533973 154052792395342451036915)
                ·
                  rfl

theorem cell23_8100452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 1, 11].length) (baseStart_8100452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8100452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8100452 prefixEnd_8100452 := by exact prefixLift 8100452
  have htrace : WordTrace (prefixWord ++ tailWord_8100452) baseStart_8100452 baseEnd_8100452 := by
    simpa [prefixWord, tailWord_8100452, baseEnd_8100452] using wordTrace_append hprefix tailTrace_8100452
  have hstable : (prefixWord ++ tailWord_8100452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8100452).length < 2 ^ (prefixWord ++ tailWord_8100452).sum := by decide
  have hdescent : baseEnd_8100452 < baseStart_8100452 := by decide
  rcases family_descends (prefixWord ++ tailWord_8100452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8100456 : List Nat := [2, 1, 4, 3, 2, 1, 1, 2, 1, 6]
def baseStart_8100456 : Nat := 118140960795 + 8100456 * 2 ^ 59
def prefixEnd_8100456 : Nat := 4983230072969 + 3 ^ 40 * 8100456 * 2
def baseEnd_8100456 : Nat := 1386475816198954720782229

theorem tailTrace_8100456 : CollatzResearch.WordTrace tailWord_8100456 prefixEnd_8100456 1386475816198954720782229 := by
  unfold tailWord_8100456
  simp only [CollatzResearch.WordTrace]
  refine ⟨147723951170719417294004611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196965268227625889725339481 147723951170719417294004611)
  ·
    refine ⟨221585926756079125941006917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147723951170719417294004611 221585926756079125941006917)
    ·
      refine ⟨41547361266764836113938797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 221585926756079125941006917 41547361266764836113938797)
      ·
        refine ⟨15580260475036813542727049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41547361266764836113938797 15580260475036813542727049)
        ·
          refine ⟨11685195356277610157045287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15580260475036813542727049 11685195356277610157045287)
          ·
            refine ⟨17527793034416415235567931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11685195356277610157045287 17527793034416415235567931)
            ·
              refine ⟨26291689551624622853351897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17527793034416415235567931 26291689551624622853351897)
              ·
                refine ⟨19718767163718467140013923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26291689551624622853351897 19718767163718467140013923)
                ·
                  refine ⟨29578150745577700710020885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19718767163718467140013923 29578150745577700710020885)
                  ·
                    refine ⟨1386475816198954720782229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29578150745577700710020885 1386475816198954720782229)
                    ·
                      rfl

theorem cell23_8100456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 1, 1, 2, 1, 6].length) (baseStart_8100456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8100456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8100456 prefixEnd_8100456 := by exact prefixLift 8100456
  have htrace : WordTrace (prefixWord ++ tailWord_8100456) baseStart_8100456 baseEnd_8100456 := by
    simpa [prefixWord, tailWord_8100456, baseEnd_8100456] using wordTrace_append hprefix tailTrace_8100456
  have hstable : (prefixWord ++ tailWord_8100456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8100456).length < 2 ^ (prefixWord ++ tailWord_8100456).sum := by decide
  have hdescent : baseEnd_8100456 < baseStart_8100456 := by decide
  rcases family_descends (prefixWord ++ tailWord_8100456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8100469 : List Nat := [1, 3, 4, 2, 2, 11]
def baseStart_8100469 : Nat := 118140960795 + 8100469 * 2 ^ 59
def prefixEnd_8100469 : Nat := 4983230072969 + 3 ^ 40 * 8100469 * 2
def baseEnd_8100469 : Nat := 17117012855330751487589

theorem tailTrace_8100469 : CollatzResearch.WordTrace tailWord_8100469 prefixEnd_8100469 17117012855330751487589 := by
  unfold tailWord_8100469
  simp only [CollatzResearch.WordTrace]
  refine ⟨295448376490391737808232461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196965584326927825205488307 295448376490391737808232461)
  ·
    refine ⟨110793141183896901678087173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 295448376490391737808232461 110793141183896901678087173)
    ·
      refine ⟨20773713971980669064641345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 110793141183896901678087173 20773713971980669064641345)
      ·
        refine ⟨15580285478985501798481009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20773713971980669064641345 15580285478985501798481009)
        ·
          refine ⟨11685214109239126348860757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15580285478985501798481009 11685214109239126348860757)
          ·
            refine ⟨17117012855330751487589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 11685214109239126348860757 17117012855330751487589)
            ·
              rfl

theorem cell23_8100469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 11].length) (baseStart_8100469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8100469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8100469 prefixEnd_8100469 := by exact prefixLift 8100469
  have htrace : WordTrace (prefixWord ++ tailWord_8100469) baseStart_8100469 baseEnd_8100469 := by
    simpa [prefixWord, tailWord_8100469, baseEnd_8100469] using wordTrace_append hprefix tailTrace_8100469
  have hstable : (prefixWord ++ tailWord_8100469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8100469).length < 2 ^ (prefixWord ++ tailWord_8100469).sum := by decide
  have hdescent : baseEnd_8100469 < baseStart_8100469 := by decide
  rcases family_descends (prefixWord ++ tailWord_8100469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8100480 : List Nat := [2, 1, 1, 2, 1, 6, 1, 4, 1, 2, 2]
def baseStart_8100480 : Nat := 118140960795 + 8100480 * 2 ^ 59
def prefixEnd_8100480 : Nat := 4983230072969 + 3 ^ 40 * 8100480 * 2
def baseEnd_8100480 : Nat := 4159439772132572068446577

theorem tailTrace_8100480 : CollatzResearch.WordTrace tailWord_8100480 prefixEnd_8100480 4159439772132572068446577 := by
  unfold tailWord_8100480
  simp only [CollatzResearch.WordTrace]
  refine ⟨147724388846675943343441447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196965851795567924457921929 147724388846675943343441447)
  ·
    refine ⟨221586583270013915015162171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147724388846675943343441447 221586583270013915015162171)
    ·
      refine ⟨332379874905020872522743257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 221586583270013915015162171 332379874905020872522743257)
      ·
        refine ⟨249284906178765654392057443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 332379874905020872522743257 249284906178765654392057443)
        ·
          refine ⟨373927359268148481588086165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 249284906178765654392057443 373927359268148481588086165)
          ·
            refine ⟨17527844965694460074441539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 373927359268148481588086165 17527844965694460074441539)
            ·
              refine ⟨26291767448541690111662309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17527844965694460074441539 26291767448541690111662309)
              ·
                refine ⟨4929706396601566895936683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26291767448541690111662309 4929706396601566895936683)
                ·
                  refine ⟨7394559594902350343905025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4929706396601566895936683 7394559594902350343905025)
                  ·
                    refine ⟨5545919696176762757928769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7394559594902350343905025 5545919696176762757928769)
                    ·
                      refine ⟨4159439772132572068446577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5545919696176762757928769 4159439772132572068446577)
                      ·
                        rfl

theorem cell23_8100480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 6, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 6, 1, 4, 1, 2, 2].length) (baseStart_8100480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8100480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8100480 prefixEnd_8100480 := by exact prefixLift 8100480
  have htrace : WordTrace (prefixWord ++ tailWord_8100480) baseStart_8100480 baseEnd_8100480 := by
    simpa [prefixWord, tailWord_8100480, baseEnd_8100480] using wordTrace_append hprefix tailTrace_8100480
  have hstable : (prefixWord ++ tailWord_8100480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8100480).length < 2 ^ (prefixWord ++ tailWord_8100480).sum := by decide
  have hdescent : baseEnd_8100480 < baseStart_8100480 := by decide
  rcases family_descends (prefixWord ++ tailWord_8100480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8100593 : List Nat := [1, 2, 2, 2, 2, 2, 5, 2, 5]
def baseStart_8100593 : Nat := 118140960795 + 8100593 * 2 ^ 59
def prefixEnd_8100593 : Nat := 4983230072969 + 3 ^ 40 * 8100593 * 2
def baseEnd_8100593 : Nat := 462166421716281125148173

theorem tailTrace_8100593 : CollatzResearch.WordTrace tailWord_8100593 prefixEnd_8100593 462166421716281125148173 := by
  unfold tailWord_8100593
  simp only [CollatzResearch.WordTrace]
  refine ⟨295452899141942506985746433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196968599427961671323830955 295452899141942506985746433)
  ·
    refine ⟨221589674356456880239309825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 295452899141942506985746433 221589674356456880239309825)
    ·
      refine ⟨166192255767342660179482369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 221589674356456880239309825 166192255767342660179482369)
      ·
        refine ⟨124644191825506995134611777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 166192255767342660179482369 124644191825506995134611777)
        ·
          refine ⟨93483143869130246350958833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 124644191825506995134611777 93483143869130246350958833)
          ·
            refine ⟨70112357901847684763219125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 93483143869130246350958833 70112357901847684763219125)
            ·
              refine ⟨6573033553298220446551793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 70112357901847684763219125 6573033553298220446551793)
              ·
                refine ⟨4929775164973665334913845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6573033553298220446551793 4929775164973665334913845)
                ·
                  refine ⟨462166421716281125148173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4929775164973665334913845 462166421716281125148173)
                  ·
                    rfl

theorem cell23_8100593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 5, 2, 5].length) (baseStart_8100593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8100593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8100593 prefixEnd_8100593 := by exact prefixLift 8100593
  have htrace : WordTrace (prefixWord ++ tailWord_8100593) baseStart_8100593 baseEnd_8100593 := by
    simpa [prefixWord, tailWord_8100593, baseEnd_8100593] using wordTrace_append hprefix tailTrace_8100593
  have hstable : (prefixWord ++ tailWord_8100593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8100593).length < 2 ^ (prefixWord ++ tailWord_8100593).sum := by decide
  have hdescent : baseEnd_8100593 < baseStart_8100593 := by decide
  rcases family_descends (prefixWord ++ tailWord_8100593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8100670 : List Nat := [4, 2, 1, 2, 3, 1, 1, 2, 3, 4]
def baseStart_8100670 : Nat := 118140960795 + 8100670 * 2 ^ 59
def prefixEnd_8100670 : Nat := 4983230072969 + 3 ^ 40 * 8100670 * 2
def baseEnd_8100670 : Nat := 1386512444485642108356901

theorem tailTrace_8100670 : CollatzResearch.WordTrace tailWord_8100670 prefixEnd_8100670 1386512444485642108356901 := by
  unfold tailWord_8100670
  simp only [CollatzResearch.WordTrace]
  refine ⟨36931963445332943642037433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 196970471708442366090866309 36931963445332943642037433)
  ·
    refine ⟨27698972583999707731528075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36931963445332943642037433 27698972583999707731528075)
    ·
      refine ⟨41548458875999561597292113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27698972583999707731528075 41548458875999561597292113)
      ·
        refine ⟨31161344156999671197969085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41548458875999561597292113 31161344156999671197969085)
        ·
          refine ⟨11685504058874876699238407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31161344156999671197969085 11685504058874876699238407)
          ·
            refine ⟨17528256088312315048857611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11685504058874876699238407 17528256088312315048857611)
            ·
              refine ⟨26292384132468472573286417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17528256088312315048857611 26292384132468472573286417)
              ·
                refine ⟨19719288099351354429964813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26292384132468472573286417 19719288099351354429964813)
                ·
                  refine ⟨7394733037256757911236805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19719288099351354429964813 7394733037256757911236805)
                  ·
                    refine ⟨1386512444485642108356901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7394733037256757911236805 1386512444485642108356901)
                    ·
                      rfl

theorem cell23_8100670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 1, 1, 2, 3, 4].length) (baseStart_8100670 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8100670 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8100670 prefixEnd_8100670 := by exact prefixLift 8100670
  have htrace : WordTrace (prefixWord ++ tailWord_8100670) baseStart_8100670 baseEnd_8100670 := by
    simpa [prefixWord, tailWord_8100670, baseEnd_8100670] using wordTrace_append hprefix tailTrace_8100670
  have hstable : (prefixWord ++ tailWord_8100670).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8100670).length < 2 ^ (prefixWord ++ tailWord_8100670).sum := by decide
  have hdescent : baseEnd_8100670 < baseStart_8100670 := by decide
  rcases family_descends (prefixWord ++ tailWord_8100670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8100693 : List Nat := [1, 3, 2, 2, 2, 1, 1, 2, 5, 1, 3]
def baseStart_8100693 : Nat := 118140960795 + 8100693 * 2 ^ 59
def prefixEnd_8100693 : Nat := 4983230072969 + 3 ^ 40 * 8100693 * 2
def baseEnd_8100693 : Nat := 4159549143511979735083097

theorem tailTrace_8100693 : CollatzResearch.WordTrace tailWord_8100693 prefixEnd_8100693 4159549143511979735083097 := by
  unfold tailWord_8100693
  simp only [CollatzResearch.WordTrace]
  refine ⟨295456546441580224064386733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196971030961053482709591155 295456546441580224064386733)
  ·
    refine ⟨110796204915592584024145025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 295456546441580224064386733 110796204915592584024145025)
    ·
      refine ⟨83097153686694438018108769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110796204915592584024145025 83097153686694438018108769)
      ·
        refine ⟨62322865265020828513581577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83097153686694438018108769 62322865265020828513581577)
        ·
          refine ⟨46742148948765621385186183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62322865265020828513581577 46742148948765621385186183)
          ·
            refine ⟨70113223423148432077779275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46742148948765621385186183 70113223423148432077779275)
            ·
              refine ⟨105169835134722648116668913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70113223423148432077779275 105169835134722648116668913)
              ·
                refine ⟨78877376351041986087501685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 105169835134722648116668913 78877376351041986087501685)
                ·
                  refine ⟨7394754032910186195703283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 78877376351041986087501685 7394754032910186195703283)
                  ·
                    refine ⟨11092131049365279293554925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7394754032910186195703283 11092131049365279293554925)
                    ·
                      refine ⟨4159549143511979735083097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11092131049365279293554925 4159549143511979735083097)
                      ·
                        rfl

theorem cell23_8100693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 1, 2, 5, 1, 3].length) (baseStart_8100693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8100693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8100693 prefixEnd_8100693 := by exact prefixLift 8100693
  have htrace : WordTrace (prefixWord ++ tailWord_8100693) baseStart_8100693 baseEnd_8100693 := by
    simpa [prefixWord, tailWord_8100693, baseEnd_8100693] using wordTrace_append hprefix tailTrace_8100693
  have hstable : (prefixWord ++ tailWord_8100693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8100693).length < 2 ^ (prefixWord ++ tailWord_8100693).sum := by decide
  have hdescent : baseEnd_8100693 < baseStart_8100693 := by decide
  rcases family_descends (prefixWord ++ tailWord_8100693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8100700 : List Nat := [2, 2, 4, 2, 1, 3, 1, 2, 6]
def baseStart_8100700 : Nat := 118140960795 + 8100700 * 2 ^ 59
def prefixEnd_8100700 : Nat := 4983230072969 + 3 ^ 40 * 8100700 * 2
def baseEnd_8100700 : Nat := 462172526430729023077285

theorem tailTrace_8100700 : CollatzResearch.WordTrace tailWord_8100700 prefixEnd_8100700 462172526430729023077285 := by
  unfold tailWord_8100700
  simp only [CollatzResearch.WordTrace]
  refine ⟨147728400876277432129945777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196971201168369909506594369 147728400876277432129945777)
  ·
    refine ⟨110796300657208074097459333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147728400876277432129945777 110796300657208074097459333)
    ·
      refine ⟨20774306373226513893273625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 110796300657208074097459333 20774306373226513893273625)
      ·
        refine ⟨15580729779919885419955219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20774306373226513893273625 15580729779919885419955219)
        ·
          refine ⟨23371094669879828129932829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15580729779919885419955219 23371094669879828129932829)
          ·
            refine ⟨8764160501204935548724811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23371094669879828129932829 8764160501204935548724811)
            ·
              refine ⟨13146240751807403323087217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8764160501204935548724811 13146240751807403323087217)
              ·
                refine ⟨9859680563855552492315413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13146240751807403323087217 9859680563855552492315413)
                ·
                  refine ⟨462172526430729023077285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9859680563855552492315413 462172526430729023077285)
                  ·
                    rfl

theorem cell23_8100700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 3, 1, 2, 6].length) (baseStart_8100700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8100700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8100700 prefixEnd_8100700 := by exact prefixLift 8100700
  have htrace : WordTrace (prefixWord ++ tailWord_8100700) baseStart_8100700 baseEnd_8100700 := by
    simpa [prefixWord, tailWord_8100700, baseEnd_8100700] using wordTrace_append hprefix tailTrace_8100700
  have hstable : (prefixWord ++ tailWord_8100700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8100700).length < 2 ^ (prefixWord ++ tailWord_8100700).sum := by decide
  have hdescent : baseEnd_8100700 < baseStart_8100700 := by decide
  rcases family_descends (prefixWord ++ tailWord_8100700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8100703 : List Nat := [1, 1, 2, 3, 1, 3, 2, 1, 4, 3, 2]
def baseStart_8100703 : Nat := 118140960795 + 8100703 * 2 ^ 59
def prefixEnd_8100703 : Nat := 4983230072969 + 3 ^ 40 * 8100703 * 2
def baseEnd_8100703 : Nat := 4159554278318524695958051

theorem tailTrace_8100703 : CollatzResearch.WordTrace tailWord_8100703 prefixEnd_8100703 4159554278318524695958051 := by
  unfold tailWord_8100703
  simp only [CollatzResearch.WordTrace]
  refine ⟨295456911171543995772250763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196971274114362663848167175 295456911171543995772250763)
  ·
    refine ⟨443185366757315993658376145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 295456911171543995772250763 443185366757315993658376145)
    ·
      refine ⟨332389025067986995243782109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 443185366757315993658376145 332389025067986995243782109)
      ·
        refine ⟨124645884400495123216418291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 332389025067986995243782109 124645884400495123216418291)
        ·
          refine ⟨186968826600742684824627437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124645884400495123216418291 186968826600742684824627437)
          ·
            refine ⟨70113309975278506809235289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 186968826600742684824627437 70113309975278506809235289)
            ·
              refine ⟨52584982481458880106926467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70113309975278506809235289 52584982481458880106926467)
              ·
                refine ⟨78877473722188320160389701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52584982481458880106926467 78877473722188320160389701)
                ·
                  refine ⟨14789526322910310030073069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 78877473722188320160389701 14789526322910310030073069)
                  ·
                    refine ⟨5546072371091366261277401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14789526322910310030073069 5546072371091366261277401)
                    ·
                      refine ⟨4159554278318524695958051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5546072371091366261277401 4159554278318524695958051)
                      ·
                        rfl

theorem cell23_8100703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 2, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 2, 1, 4, 3, 2].length) (baseStart_8100703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8100703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8100703 prefixEnd_8100703 := by exact prefixLift 8100703
  have htrace : WordTrace (prefixWord ++ tailWord_8100703) baseStart_8100703 baseEnd_8100703 := by
    simpa [prefixWord, tailWord_8100703, baseEnd_8100703] using wordTrace_append hprefix tailTrace_8100703
  have hstable : (prefixWord ++ tailWord_8100703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8100703).length < 2 ^ (prefixWord ++ tailWord_8100703).sum := by decide
  have hdescent : baseEnd_8100703 < baseStart_8100703 := by decide
  rcases family_descends (prefixWord ++ tailWord_8100703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8100733 : List Nat := [1, 4, 1, 1, 2, 1, 3, 4, 1, 1, 4]
def baseStart_8100733 : Nat := 118140960795 + 8100733 * 2 ^ 59
def prefixEnd_8100733 : Nat := 4983230072969 + 3 ^ 40 * 8100733 * 2
def baseEnd_8100733 : Nat := 4159569682738159578582913

theorem tailTrace_8100733 : CollatzResearch.WordTrace tailWord_8100733 prefixEnd_8100733 4159569682738159578582913 := by
  unfold tailWord_8100733
  simp only [CollatzResearch.WordTrace]
  refine ⟨295458005361435310895842853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196972003574290207263895235 295458005361435310895842853)
  ·
    refine ⟨55398376005269120792970535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 295458005361435310895842853 55398376005269120792970535)
    ·
      refine ⟨83097564007903681189455803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55398376005269120792970535 83097564007903681189455803)
      ·
        refine ⟨124646346011855521784183705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83097564007903681189455803 124646346011855521784183705)
        ·
          refine ⟨93484759508891641338137779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 124646346011855521784183705 93484759508891641338137779)
          ·
            refine ⟨140227139263337462007206669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93484759508891641338137779 140227139263337462007206669)
            ·
              refine ⟨52585177223751548252702501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 140227139263337462007206669 52585177223751548252702501)
              ·
                refine ⟨9859720729453415297381719, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 52585177223751548252702501 9859720729453415297381719)
                ·
                  refine ⟨14789581094180122946072579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9859720729453415297381719 14789581094180122946072579)
                  ·
                    refine ⟨22184371641270184419108869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14789581094180122946072579 22184371641270184419108869)
                    ·
                      refine ⟨4159569682738159578582913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22184371641270184419108869 4159569682738159578582913)
                      ·
                        rfl

theorem cell23_8100733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 3, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 3, 4, 1, 1, 4].length) (baseStart_8100733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8100733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8100733 prefixEnd_8100733 := by exact prefixLift 8100733
  have htrace : WordTrace (prefixWord ++ tailWord_8100733) baseStart_8100733 baseEnd_8100733 := by
    simpa [prefixWord, tailWord_8100733, baseEnd_8100733] using wordTrace_append hprefix tailTrace_8100733
  have hstable : (prefixWord ++ tailWord_8100733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8100733).length < 2 ^ (prefixWord ++ tailWord_8100733).sum := by decide
  have hdescent : baseEnd_8100733 < baseStart_8100733 := by decide
  rcases family_descends (prefixWord ++ tailWord_8100733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8100738 : List Nat := [3, 4, 2, 2, 2, 1, 1, 3, 1, 4]
def baseStart_8100738 : Nat := 118140960795 + 8100738 * 2 ^ 59
def prefixEnd_8100738 : Nat := 4983230072969 + 3 ^ 40 * 8100738 * 2
def baseEnd_8100738 : Nat := 1386524083380477353006797

theorem tailTrace_8100738 : CollatzResearch.WordTrace tailWord_8100738 prefixEnd_8100738 1386524083380477353006797 := by
  unfold tailWord_8100738
  simp only [CollatzResearch.WordTrace]
  refine ⟨73864546931604299187443717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 196972125150944797833183245 73864546931604299187443717)
  ·
    refine ⟨13849602549675806097645697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 73864546931604299187443717 13849602549675806097645697)
    ·
      refine ⟨10387201912256854573234273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13849602549675806097645697 10387201912256854573234273)
      ·
        refine ⟨7790401434192640929925705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10387201912256854573234273 7790401434192640929925705)
        ·
          refine ⟨5842801075644480697444279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7790401434192640929925705 5842801075644480697444279)
          ·
            refine ⟨8764201613466721046166419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5842801075644480697444279 8764201613466721046166419)
            ·
              refine ⟨13146302420200081569249629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8764201613466721046166419 13146302420200081569249629)
              ·
                refine ⟨4929863407575030588468611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13146302420200081569249629 4929863407575030588468611)
                ·
                  refine ⟨7394795111362545882702917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4929863407575030588468611 7394795111362545882702917)
                  ·
                    refine ⟨1386524083380477353006797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7394795111362545882702917 1386524083380477353006797)
                    ·
                      rfl

theorem cell23_8100738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 2, 1, 1, 3, 1, 4].length) (baseStart_8100738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8100738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8100738 prefixEnd_8100738 := by exact prefixLift 8100738
  have htrace : WordTrace (prefixWord ++ tailWord_8100738) baseStart_8100738 baseEnd_8100738 := by
    simpa [prefixWord, tailWord_8100738, baseEnd_8100738] using wordTrace_append hprefix tailTrace_8100738
  have hstable : (prefixWord ++ tailWord_8100738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8100738).length < 2 ^ (prefixWord ++ tailWord_8100738).sum := by decide
  have hdescent : baseEnd_8100738 < baseStart_8100738 := by decide
  rcases family_descends (prefixWord ++ tailWord_8100738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8100743 : List Nat := [1, 1, 4, 2, 3, 1, 1, 2, 4, 4]
def baseStart_8100743 : Nat := 118140960795 + 8100743 * 2 ^ 59
def prefixEnd_8100743 : Nat := 4983230072969 + 3 ^ 40 * 8100743 * 2
def baseEnd_8100743 : Nat := 1386524939181568179819289

theorem tailTrace_8100743 : CollatzResearch.WordTrace tailWord_8100743 prefixEnd_8100743 1386524939181568179819289 := by
  unfold tailWord_8100743
  simp only [CollatzResearch.WordTrace]
  refine ⟨295458370091399082603706883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196972246727599388402471255 295458370091399082603706883)
  ·
    refine ⟨443187555137098623905560325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 295458370091399082603706883 443187555137098623905560325)
    ·
      refine ⟨83097666588205991982292561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 443187555137098623905560325 83097666588205991982292561)
      ·
        refine ⟨62323249941154493986719421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83097666588205991982292561 62323249941154493986719421)
        ·
          refine ⟨23371218727932935245019783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62323249941154493986719421 23371218727932935245019783)
          ·
            refine ⟨35056828091899402867529675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23371218727932935245019783 35056828091899402867529675)
            ·
              refine ⟨52585242137849104301294513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35056828091899402867529675 52585242137849104301294513)
              ·
                refine ⟨39438931603386828225970885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52585242137849104301294513 39438931603386828225970885)
                ·
                  refine ⟨7394799675635030292369541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39438931603386828225970885 7394799675635030292369541)
                  ·
                    refine ⟨1386524939181568179819289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7394799675635030292369541 1386524939181568179819289)
                    ·
                      rfl

theorem cell23_8100743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 1, 2, 4, 4].length) (baseStart_8100743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8100743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8100743 prefixEnd_8100743 := by exact prefixLift 8100743
  have htrace : WordTrace (prefixWord ++ tailWord_8100743) baseStart_8100743 baseEnd_8100743 := by
    simpa [prefixWord, tailWord_8100743, baseEnd_8100743] using wordTrace_append hprefix tailTrace_8100743
  have hstable : (prefixWord ++ tailWord_8100743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8100743).length < 2 ^ (prefixWord ++ tailWord_8100743).sum := by decide
  have hdescent : baseEnd_8100743 < baseStart_8100743 := by decide
  rcases family_descends (prefixWord ++ tailWord_8100743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8100744 : List Nat := [2, 1, 3, 3, 2, 3, 1, 3, 1, 1, 3]
def baseStart_8100744 : Nat := 118140960795 + 8100744 * 2 ^ 59
def prefixEnd_8100744 : Nat := 4983230072969 + 3 ^ 40 * 8100744 * 2
def baseEnd_8100744 : Nat := 4159575331025359035545363

theorem tailTrace_8100744 : CollatzResearch.WordTrace tailWord_8100744 prefixEnd_8100744 4159575331025359035545363 := by
  unfold tailWord_8100744
  simp only [CollatzResearch.WordTrace]
  refine ⟨147729203282197729887246643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196972271042930306516328857 147729203282197729887246643)
  ·
    refine ⟨221593804923296594830869965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147729203282197729887246643 221593804923296594830869965)
    ·
      refine ⟨83097676846236223061576237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 221593804923296594830869965 83097676846236223061576237)
      ·
        refine ⟨31161628817338583648091089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 83097676846236223061576237 31161628817338583648091089)
        ·
          refine ⟨23371221613003937736068317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31161628817338583648091089 23371221613003937736068317)
          ·
            refine ⟨8764208104876476651025619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23371221613003937736068317 8764208104876476651025619)
            ·
              refine ⟨13146312157314714976538429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8764208104876476651025619 13146312157314714976538429)
              ·
                refine ⟨4929867058993018116201911, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13146312157314714976538429 4929867058993018116201911)
                ·
                  refine ⟨7394800588489527174302867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4929867058993018116201911 7394800588489527174302867)
                  ·
                    refine ⟨11092200882734290761454301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7394800588489527174302867 11092200882734290761454301)
                    ·
                      refine ⟨4159575331025359035545363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11092200882734290761454301 4159575331025359035545363)
                      ·
                        rfl

theorem cell23_8100744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 3, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 3, 1, 3, 1, 1, 3].length) (baseStart_8100744 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8100744 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8100744 prefixEnd_8100744 := by exact prefixLift 8100744
  have htrace : WordTrace (prefixWord ++ tailWord_8100744) baseStart_8100744 baseEnd_8100744 := by
    simpa [prefixWord, tailWord_8100744, baseEnd_8100744] using wordTrace_append hprefix tailTrace_8100744
  have hstable : (prefixWord ++ tailWord_8100744).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8100744).length < 2 ^ (prefixWord ++ tailWord_8100744).sum := by decide
  have hdescent : baseEnd_8100744 < baseStart_8100744 := by decide
  rcases family_descends (prefixWord ++ tailWord_8100744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8100767 : List Nat := [1, 1, 2, 5, 2, 1, 3, 1, 3, 2, 2]
def baseStart_8100767 : Nat := 118140960795 + 8100767 * 2 ^ 59
def prefixEnd_8100767 : Nat := 4983230072969 + 3 ^ 40 * 8100767 * 2
def baseEnd_8100767 : Nat := 4159587141080412445557757

theorem tailTrace_8100767 : CollatzResearch.WordTrace tailWord_8100767 prefixEnd_8100767 4159587141080412445557757 := by
  unfold tailWord_8100767
  simp only [CollatzResearch.WordTrace]
  refine ⟨295459245443312134702580555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196972830295541423135053703 295459245443312134702580555)
  ·
    refine ⟨443188868164968202053870833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 295459245443312134702580555 443188868164968202053870833)
    ·
      refine ⟨332391651123726151540403125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 443188868164968202053870833 332391651123726151540403125)
      ·
        refine ⟨31161717292849326706912793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 332391651123726151540403125 31161717292849326706912793)
        ·
          refine ⟨23371287969636995030184595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31161717292849326706912793 23371287969636995030184595)
          ·
            refine ⟨35056931954455492545276893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23371287969636995030184595 35056931954455492545276893)
            ·
              refine ⟨13146349482920809704478835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35056931954455492545276893 13146349482920809704478835)
              ·
                refine ⟨19719524224381214556718253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13146349482920809704478835 19719524224381214556718253)
                ·
                  refine ⟨7394821584142955458769345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19719524224381214556718253 7394821584142955458769345)
                  ·
                    refine ⟨5546116188107216594077009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7394821584142955458769345 5546116188107216594077009)
                    ·
                      refine ⟨4159587141080412445557757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5546116188107216594077009 4159587141080412445557757)
                      ·
                        rfl

theorem cell23_8100767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 3, 1, 3, 2, 2].length) (baseStart_8100767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8100767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8100767 prefixEnd_8100767 := by exact prefixLift 8100767
  have htrace : WordTrace (prefixWord ++ tailWord_8100767) baseStart_8100767 baseEnd_8100767 := by
    simpa [prefixWord, tailWord_8100767, baseEnd_8100767] using wordTrace_append hprefix tailTrace_8100767
  have hstable : (prefixWord ++ tailWord_8100767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8100767).length < 2 ^ (prefixWord ++ tailWord_8100767).sum := by decide
  have hdescent : baseEnd_8100767 < baseStart_8100767 := by decide
  rcases family_descends (prefixWord ++ tailWord_8100767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8100783 : List Nat := [1, 1, 2, 1, 2, 2, 2, 2, 6, 1, 3]
def baseStart_8100783 : Nat := 118140960795 + 8100783 * 2 ^ 59
def prefixEnd_8100783 : Nat := 4983230072969 + 3 ^ 40 * 8100783 * 2
def baseEnd_8100783 : Nat := 4159595356770884382957683

theorem tailTrace_8100783 : CollatzResearch.WordTrace tailWord_8100783 prefixEnd_8100783 4159595356770884382957683 := by
  unfold tailWord_8100783
  simp only [CollatzResearch.WordTrace]
  refine ⟨295459829011254169435163003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196973219340836112956775335 295459829011254169435163003)
  ·
    refine ⟨443189743516881254152744505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 295459829011254169435163003 443189743516881254152744505)
    ·
      refine ⟨332392307637660940614558379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 443189743516881254152744505 332392307637660940614558379)
      ·
        refine ⟨498588461456491410921837569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 332392307637660940614558379 498588461456491410921837569)
        ·
          refine ⟨373941346092368558191378177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 498588461456491410921837569 373941346092368558191378177)
          ·
            refine ⟨280456009569276418643533633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 373941346092368558191378177 280456009569276418643533633)
            ·
              refine ⟨210342007176957313982650225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 280456009569276418643533633 210342007176957313982650225)
              ·
                refine ⟨157756505382717985486987669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 210342007176957313982650225 157756505382717985486987669)
                ·
                  refine ⟨7394836189814905569702547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 157756505382717985486987669 7394836189814905569702547)
                  ·
                    refine ⟨11092254284722358354553821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7394836189814905569702547 11092254284722358354553821)
                    ·
                      refine ⟨4159595356770884382957683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11092254284722358354553821 4159595356770884382957683)
                      ·
                        rfl

theorem cell23_8100783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 2, 6, 1, 3].length) (baseStart_8100783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8100783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8100783 prefixEnd_8100783 := by exact prefixLift 8100783
  have htrace : WordTrace (prefixWord ++ tailWord_8100783) baseStart_8100783 baseEnd_8100783 := by
    simpa [prefixWord, tailWord_8100783, baseEnd_8100783] using wordTrace_append hprefix tailTrace_8100783
  have hstable : (prefixWord ++ tailWord_8100783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8100783).length < 2 ^ (prefixWord ++ tailWord_8100783).sum := by decide
  have hdescent : baseEnd_8100783 < baseStart_8100783 := by decide
  rcases family_descends (prefixWord ++ tailWord_8100783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8100804 : List Nat := [2, 3, 3, 3, 2, 1, 1, 1, 1, 1, 5]
def baseStart_8100804 : Nat := 118140960795 + 8100804 * 2 ^ 59
def prefixEnd_8100804 : Nat := 4983230072969 + 3 ^ 40 * 8100804 * 2
def baseEnd_8100804 : Nat := 4159606139864628800795087

theorem tailTrace_8100804 : CollatzResearch.WordTrace tailWord_8100804 prefixEnd_8100804 4159606139864628800795087 := by
  unfold tailWord_8100804
  simp only [CollatzResearch.WordTrace]
  refine ⟨147730297472089045010838733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196973729962785393347784977 147730297472089045010838733)
  ·
    refine ⟨55398861552033391879064525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 147730297472089045010838733 55398861552033391879064525)
    ·
      refine ⟨20774573082012521954649197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55398861552033391879064525 20774573082012521954649197)
      ·
        refine ⟨7790464905754695732993449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20774573082012521954649197 7790464905754695732993449)
        ·
          refine ⟨5842848679316021799745087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7790464905754695732993449 5842848679316021799745087)
          ·
            refine ⟨8764273018974032699617631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5842848679316021799745087 8764273018974032699617631)
            ·
              refine ⟨13146409528461049049426447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8764273018974032699617631 13146409528461049049426447)
              ·
                refine ⟨19719614292691573574139671, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13146409528461049049426447 19719614292691573574139671)
                ·
                  refine ⟨29579421439037360361209507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19719614292691573574139671 29579421439037360361209507)
                  ·
                    refine ⟨44369132158556040541814261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29579421439037360361209507 44369132158556040541814261)
                    ·
                      refine ⟨4159606139864628800795087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44369132158556040541814261 4159606139864628800795087)
                      ·
                        rfl

theorem cell23_8100804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 2, 1, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 2, 1, 1, 1, 1, 1, 5].length) (baseStart_8100804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8100804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8100804 prefixEnd_8100804 := by exact prefixLift 8100804
  have htrace : WordTrace (prefixWord ++ tailWord_8100804) baseStart_8100804 baseEnd_8100804 := by
    simpa [prefixWord, tailWord_8100804, baseEnd_8100804] using wordTrace_append hprefix tailTrace_8100804
  have hstable : (prefixWord ++ tailWord_8100804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8100804).length < 2 ^ (prefixWord ++ tailWord_8100804).sum := by decide
  have hdescent : baseEnd_8100804 < baseStart_8100804 := by decide
  rcases family_descends (prefixWord ++ tailWord_8100804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8100816 : List Nat := [2, 1, 1, 1, 1, 2, 3, 4, 2, 6]
def baseStart_8100816 : Nat := 118140960795 + 8100816 * 2 ^ 59
def prefixEnd_8100816 : Nat := 4983230072969 + 3 ^ 40 * 8100816 * 2
def baseEnd_8100816 : Nat := 1386537433877494251281677

theorem tailTrace_8100816 : CollatzResearch.WordTrace tailWord_8100816 prefixEnd_8100816 1386537433877494251281677 := by
  unfold tailWord_8100816
  simp only [CollatzResearch.WordTrace]
  refine ⟨147730516310067308035557151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196974021746756410714076201 147730516310067308035557151)
  ·
    refine ⟨221595774465100962053335727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147730516310067308035557151 221595774465100962053335727)
    ·
      refine ⟨332393661697651443080003591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 221595774465100962053335727 332393661697651443080003591)
      ·
        refine ⟨498590492546477164620005387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 332393661697651443080003591 498590492546477164620005387)
        ·
          refine ⟨747885738819715746930008081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 498590492546477164620005387 747885738819715746930008081)
          ·
            refine ⟨560914304114786810197506061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 747885738819715746930008081 560914304114786810197506061)
            ·
              refine ⟨210342864043045053824064773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 560914304114786810197506061 210342864043045053824064773)
              ·
                refine ⟨39439287008070947592012145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 210342864043045053824064773 39439287008070947592012145)
                ·
                  refine ⟨29579465256053210694009109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39439287008070947592012145 29579465256053210694009109)
                  ·
                    refine ⟨1386537433877494251281677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29579465256053210694009109 1386537433877494251281677)
                    ·
                      rfl

theorem cell23_8100816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 4, 2, 6].length) (baseStart_8100816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8100816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8100816 prefixEnd_8100816 := by exact prefixLift 8100816
  have htrace : WordTrace (prefixWord ++ tailWord_8100816) baseStart_8100816 baseEnd_8100816 := by
    simpa [prefixWord, tailWord_8100816, baseEnd_8100816] using wordTrace_append hprefix tailTrace_8100816
  have hstable : (prefixWord ++ tailWord_8100816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8100816).length < 2 ^ (prefixWord ++ tailWord_8100816).sum := by decide
  have hdescent : baseEnd_8100816 < baseStart_8100816 := by decide
  rcases family_descends (prefixWord ++ tailWord_8100816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8100818 : List Nat := [3, 2, 2, 3, 1, 3, 2, 2, 1, 2, 2]
def baseStart_8100818 : Nat := 118140960795 + 8100818 * 2 ^ 59
def prefixEnd_8100818 : Nat := 4983230072969 + 3 ^ 40 * 8100818 * 2
def baseEnd_8100818 : Nat := 4159613328593791746020023

theorem tailTrace_8100818 : CollatzResearch.WordTrace tailWord_8100818 prefixEnd_8100818 4159613328593791746020023 := by
  unfold tailWord_8100818
  simp only [CollatzResearch.WordTrace]
  refine ⟨73865276391531842603171777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 196974070377418246941791405 73865276391531842603171777)
  ·
    refine ⟨55398957293648881952378833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73865276391531842603171777 55398957293648881952378833)
    ·
      refine ⟨41549217970236661464284125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55398957293648881952378833 41549217970236661464284125)
      ·
        refine ⟨15580956738838748049106547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41549217970236661464284125 15580956738838748049106547)
        ·
          refine ⟨23371435108258122073659821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15580956738838748049106547 23371435108258122073659821)
          ·
            refine ⟨8764288165596795777622433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23371435108258122073659821 8764288165596795777622433)
            ·
              refine ⟨6573216124197596833216825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8764288165596795777622433 6573216124197596833216825)
              ·
                refine ⟨4929912093148197624912619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6573216124197596833216825 4929912093148197624912619)
                ·
                  refine ⟨7394868139722296437368929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4929912093148197624912619 7394868139722296437368929)
                  ·
                    refine ⟨5546151104791722328026697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7394868139722296437368929 5546151104791722328026697)
                    ·
                      refine ⟨4159613328593791746020023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5546151104791722328026697 4159613328593791746020023)
                      ·
                        rfl

theorem cell23_8100818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 3, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 3, 2, 2, 1, 2, 2].length) (baseStart_8100818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8100818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8100818 prefixEnd_8100818 := by exact prefixLift 8100818
  have htrace : WordTrace (prefixWord ++ tailWord_8100818) baseStart_8100818 baseEnd_8100818 := by
    simpa [prefixWord, tailWord_8100818, baseEnd_8100818] using wordTrace_append hprefix tailTrace_8100818
  have hstable : (prefixWord ++ tailWord_8100818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8100818).length < 2 ^ (prefixWord ++ tailWord_8100818).sum := by decide
  have hdescent : baseEnd_8100818 < baseStart_8100818 := by decide
  rcases family_descends (prefixWord ++ tailWord_8100818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8100834 : List Nat := [3, 3, 3, 1, 1, 1, 2, 3, 2, 1, 3]
def baseStart_8100834 : Nat := 118140960795 + 8100834 * 2 ^ 59
def prefixEnd_8100834 : Nat := 4983230072969 + 3 ^ 40 * 8100834 * 2
def baseEnd_8100834 : Nat := 4159621544284263683419949

theorem tailTrace_8100834 : CollatzResearch.WordTrace tailWord_8100834 prefixEnd_8100834 4159621544284263683419949 := by
  unfold tailWord_8100834
  simp only [CollatzResearch.WordTrace]
  refine ⟨73865422283517351286317389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 196974459422712936763513037 73865422283517351286317389)
  ·
    refine ⟨27699533356319006732369021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73865422283517351286317389 27699533356319006732369021)
    ·
      refine ⟨10387325008619627524638383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27699533356319006732369021 10387325008619627524638383)
      ·
        refine ⟨15580987512929441286957575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10387325008619627524638383 15580987512929441286957575)
        ·
          refine ⟨23371481269394161930436363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15580987512929441286957575 23371481269394161930436363)
          ·
            refine ⟨35057221904091242895654545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23371481269394161930436363 35057221904091242895654545)
            ·
              refine ⟨26292916428068432171740909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35057221904091242895654545 26292916428068432171740909)
              ·
                refine ⟨9859843660525662064402841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26292916428068432171740909 9859843660525662064402841)
                ·
                  refine ⟨7394882745394246548302131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9859843660525662064402841 7394882745394246548302131)
                  ·
                    refine ⟨11092324118091369822453197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7394882745394246548302131 11092324118091369822453197)
                    ·
                      refine ⟨4159621544284263683419949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11092324118091369822453197 4159621544284263683419949)
                      ·
                        rfl

theorem cell23_8100834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 2, 3, 2, 1, 3].length) (baseStart_8100834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8100834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8100834 prefixEnd_8100834 := by exact prefixLift 8100834
  have htrace : WordTrace (prefixWord ++ tailWord_8100834) baseStart_8100834 baseEnd_8100834 := by
    simpa [prefixWord, tailWord_8100834, baseEnd_8100834] using wordTrace_append hprefix tailTrace_8100834
  have hstable : (prefixWord ++ tailWord_8100834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8100834).length < 2 ^ (prefixWord ++ tailWord_8100834).sum := by decide
  have hdescent : baseEnd_8100834 < baseStart_8100834 := by decide
  rcases family_descends (prefixWord ++ tailWord_8100834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8100840 : List Nat := [2, 1, 4, 1, 1, 1, 3, 3, 1, 4, 2]
def baseStart_8100840 : Nat := 118140960795 + 8100840 * 2 ^ 59
def prefixEnd_8100840 : Nat := 4983230072969 + 3 ^ 40 * 8100840 * 2
def baseEnd_8100840 : Nat := 4159624625168190659944921

theorem tailTrace_8100840 : CollatzResearch.WordTrace tailWord_8100840 prefixEnd_8100840 4159624625168190659944921 := by
  unfold tailWord_8100840
  simp only [CollatzResearch.WordTrace]
  refine ⟨147730953986023834084993987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196974605314698445446658649 147730953986023834084993987)
  ·
    refine ⟨221596430979035751127490981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147730953986023834084993987 221596430979035751127490981)
    ·
      refine ⟨41549330808569203336404559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 221596430979035751127490981 41549330808569203336404559)
      ·
        refine ⟨62323996212853805004606839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41549330808569203336404559 62323996212853805004606839)
        ·
          refine ⟨93485994319280707506910259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62323996212853805004606839 93485994319280707506910259)
          ·
            refine ⟨140228991478921061260365389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93485994319280707506910259 140228991478921061260365389)
            ·
              refine ⟨52585871804595397972637021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 140228991478921061260365389 52585871804595397972637021)
              ·
                refine ⟨19719701926723274239738883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52585871804595397972637021 19719701926723274239738883)
                ·
                  refine ⟨29579552890084911359608325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19719701926723274239738883 29579552890084911359608325)
                  ·
                    refine ⟨5546166166890920879926561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29579552890084911359608325 5546166166890920879926561)
                    ·
                      refine ⟨4159624625168190659944921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5546166166890920879926561 4159624625168190659944921)
                      ·
                        rfl

theorem cell23_8100840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 3, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 3, 3, 1, 4, 2].length) (baseStart_8100840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8100840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8100840 prefixEnd_8100840 := by exact prefixLift 8100840
  have htrace : WordTrace (prefixWord ++ tailWord_8100840) baseStart_8100840 baseEnd_8100840 := by
    simpa [prefixWord, tailWord_8100840, baseEnd_8100840] using wordTrace_append hprefix tailTrace_8100840
  have hstable : (prefixWord ++ tailWord_8100840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8100840).length < 2 ^ (prefixWord ++ tailWord_8100840).sum := by decide
  have hdescent : baseEnd_8100840 < baseStart_8100840 := by decide
  rcases family_descends (prefixWord ++ tailWord_8100840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8100852 : List Nat := [2, 6, 2, 1, 1, 1, 2, 3, 1, 2, 2]
def baseStart_8100852 : Nat := 118140960795 + 8100852 * 2 ^ 59
def prefixEnd_8100852 : Nat := 4983230072969 + 3 ^ 40 * 8100852 * 2
def baseEnd_8100852 : Nat := 4159630786936044612994867

theorem tailTrace_8100852 : CollatzResearch.WordTrace tailWord_8100852 prefixEnd_8100852 4159630786936044612994867 := by
  unfold tailWord_8100852
  simp only [CollatzResearch.WordTrace]
  refine ⟨147731172824002097109712405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196974897098669462812949873 147731172824002097109712405)
  ·
    refine ⟨6924898726125098302017769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 147731172824002097109712405 6924898726125098302017769)
    ·
      refine ⟨5193674044593823726513327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6924898726125098302017769 5193674044593823726513327)
      ·
        refine ⟨7790511066890735589769991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5193674044593823726513327 7790511066890735589769991)
        ·
          refine ⟨11685766600336103384654987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7790511066890735589769991 11685766600336103384654987)
          ·
            refine ⟨17528649900504155076982481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11685766600336103384654987 17528649900504155076982481)
            ·
              refine ⟨13146487425378116307736861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17528649900504155076982481 13146487425378116307736861)
              ·
                refine ⟨4929932784516793615401323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13146487425378116307736861 4929932784516793615401323)
                ·
                  refine ⟨7394899176775190423101985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4929932784516793615401323 7394899176775190423101985)
                  ·
                    refine ⟨5546174382581392817326489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7394899176775190423101985 5546174382581392817326489)
                    ·
                      refine ⟨4159630786936044612994867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5546174382581392817326489 4159630786936044612994867)
                      ·
                        rfl

theorem cell23_8100852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 1, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 1, 2, 3, 1, 2, 2].length) (baseStart_8100852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8100852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8100852 prefixEnd_8100852 := by exact prefixLift 8100852
  have htrace : WordTrace (prefixWord ++ tailWord_8100852) baseStart_8100852 baseEnd_8100852 := by
    simpa [prefixWord, tailWord_8100852, baseEnd_8100852] using wordTrace_append hprefix tailTrace_8100852
  have hstable : (prefixWord ++ tailWord_8100852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8100852).length < 2 ^ (prefixWord ++ tailWord_8100852).sum := by decide
  have hdescent : baseEnd_8100852 < baseStart_8100852 := by decide
  rcases family_descends (prefixWord ++ tailWord_8100852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8100856 : List Nat := [2, 1, 2, 1, 1, 3, 1, 2, 1, 2, 7]
def baseStart_8100856 : Nat := 118140960795 + 8100856 * 2 ^ 59
def prefixEnd_8100856 : Nat := 4983230072969 + 3 ^ 40 * 8100856 * 2
def baseEnd_8100856 : Nat := 4159632840858662597344847

theorem tailTrace_8100856 : CollatzResearch.WordTrace tailWord_8100856 prefixEnd_8100856 4159632840858662597344847 := by
  unfold tailWord_8100856
  simp only [CollatzResearch.WordTrace]
  refine ⟨147731245769994851451285211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196974994359993135268380281 147731245769994851451285211)
  ·
    refine ⟨221596868654992277176927817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147731245769994851451285211 221596868654992277176927817)
    ·
      refine ⟨166197651491244207882695863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 221596868654992277176927817 166197651491244207882695863)
      ·
        refine ⟨249296477236866311824043795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166197651491244207882695863 249296477236866311824043795)
        ·
          refine ⟨373944715855299467736065693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 249296477236866311824043795 373944715855299467736065693)
          ·
            refine ⟨140229268445737300401024635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 373944715855299467736065693 140229268445737300401024635)
            ·
              refine ⟨210343902668605950601536953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 140229268445737300401024635 210343902668605950601536953)
              ·
                refine ⟨157757927001454462951152715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 210343902668605950601536953 157757927001454462951152715)
                ·
                  refine ⟨236636890502181694426729073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 157757927001454462951152715 236636890502181694426729073)
                  ·
                    refine ⟨177477667876636270820046805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 236636890502181694426729073 177477667876636270820046805)
                    ·
                      refine ⟨4159632840858662597344847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 177477667876636270820046805 4159632840858662597344847)
                      ·
                        rfl

theorem cell23_8100856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 2, 1, 2, 7].length) (baseStart_8100856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8100856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8100856 prefixEnd_8100856 := by exact prefixLift 8100856
  have htrace : WordTrace (prefixWord ++ tailWord_8100856) baseStart_8100856 baseEnd_8100856 := by
    simpa [prefixWord, tailWord_8100856, baseEnd_8100856] using wordTrace_append hprefix tailTrace_8100856
  have hstable : (prefixWord ++ tailWord_8100856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8100856).length < 2 ^ (prefixWord ++ tailWord_8100856).sum := by decide
  have hdescent : baseEnd_8100856 < baseStart_8100856 := by decide
  rcases family_descends (prefixWord ++ tailWord_8100856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8100874 : List Nat := [3, 1, 2, 2, 3, 1, 3, 2, 2, 2, 2]
def baseStart_8100874 : Nat := 118140960795 + 8100874 * 2 ^ 59
def prefixEnd_8100874 : Nat := 4983230072969 + 3 ^ 40 * 8100874 * 2
def baseEnd_8100874 : Nat := 4159642083510443526919765

theorem tailTrace_8100874 : CollatzResearch.WordTrace tailWord_8100874 prefixEnd_8100874 4159642083510443526919765 := by
  unfold tailWord_8100874
  simp only [CollatzResearch.WordTrace]
  refine ⟨73865787013481122994181419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 196975432035949661317817117 73865787013481122994181419)
  ·
    refine ⟨110798680520221684491272129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73865787013481122994181419 110798680520221684491272129)
    ·
      refine ⟨83099010390166263368454097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110798680520221684491272129 83099010390166263368454097)
      ·
        refine ⟨62324257792624697526340573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83099010390166263368454097 62324257792624697526340573)
        ·
          refine ⟨23371596672234261572377715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62324257792624697526340573 23371596672234261572377715)
          ·
            refine ⟨35057395008351392358566573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23371596672234261572377715 35057395008351392358566573)
            ·
              refine ⟨13146523128131772134462465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35057395008351392358566573 13146523128131772134462465)
              ·
                refine ⟨9859892346098829100846849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13146523128131772134462465 9859892346098829100846849)
                ·
                  refine ⟨7394919259574121825635137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9859892346098829100846849 7394919259574121825635137)
                  ·
                    refine ⟨5546189444680591369226353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7394919259574121825635137 5546189444680591369226353)
                    ·
                      refine ⟨4159642083510443526919765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5546189444680591369226353 4159642083510443526919765)
                      ·
                        rfl

theorem cell23_8100874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 3, 2, 2, 2, 2].length) (baseStart_8100874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8100874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8100874 prefixEnd_8100874 := by exact prefixLift 8100874
  have htrace : WordTrace (prefixWord ++ tailWord_8100874) baseStart_8100874 baseEnd_8100874 := by
    simpa [prefixWord, tailWord_8100874, baseEnd_8100874] using wordTrace_append hprefix tailTrace_8100874
  have hstable : (prefixWord ++ tailWord_8100874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8100874).length < 2 ^ (prefixWord ++ tailWord_8100874).sum := by decide
  have hdescent : baseEnd_8100874 < baseStart_8100874 := by decide
  rcases family_descends (prefixWord ++ tailWord_8100874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8100910 : List Nat := [4, 1, 3, 1, 1, 1, 2, 3, 2, 5]
def baseStart_8100910 : Nat := 118140960795 + 8100910 * 2 ^ 59
def prefixEnd_8100910 : Nat := 4983230072969 + 3 ^ 40 * 8100910 * 2
def baseEnd_8100910 : Nat := 1386553522938001795356533

theorem tailTrace_8100910 : CollatzResearch.WordTrace tailWord_8100910 prefixEnd_8100910 1386553522938001795356533 := by
  unfold tailWord_8100910
  simp only [CollatzResearch.WordTrace]
  refine ⟨36933057635224258765629523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 196976307387862713416690789 36933057635224258765629523)
  ·
    refine ⟨55399586452836388148444285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36933057635224258765629523 55399586452836388148444285)
    ·
      refine ⟨20774844919813645555666607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55399586452836388148444285 20774844919813645555666607)
      ·
        refine ⟨31162267379720468333499911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20774844919813645555666607 31162267379720468333499911)
        ·
          refine ⟨46743401069580702500249867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31162267379720468333499911 46743401069580702500249867)
          ·
            refine ⟨70115101604371053750374801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46743401069580702500249867 70115101604371053750374801)
            ·
              refine ⟨52586326203278290312781101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70115101604371053750374801 52586326203278290312781101)
              ·
                refine ⟨19719872326229358867292913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52586326203278290312781101 19719872326229358867292913)
                ·
                  refine ⟨14789904244672019150469685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19719872326229358867292913 14789904244672019150469685)
                  ·
                    refine ⟨1386553522938001795356533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14789904244672019150469685 1386553522938001795356533)
                    ·
                      rfl

theorem cell23_8100910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 2, 3, 2, 5].length) (baseStart_8100910 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8100910 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8100910 prefixEnd_8100910 := by exact prefixLift 8100910
  have htrace : WordTrace (prefixWord ++ tailWord_8100910) baseStart_8100910 baseEnd_8100910 := by
    simpa [prefixWord, tailWord_8100910, baseEnd_8100910] using wordTrace_append hprefix tailTrace_8100910
  have hstable : (prefixWord ++ tailWord_8100910).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8100910).length < 2 ^ (prefixWord ++ tailWord_8100910).sum := by decide
  have hdescent : baseEnd_8100910 < baseStart_8100910 := by decide
  rcases family_descends (prefixWord ++ tailWord_8100910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8100913 : List Nat := [1, 2, 2, 3, 1, 2, 1, 3, 1, 3, 4]
def baseStart_8100913 : Nat := 118140960795 + 8100913 * 2 ^ 59
def prefixEnd_8100913 : Nat := 4983230072969 + 3 ^ 40 * 8100913 * 2
def baseEnd_8100913 : Nat := 4159662109255968874332085

theorem tailTrace_8100913 : CollatzResearch.WordTrace tailWord_8100913 prefixEnd_8100913 4159662109255968874332085 := by
  unfold tailWord_8100913
  simp only [CollatzResearch.WordTrace]
  refine ⟨295464570500783201637395393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196976380333855467758263595 295464570500783201637395393)
  ·
    refine ⟨221598427875587401228046545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 295464570500783201637395393 221598427875587401228046545)
    ·
      refine ⟨166198820906690550921034909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 221598427875587401228046545 166198820906690550921034909)
      ·
        refine ⟨62324557840008956595388091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 166198820906690550921034909 62324557840008956595388091)
        ·
          refine ⟨93486836760013434893082137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62324557840008956595388091 93486836760013434893082137)
          ·
            refine ⟨70115127570010076169811603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 93486836760013434893082137 70115127570010076169811603)
            ·
              refine ⟨105172691355015114254717405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70115127570010076169811603 105172691355015114254717405)
              ·
                refine ⟨39439759258130667845519027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 105172691355015114254717405 39439759258130667845519027)
                ·
                  refine ⟨59159638887196001768278541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39439759258130667845519027 59159638887196001768278541)
                  ·
                    refine ⟨22184864582698500663104453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 59159638887196001768278541 22184864582698500663104453)
                    ·
                      refine ⟨4159662109255968874332085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22184864582698500663104453 4159662109255968874332085)
                      ·
                        rfl

theorem cell23_8100913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 1, 3, 1, 3, 4].length) (baseStart_8100913 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8100913 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8100913 prefixEnd_8100913 := by exact prefixLift 8100913
  have htrace : WordTrace (prefixWord ++ tailWord_8100913) baseStart_8100913 baseEnd_8100913 := by
    simpa [prefixWord, tailWord_8100913, baseEnd_8100913] using wordTrace_append hprefix tailTrace_8100913
  have hstable : (prefixWord ++ tailWord_8100913).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8100913).length < 2 ^ (prefixWord ++ tailWord_8100913).sum := by decide
  have hdescent : baseEnd_8100913 < baseStart_8100913 := by decide
  rcases family_descends (prefixWord ++ tailWord_8100913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8100967 : List Nat := [1, 1, 5, 1, 1, 4, 2, 1, 2, 2, 3]
def baseStart_8100967 : Nat := 118140960795 + 8100967 * 2 ^ 59
def prefixEnd_8100967 : Nat := 4983230072969 + 3 ^ 40 * 8100967 * 2
def baseEnd_8100967 : Nat := 4159689837211311663056837

theorem tailTrace_8100967 : CollatzResearch.WordTrace tailWord_8100967 prefixEnd_8100967 4159689837211311663056837 := by
  unfold tailWord_8100967
  simp only [CollatzResearch.WordTrace]
  refine ⟨295466540042587568859861155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196977693361725045906574103 295466540042587568859861155)
  ·
    refine ⟨443199810063881353289791733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 295466540042587568859861155 443199810063881353289791733)
    ·
      refine ⟨41549982193488876870917975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 443199810063881353289791733 41549982193488876870917975)
      ·
        refine ⟨62324973290233315306376963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41549982193488876870917975 62324973290233315306376963)
        ·
          refine ⟨93487459935349972959565445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62324973290233315306376963 93487459935349972959565445)
          ·
            refine ⟨17528898737878119929918521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 93487459935349972959565445 17528898737878119929918521)
            ·
              refine ⟨13146674053408589947438891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17528898737878119929918521 13146674053408589947438891)
              ·
                refine ⟨19720011080112884921158337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13146674053408589947438891 19720011080112884921158337)
                ·
                  refine ⟨14790008310084663690868753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19720011080112884921158337 14790008310084663690868753)
                  ·
                    refine ⟨11092506232563497768151565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14790008310084663690868753 11092506232563497768151565)
                    ·
                      refine ⟨4159689837211311663056837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11092506232563497768151565 4159689837211311663056837)
                      ·
                        rfl

theorem cell23_8100967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 4, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 4, 2, 1, 2, 2, 3].length) (baseStart_8100967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8100967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8100967 prefixEnd_8100967 := by exact prefixLift 8100967
  have htrace : WordTrace (prefixWord ++ tailWord_8100967) baseStart_8100967 baseEnd_8100967 := by
    simpa [prefixWord, tailWord_8100967, baseEnd_8100967] using wordTrace_append hprefix tailTrace_8100967
  have hstable : (prefixWord ++ tailWord_8100967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8100967).length < 2 ^ (prefixWord ++ tailWord_8100967).sum := by decide
  have hdescent : baseEnd_8100967 < baseStart_8100967 := by decide
  rcases family_descends (prefixWord ++ tailWord_8100967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8101031 : List Nat := [1, 1, 6, 2, 1, 1, 1, 5, 1, 1, 3]
def baseStart_8101031 : Nat := 118140960795 + 8101031 * 2 ^ 59
def prefixEnd_8101031 : Nat := 4983230072969 + 3 ^ 40 * 8101031 * 2
def baseEnd_8101031 : Nat := 4159722699973199412656543

theorem tailTrace_8101031 : CollatzResearch.WordTrace tailWord_8101031 prefixEnd_8101031 4159722699973199412656543 := by
  unfold tailWord_8101031
  simp only [CollatzResearch.WordTrace]
  refine ⟨295468874314355707790190947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196979249542903805193460631 295468874314355707790190947)
  ·
    refine ⟨443203311471533561685286421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 295468874314355707790190947 443203311471533561685286421)
    ·
      refine ⟨20775155225228135703997801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 443203311471533561685286421 20775155225228135703997801)
      ·
        refine ⟨15581366418921101777998351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20775155225228135703997801 15581366418921101777998351)
        ·
          refine ⟨23372049628381652666997527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15581366418921101777998351 23372049628381652666997527)
          ·
            refine ⟨35058074442572479000496291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23372049628381652666997527 35058074442572479000496291)
            ·
              refine ⟨52587111663858718500744437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35058074442572479000496291 52587111663858718500744437)
              ·
                refine ⟨4930041718486754859444791, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 52587111663858718500744437 4930041718486754859444791)
                ·
                  refine ⟨7395062577730132289167187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4930041718486754859444791 7395062577730132289167187)
                  ·
                    refine ⟨11092593866595198433750781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7395062577730132289167187 11092593866595198433750781)
                    ·
                      refine ⟨4159722699973199412656543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11092593866595198433750781 4159722699973199412656543)
                      ·
                        rfl

theorem cell23_8101031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 1, 5, 1, 1, 3].length) (baseStart_8101031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8101031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8101031 prefixEnd_8101031 := by exact prefixLift 8101031
  have htrace : WordTrace (prefixWord ++ tailWord_8101031) baseStart_8101031 baseEnd_8101031 := by
    simpa [prefixWord, tailWord_8101031, baseEnd_8101031] using wordTrace_append hprefix tailTrace_8101031
  have hstable : (prefixWord ++ tailWord_8101031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8101031).length < 2 ^ (prefixWord ++ tailWord_8101031).sum := by decide
  have hdescent : baseEnd_8101031 < baseStart_8101031 := by decide
  rcases family_descends (prefixWord ++ tailWord_8101031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8101034 : List Nat := [3, 1, 5, 1, 1, 2, 1, 3, 1, 5]
def baseStart_8101034 : Nat := 118140960795 + 8101034 * 2 ^ 59
def prefixEnd_8101034 : Nat := 4983230072969 + 3 ^ 40 * 8101034 * 2
def baseEnd_8101034 : Nat := 1386574746805054300306343

theorem tailTrace_8101034 : CollatzResearch.WordTrace tailWord_8101034 prefixEnd_8101034 1386574746805054300306343 := by
  unfold tailWord_8101034
  simp only [CollatzResearch.WordTrace]
  refine ⟨73867245933336209825637539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 196979322488896559535033437 73867245933336209825637539)
  ·
    refine ⟨110800868900004314738456309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73867245933336209825637539 110800868900004314738456309)
    ·
      refine ⟨10387581459375404506730279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 110800868900004314738456309 10387581459375404506730279)
      ·
        refine ⟨15581372189063106760095419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10387581459375404506730279 15581372189063106760095419)
        ·
          refine ⟨23372058283594660140143129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15581372189063106760095419 23372058283594660140143129)
          ·
            refine ⟨17529043712695995105107347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23372058283594660140143129 17529043712695995105107347)
            ·
              refine ⟨26293565569043992657661021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17529043712695995105107347 26293565569043992657661021)
              ·
                refine ⟨9860087088391497246622883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26293565569043992657661021 9860087088391497246622883)
                ·
                  refine ⟨14790130632587245869934325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9860087088391497246622883 14790130632587245869934325)
                  ·
                    refine ⟨1386574746805054300306343, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14790130632587245869934325 1386574746805054300306343)
                    ·
                      rfl

theorem cell23_8101034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 2, 1, 3, 1, 5].length) (baseStart_8101034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8101034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8101034 prefixEnd_8101034 := by exact prefixLift 8101034
  have htrace : WordTrace (prefixWord ++ tailWord_8101034) baseStart_8101034 baseEnd_8101034 := by
    simpa [prefixWord, tailWord_8101034, baseEnd_8101034] using wordTrace_append hprefix tailTrace_8101034
  have hstable : (prefixWord ++ tailWord_8101034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8101034).length < 2 ^ (prefixWord ++ tailWord_8101034).sum := by decide
  have hdescent : baseEnd_8101034 < baseStart_8101034 := by decide
  rcases family_descends (prefixWord ++ tailWord_8101034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8101057 : List Nat := [1, 2, 6, 1, 1, 1, 1, 1, 3, 1, 5]
def baseStart_8101057 : Nat := 118140960795 + 8101057 * 2 ^ 59
def prefixEnd_8101057 : Nat := 4983230072969 + 3 ^ 40 * 8101057 * 2
def baseEnd_8101057 : Nat := 4159736050470216310931423

theorem tailTrace_8101057 : CollatzResearch.WordTrace tailWord_8101057 prefixEnd_8101057 4159736050470216310931423 := by
  unfold tailWord_8101057
  simp only [CollatzResearch.WordTrace]
  refine ⟨295469822612261514230637425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196979881741507676153758283 295469822612261514230637425)
  ·
    refine ⟨221602366959196135672978069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 295469822612261514230637425 221602366959196135672978069)
    ·
      refine ⟨10387610951212318859670847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 221602366959196135672978069 10387610951212318859670847)
      ·
        refine ⟨15581416426818478289506271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10387610951212318859670847 15581416426818478289506271)
        ·
          refine ⟨23372124640227717434259407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15581416426818478289506271 23372124640227717434259407)
          ·
            refine ⟨35058186960341576151389111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23372124640227717434259407 35058186960341576151389111)
            ·
              refine ⟨52587280440512364227083667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35058186960341576151389111 52587280440512364227083667)
              ·
                refine ⟨78880920660768546340625501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52587280440512364227083667 78880920660768546340625501)
                ·
                  refine ⟨29580345247788204877734563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 78880920660768546340625501 29580345247788204877734563)
                  ·
                    refine ⟨44370517871682307316601845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29580345247788204877734563 44370517871682307316601845)
                    ·
                      refine ⟨4159736050470216310931423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44370517871682307316601845 4159736050470216310931423)
                      ·
                        rfl

theorem cell23_8101057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 1, 1, 3, 1, 5].length) (baseStart_8101057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8101057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8101057 prefixEnd_8101057 := by exact prefixLift 8101057
  have htrace : WordTrace (prefixWord ++ tailWord_8101057) baseStart_8101057 baseEnd_8101057 := by
    simpa [prefixWord, tailWord_8101057, baseEnd_8101057] using wordTrace_append hprefix tailTrace_8101057
  have hstable : (prefixWord ++ tailWord_8101057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8101057).length < 2 ^ (prefixWord ++ tailWord_8101057).sum := by decide
  have hdescent : baseEnd_8101057 < baseStart_8101057 := by decide
  rcases family_descends (prefixWord ++ tailWord_8101057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8101074 : List Nat := [3, 2, 2, 2, 1, 1, 4, 2, 1, 2, 3]
def baseStart_8101074 : Nat := 118140960795 + 8101074 * 2 ^ 59
def prefixEnd_8101074 : Nat := 4983230072969 + 3 ^ 40 * 8101074 * 2
def baseEnd_8101074 : Nat := 4159744779641342744418845

theorem tailTrace_8101074 : CollatzResearch.WordTrace tailWord_8101074 prefixEnd_8101074 4159744779641342744418845 := by
  unfold tailWord_8101074
  simp only [CollatzResearch.WordTrace]
  refine ⟨73867610663299981533501569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 196980295102133284089337517 73867610663299981533501569)
  ·
    refine ⟨55400707997474986150126177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73867610663299981533501569 55400707997474986150126177)
    ·
      refine ⟨41550530998106239612594633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55400707997474986150126177 41550530998106239612594633)
      ·
        refine ⟨31162898248579679709445975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41550530998106239612594633 31162898248579679709445975)
        ·
          refine ⟨46744347372869519564168963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31162898248579679709445975 46744347372869519564168963)
          ·
            refine ⟨70116521059304279346253445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46744347372869519564168963 70116521059304279346253445)
            ·
              refine ⟨13146847698619552377422521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 70116521059304279346253445 13146847698619552377422521)
              ·
                refine ⟨9860135773964664283066891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13146847698619552377422521 9860135773964664283066891)
                ·
                  refine ⟨14790203660946996424600337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9860135773964664283066891 14790203660946996424600337)
                  ·
                    refine ⟨11092652745710247318450253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14790203660946996424600337 11092652745710247318450253)
                    ·
                      refine ⟨4159744779641342744418845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11092652745710247318450253 4159744779641342744418845)
                      ·
                        rfl

theorem cell23_8101074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 4, 2, 1, 2, 3].length) (baseStart_8101074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8101074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8101074 prefixEnd_8101074 := by exact prefixLift 8101074
  have htrace : WordTrace (prefixWord ++ tailWord_8101074) baseStart_8101074 baseEnd_8101074 := by
    simpa [prefixWord, tailWord_8101074, baseEnd_8101074] using wordTrace_append hprefix tailTrace_8101074
  have hstable : (prefixWord ++ tailWord_8101074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8101074).length < 2 ^ (prefixWord ++ tailWord_8101074).sum := by decide
  have hdescent : baseEnd_8101074 < baseStart_8101074 := by decide
  rcases family_descends (prefixWord ++ tailWord_8101074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8101077 : List Nat := [1, 3, 2, 4, 1, 1, 4, 7]
def baseStart_8101077 : Nat := 118140960795 + 8101077 * 2 ^ 59
def prefixEnd_8101077 : Nat := 4983230072969 + 3 ^ 40 * 8101077 * 2
def baseEnd_8101077 : Nat := 154064678521603934543753

theorem tailTrace_8101077 : CollatzResearch.WordTrace tailWord_8101077 prefixEnd_8101077 154064678521603934543753 := by
  unfold tailWord_8101077
  simp only [CollatzResearch.WordTrace]
  refine ⟨295470552072189057646365485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196980368048126038430910323 295470552072189057646365485)
  ·
    refine ⟨110801457027070896617387057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 295470552072189057646365485 110801457027070896617387057)
    ·
      refine ⟨83101092770303172463040293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110801457027070896617387057 83101092770303172463040293)
      ·
        refine ⟨15581454894431844836820055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 83101092770303172463040293 15581454894431844836820055)
        ·
          refine ⟨23372182341647767255230083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15581454894431844836820055 23372182341647767255230083)
          ·
            refine ⟨35058273512471650882845125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23372182341647767255230083 35058273512471650882845125)
            ·
              refine ⟨6573426283588434540533461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35058273512471650882845125 6573426283588434540533461)
              ·
                refine ⟨154064678521603934543753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6573426283588434540533461 154064678521603934543753)
                ·
                  rfl

theorem cell23_8101077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 4, 7].length) (baseStart_8101077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8101077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8101077 prefixEnd_8101077 := by exact prefixLift 8101077
  have htrace : WordTrace (prefixWord ++ tailWord_8101077) baseStart_8101077 baseEnd_8101077 := by
    simpa [prefixWord, tailWord_8101077, baseEnd_8101077] using wordTrace_append hprefix tailTrace_8101077
  have hstable : (prefixWord ++ tailWord_8101077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8101077).length < 2 ^ (prefixWord ++ tailWord_8101077).sum := by decide
  have hdescent : baseEnd_8101077 < baseStart_8101077 := by decide
  rcases family_descends (prefixWord ++ tailWord_8101077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8101083 : List Nat := [1, 1, 1, 1, 1, 1, 1, 4, 2, 3, 7]
def baseStart_8101083 : Nat := 118140960795 + 8101083 * 2 ^ 59
def prefixEnd_8101083 : Nat := 4983230072969 + 3 ^ 40 * 8101083 * 2
def baseEnd_8101083 : Nat := 4159749400967233209206303

theorem tailTrace_8101083 : CollatzResearch.WordTrace tailWord_8101083 prefixEnd_8101083 4159749400967233209206303 := by
  unfold tailWord_8101083
  simp only [CollatzResearch.WordTrace]
  refine ⟨295470770910167320671083903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196980513940111547114055935 295470770910167320671083903)
  ·
    refine ⟨443206156365250981006625855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 295470770910167320671083903 443206156365250981006625855)
    ·
      refine ⟨664809234547876471509938783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 443206156365250981006625855 664809234547876471509938783)
      ·
        refine ⟨997213851821814707264908175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 664809234547876471509938783 997213851821814707264908175)
        ·
          refine ⟨1495820777732722060897362263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 997213851821814707264908175 1495820777732722060897362263)
          ·
            refine ⟨2243731166599083091346043395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1495820777732722060897362263 2243731166599083091346043395)
            ·
              refine ⟨3365596749898624637019065093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2243731166599083091346043395 3365596749898624637019065093)
              ·
                refine ⟨631049390605992119441074705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3365596749898624637019065093 631049390605992119441074705)
                ·
                  refine ⟨473287042954494089580806029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 631049390605992119441074705 473287042954494089580806029)
                  ·
                    refine ⟨177482641107935283592802261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 473287042954494089580806029 177482641107935283592802261)
                    ·
                      refine ⟨4159749400967233209206303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 177482641107935283592802261 4159749400967233209206303)
                      ·
                        rfl

theorem cell23_8101083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4, 2, 3, 7].length) (baseStart_8101083 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8101083 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8101083 prefixEnd_8101083 := by exact prefixLift 8101083
  have htrace : WordTrace (prefixWord ++ tailWord_8101083) baseStart_8101083 baseEnd_8101083 := by
    simpa [prefixWord, tailWord_8101083, baseEnd_8101083] using wordTrace_append hprefix tailTrace_8101083
  have hstable : (prefixWord ++ tailWord_8101083).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8101083).length < 2 ^ (prefixWord ++ tailWord_8101083).sum := by decide
  have hdescent : baseEnd_8101083 < baseStart_8101083 := by decide
  rcases family_descends (prefixWord ++ tailWord_8101083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8101087 : List Nat := [1, 1, 2, 3, 2, 1, 3, 2, 4, 1, 3]
def baseStart_8101087 : Nat := 118140960795 + 8101087 * 2 ^ 59
def prefixEnd_8101087 : Nat := 4983230072969 + 3 ^ 40 * 8101087 * 2
def baseEnd_8101087 : Nat := 4159751454889851193556285

theorem tailTrace_8101087 : CollatzResearch.WordTrace tailWord_8101087 prefixEnd_8101087 4159751454889851193556285 := by
  unfold tailWord_8101087
  simp only [CollatzResearch.WordTrace]
  refine ⟨295470916802152829354229515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196980611201435219569486343 295470916802152829354229515)
  ·
    refine ⟨443206375203229244031344273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 295470916802152829354229515 443206375203229244031344273)
    ·
      refine ⟨332404781402421933023508205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 443206375203229244031344273 332404781402421933023508205)
      ·
        refine ⟨124651793025908224883815577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 332404781402421933023508205 124651793025908224883815577)
        ·
          refine ⟨93488844769431168662861683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 124651793025908224883815577 93488844769431168662861683)
          ·
            refine ⟨140233267154146752994292525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93488844769431168662861683 140233267154146752994292525)
            ·
              refine ⟨52587475182805032372859697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 140233267154146752994292525 52587475182805032372859697)
              ·
                refine ⟨39440606387103774279644773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52587475182805032372859697 39440606387103774279644773)
                ·
                  refine ⟨7395113697581957677433395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39440606387103774279644773 7395113697581957677433395)
                  ·
                    refine ⟨11092670546372936516150093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7395113697581957677433395 11092670546372936516150093)
                    ·
                      refine ⟨4159751454889851193556285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11092670546372936516150093 4159751454889851193556285)
                      ·
                        rfl

theorem cell23_8101087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 3, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 3, 2, 4, 1, 3].length) (baseStart_8101087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8101087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8101087 prefixEnd_8101087 := by exact prefixLift 8101087
  have htrace : WordTrace (prefixWord ++ tailWord_8101087) baseStart_8101087 baseEnd_8101087 := by
    simpa [prefixWord, tailWord_8101087, baseEnd_8101087] using wordTrace_append hprefix tailTrace_8101087
  have hstable : (prefixWord ++ tailWord_8101087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8101087).length < 2 ^ (prefixWord ++ tailWord_8101087).sum := by decide
  have hdescent : baseEnd_8101087 < baseStart_8101087 := by decide
  rcases family_descends (prefixWord ++ tailWord_8101087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8101088 : List Nat := [2, 1, 1, 3, 1, 6, 1, 3, 1, 2, 2]
def baseStart_8101088 : Nat := 118140960795 + 8101088 * 2 ^ 59
def prefixEnd_8101088 : Nat := 4983230072969 + 3 ^ 40 * 8101088 * 2
def baseEnd_8101088 : Nat := 4159751968370505689643781

theorem tailTrace_8101088 : CollatzResearch.WordTrace tailWord_8101088 prefixEnd_8101088 4159751968370505689643781 := by
  unfold tailWord_8101088
  simp only [CollatzResearch.WordTrace]
  refine ⟨147735476637574603262507959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196980635516766137683343945 147735476637574603262507959)
  ·
    refine ⟨221603214956361904893761939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147735476637574603262507959 221603214956361904893761939)
    ·
      refine ⟨332404822434542857340642909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 221603214956361904893761939 332404822434542857340642909)
      ·
        refine ⟨124651808412953571502741091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 332404822434542857340642909 124651808412953571502741091)
        ·
          refine ⟨186977712619430357254111637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124651808412953571502741091 186977712619430357254111637)
          ·
            refine ⟨8764580279035797996286483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 186977712619430357254111637 8764580279035797996286483)
            ·
              refine ⟨13146870418553696994429725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8764580279035797996286483 13146870418553696994429725)
              ·
                refine ⟨4930076406957636372911147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13146870418553696994429725 4930076406957636372911147)
                ·
                  refine ⟨7395114610436454559366721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4930076406957636372911147 7395114610436454559366721)
                  ·
                    refine ⟨5546335957827340919525041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7395114610436454559366721 5546335957827340919525041)
                    ·
                      refine ⟨4159751968370505689643781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5546335957827340919525041 4159751968370505689643781)
                      ·
                        rfl

theorem cell23_8101088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 6, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 6, 1, 3, 1, 2, 2].length) (baseStart_8101088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8101088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8101088 prefixEnd_8101088 := by exact prefixLift 8101088
  have htrace : WordTrace (prefixWord ++ tailWord_8101088) baseStart_8101088 baseEnd_8101088 := by
    simpa [prefixWord, tailWord_8101088, baseEnd_8101088] using wordTrace_append hprefix tailTrace_8101088
  have hstable : (prefixWord ++ tailWord_8101088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8101088).length < 2 ^ (prefixWord ++ tailWord_8101088).sum := by decide
  have hdescent : baseEnd_8101088 < baseStart_8101088 := by decide
  rcases family_descends (prefixWord ++ tailWord_8101088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8101121 : List Nat := [1, 2, 4, 1, 1, 3, 4, 1, 2, 1, 3]
def baseStart_8101121 : Nat := 118140960795 + 8101121 * 2 ^ 59
def prefixEnd_8101121 : Nat := 4983230072969 + 3 ^ 40 * 8101121 * 2
def baseEnd_8101121 : Nat := 4159768913232104060531129

theorem tailTrace_8101121 : CollatzResearch.WordTrace tailWord_8101121 prefixEnd_8101121 4159768913232104060531129 := by
  unfold tailWord_8101121
  simp only [CollatzResearch.WordTrace]
  refine ⟨295472156884029653160967217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196981437922686435440644811 295472156884029653160967217)
  ·
    refine ⟨221604117663022239870725413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 295472156884029653160967217 221604117663022239870725413)
    ·
      refine ⟨41550772061816669975761015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 221604117663022239870725413 41550772061816669975761015)
      ·
        refine ⟨62326158092725004963641523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41550772061816669975761015 62326158092725004963641523)
        ·
          refine ⟨93489237139087507445462285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62326158092725004963641523 93489237139087507445462285)
          ·
            refine ⟨35058463927157815292048357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 93489237139087507445462285 35058463927157815292048357)
            ·
              refine ⟨6573461986342090367259067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35058463927157815292048357 6573461986342090367259067)
              ·
                refine ⟨9860192979513135550888601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6573461986342090367259067 9860192979513135550888601)
                ·
                  refine ⟨7395144734634851663166451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9860192979513135550888601 7395144734634851663166451)
                  ·
                    refine ⟨11092717101952277494749677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7395144734634851663166451 11092717101952277494749677)
                    ·
                      refine ⟨4159768913232104060531129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11092717101952277494749677 4159768913232104060531129)
                      ·
                        rfl

theorem cell23_8101121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 4, 1, 2, 1, 3].length) (baseStart_8101121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8101121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8101121 prefixEnd_8101121 := by exact prefixLift 8101121
  have htrace : WordTrace (prefixWord ++ tailWord_8101121) baseStart_8101121 baseEnd_8101121 := by
    simpa [prefixWord, tailWord_8101121, baseEnd_8101121] using wordTrace_append hprefix tailTrace_8101121
  have hstable : (prefixWord ++ tailWord_8101121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8101121).length < 2 ^ (prefixWord ++ tailWord_8101121).sum := by decide
  have hdescent : baseEnd_8101121 < baseStart_8101121 := by decide
  rcases family_descends (prefixWord ++ tailWord_8101121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8101131 : List Nat := [1, 1, 1, 1, 5, 5, 1, 2, 1, 3, 2]
def baseStart_8101131 : Nat := 118140960795 + 8101131 * 2 ^ 59
def prefixEnd_8101131 : Nat := 4983230072969 + 3 ^ 40 * 8101131 * 2
def baseEnd_8101131 : Nat := 4159774048038649021406083

theorem tailTrace_8101131 : CollatzResearch.WordTrace tailWord_8101131 prefixEnd_8101131 4159774048038649021406083 := by
  unfold tailWord_8101131
  simp only [CollatzResearch.WordTrace]
  refine ⟨295472521613993424868831247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196981681075995616579220831 295472521613993424868831247)
  ·
    refine ⟨443208782420990137303246871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 295472521613993424868831247 443208782420990137303246871)
    ·
      refine ⟨664813173631485205954870307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 443208782420990137303246871 664813173631485205954870307)
      ·
        refine ⟨997219760447227808932305461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 664813173631485205954870307 997219760447227808932305461)
        ·
          refine ⟨93489352541927607087403637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 997219760447227808932305461 93489352541927607087403637)
          ·
            refine ⟨8764626800805713164444091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 93489352541927607087403637 8764626800805713164444091)
            ·
              refine ⟨13146940201208569746666137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8764626800805713164444091 13146940201208569746666137)
              ·
                refine ⟨9860205150906427309999603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13146940201208569746666137 9860205150906427309999603)
                ·
                  refine ⟨14790307726359640964999405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9860205150906427309999603 14790307726359640964999405)
                  ·
                    refine ⟨5546365397384865361874777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14790307726359640964999405 5546365397384865361874777)
                    ·
                      refine ⟨4159774048038649021406083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5546365397384865361874777 4159774048038649021406083)
                      ·
                        rfl

theorem cell23_8101131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 5, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 5, 1, 2, 1, 3, 2].length) (baseStart_8101131 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8101131 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8101131 prefixEnd_8101131 := by exact prefixLift 8101131
  have htrace : WordTrace (prefixWord ++ tailWord_8101131) baseStart_8101131 baseEnd_8101131 := by
    simpa [prefixWord, tailWord_8101131, baseEnd_8101131] using wordTrace_append hprefix tailTrace_8101131
  have hstable : (prefixWord ++ tailWord_8101131).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8101131).length < 2 ^ (prefixWord ++ tailWord_8101131).sum := by decide
  have hdescent : baseEnd_8101131 < baseStart_8101131 := by decide
  rcases family_descends (prefixWord ++ tailWord_8101131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8101144 : List Nat := [2, 1, 2, 3, 1, 4, 1, 2, 1, 4, 2]
def baseStart_8101144 : Nat := 118140960795 + 8101144 * 2 ^ 59
def prefixEnd_8101144 : Nat := 4983230072969 + 3 ^ 40 * 8101144 * 2
def baseEnd_8101144 : Nat := 4159780723287157470543523

theorem tailTrace_8101144 : CollatzResearch.WordTrace tailWord_8101144 prefixEnd_8101144 4159780723287157470543523 := by
  unfold tailWord_8101144
  simp only [CollatzResearch.WordTrace]
  refine ⟨147736497881473164044527243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196981997175297552059369657 147736497881473164044527243)
  ·
    refine ⟨221604746822209746066790865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147736497881473164044527243 221604746822209746066790865)
    ·
      refine ⟨166203560116657309550093149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 221604746822209746066790865 166203560116657309550093149)
      ·
        refine ⟨62326335043746491081284931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 166203560116657309550093149 62326335043746491081284931)
        ·
          refine ⟨93489502565619736621927397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62326335043746491081284931 93489502565619736621927397)
          ·
            refine ⟨17529281731053700616611387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 93489502565619736621927397 17529281731053700616611387)
            ·
              refine ⟨26293922596580550924917081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17529281731053700616611387 26293922596580550924917081)
              ·
                refine ⟨19720441947435413193687811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26293922596580550924917081 19720441947435413193687811)
                ·
                  refine ⟨29580662921153119790531717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19720441947435413193687811 29580662921153119790531717)
                  ·
                    refine ⟨5546374297716209960724697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29580662921153119790531717 5546374297716209960724697)
                    ·
                      refine ⟨4159780723287157470543523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5546374297716209960724697 4159780723287157470543523)
                      ·
                        rfl

theorem cell23_8101144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 4, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 4, 1, 2, 1, 4, 2].length) (baseStart_8101144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8101144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8101144 prefixEnd_8101144 := by exact prefixLift 8101144
  have htrace : WordTrace (prefixWord ++ tailWord_8101144) baseStart_8101144 baseEnd_8101144 := by
    simpa [prefixWord, tailWord_8101144, baseEnd_8101144] using wordTrace_append hprefix tailTrace_8101144
  have hstable : (prefixWord ++ tailWord_8101144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8101144).length < 2 ^ (prefixWord ++ tailWord_8101144).sum := by decide
  have hdescent : baseEnd_8101144 < baseStart_8101144 := by decide
  rcases family_descends (prefixWord ++ tailWord_8101144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8101187 : List Nat := [1, 1, 1, 3, 1, 3, 1, 1, 4, 5, 2]
def baseStart_8101187 : Nat := 118140960795 + 8101187 * 2 ^ 59
def prefixEnd_8101187 : Nat := 4983230072969 + 3 ^ 40 * 8101187 * 2
def baseEnd_8101187 : Nat := 4159802802955300802305825

theorem tailTrace_8101187 : CollatzResearch.WordTrace tailWord_8101187 prefixEnd_8101187 4159802802955300802305825 := by
  unfold tailWord_8101187
  simp only [CollatzResearch.WordTrace]
  refine ⟨295474564101790546432869815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196983042734527030955246543 295474564101790546432869815)
  ·
    refine ⟨443211846152685819649304723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 295474564101790546432869815 443211846152685819649304723)
    ·
      refine ⟨664817769229028729473957085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 443211846152685819649304723 664817769229028729473957085)
      ·
        refine ⟨249306663460885773552733907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 664817769229028729473957085 249306663460885773552733907)
        ·
          refine ⟨373959995191328660329100861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 249306663460885773552733907 373959995191328660329100861)
          ·
            refine ⟨140234998196748247623412823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 373959995191328660329100861 140234998196748247623412823)
            ·
              refine ⟨210352497295122371435119235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 140234998196748247623412823 210352497295122371435119235)
              ·
                refine ⟨315528745942683557152678853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 210352497295122371435119235 315528745942683557152678853)
                ·
                  refine ⟨59161639864253166966127285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 315528745942683557152678853 59161639864253166966127285)
                  ·
                    refine ⟨5546403737273734403074433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 59161639864253166966127285 5546403737273734403074433)
                    ·
                      refine ⟨4159802802955300802305825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5546403737273734403074433 4159802802955300802305825)
                      ·
                        rfl

theorem cell23_8101187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 1, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 1, 4, 5, 2].length) (baseStart_8101187 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8101187 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8101187 prefixEnd_8101187 := by exact prefixLift 8101187
  have htrace : WordTrace (prefixWord ++ tailWord_8101187) baseStart_8101187 baseEnd_8101187 := by
    simpa [prefixWord, tailWord_8101187, baseEnd_8101187] using wordTrace_append hprefix tailTrace_8101187
  have hstable : (prefixWord ++ tailWord_8101187).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8101187).length < 2 ^ (prefixWord ++ tailWord_8101187).sum := by decide
  have hdescent : baseEnd_8101187 < baseStart_8101187 := by decide
  rcases family_descends (prefixWord ++ tailWord_8101187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8101217 : List Nat := [1, 2, 3, 1, 1, 1, 1, 6, 2, 1, 4]
def baseStart_8101217 : Nat := 118140960795 + 8101217 * 2 ^ 59
def prefixEnd_8101217 : Nat := 4983230072969 + 3 ^ 40 * 8101217 * 2
def baseEnd_8101217 : Nat := 4159818207374935684930687

theorem tailTrace_8101217 : CollatzResearch.WordTrace tailWord_8101217 prefixEnd_8101217 4159818207374935684930687 := by
  unfold tailWord_8101217
  simp only [CollatzResearch.WordTrace]
  refine ⟨295475658291681861556461905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196983772194454574370974603 295475658291681861556461905)
  ·
    refine ⟨221606743718761396167346429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 295475658291681861556461905 221606743718761396167346429)
    ·
      refine ⟨83102528894535523562754911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 221606743718761396167346429 83102528894535523562754911)
      ·
        refine ⟨124653793341803285344132367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83102528894535523562754911 124653793341803285344132367)
        ·
          refine ⟨186980690012704928016198551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124653793341803285344132367 186980690012704928016198551)
          ·
            refine ⟨280471035019057392024297827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 186980690012704928016198551 280471035019057392024297827)
            ·
              refine ⟨420706552528586088036446741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 280471035019057392024297827 420706552528586088036446741)
              ·
                refine ⟨19720619649777472876708441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 420706552528586088036446741 19720619649777472876708441)
                ·
                  refine ⟨14790464737333104657531331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19720619649777472876708441 14790464737333104657531331)
                  ·
                    refine ⟨22185697105999656986296997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14790464737333104657531331 22185697105999656986296997)
                    ·
                      refine ⟨4159818207374935684930687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22185697105999656986296997 4159818207374935684930687)
                      ·
                        rfl

theorem cell23_8101217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 6, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 6, 2, 1, 4].length) (baseStart_8101217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8101217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8101217 prefixEnd_8101217 := by exact prefixLift 8101217
  have htrace : WordTrace (prefixWord ++ tailWord_8101217) baseStart_8101217 baseEnd_8101217 := by
    simpa [prefixWord, tailWord_8101217, baseEnd_8101217] using wordTrace_append hprefix tailTrace_8101217
  have hstable : (prefixWord ++ tailWord_8101217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8101217).length < 2 ^ (prefixWord ++ tailWord_8101217).sum := by decide
  have hdescent : baseEnd_8101217 < baseStart_8101217 := by decide
  rcases family_descends (prefixWord ++ tailWord_8101217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8101234 : List Nat := [3, 2, 1, 2, 1, 2, 1, 3, 2, 4, 2]
def baseStart_8101234 : Nat := 118140960795 + 8101234 * 2 ^ 59
def prefixEnd_8101234 : Nat := 4983230072969 + 3 ^ 40 * 8101234 * 2
def baseEnd_8101234 : Nat := 4159826936546062118418109

theorem tailTrace_8101234 : CollatzResearch.WordTrace tailWord_8101234 prefixEnd_8101234 4159826936546062118418109 := by
  unfold tailWord_8101234
  simp only [CollatzResearch.WordTrace]
  refine ⟨73869069583155068364957689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 196984185555080182306553837 73869069583155068364957689)
  ·
    refine ⟨55401802187366301273718267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73869069583155068364957689 55401802187366301273718267)
    ·
      refine ⟨83102703281049451910577401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55401802187366301273718267 83102703281049451910577401)
      ·
        refine ⟨62327027460787088932933051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83102703281049451910577401 62327027460787088932933051)
        ·
          refine ⟨93490541191180633399399577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62327027460787088932933051 93490541191180633399399577)
          ·
            refine ⟨70117905893385475049549683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 93490541191180633399399577 70117905893385475049549683)
            ·
              refine ⟨105176858840078212574324525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70117905893385475049549683 105176858840078212574324525)
              ·
                refine ⟨39441322065029329715371697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 105176858840078212574324525 39441322065029329715371697)
                ·
                  refine ⟨29580991548771997286528773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39441322065029329715371697 29580991548771997286528773)
                  ·
                    refine ⟨5546435915394749491224145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29580991548771997286528773 5546435915394749491224145)
                    ·
                      refine ⟨4159826936546062118418109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5546435915394749491224145 4159826936546062118418109)
                      ·
                        rfl

theorem cell23_8101234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 1, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 1, 3, 2, 4, 2].length) (baseStart_8101234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8101234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8101234 prefixEnd_8101234 := by exact prefixLift 8101234
  have htrace : WordTrace (prefixWord ++ tailWord_8101234) baseStart_8101234 baseEnd_8101234 := by
    simpa [prefixWord, tailWord_8101234, baseEnd_8101234] using wordTrace_append hprefix tailTrace_8101234
  have hstable : (prefixWord ++ tailWord_8101234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8101234).length < 2 ^ (prefixWord ++ tailWord_8101234).sum := by decide
  have hdescent : baseEnd_8101234 < baseStart_8101234 := by decide
  rcases family_descends (prefixWord ++ tailWord_8101234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8101304 : List Nat := [2, 1, 2, 1, 2, 2, 5, 2, 1, 5]
def baseStart_8101304 : Nat := 118140960795 + 8101304 * 2 ^ 59
def prefixEnd_8101304 : Nat := 4983230072969 + 3 ^ 40 * 8101304 * 2
def baseEnd_8101304 : Nat := 1386620960063958948180929

theorem tailTrace_8101304 : CollatzResearch.WordTrace tailWord_8101304 prefixEnd_8101304 1386620960063958948180929 := by
  unfold tailWord_8101304
  simp only [CollatzResearch.WordTrace]
  refine ⟨147739415721183337707439483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196985887628244450276585977 147739415721183337707439483)
  ·
    refine ⟨221609123581775006561159225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147739415721183337707439483 221609123581775006561159225)
    ·
      refine ⟨166206842686331254920869419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 221609123581775006561159225 166206842686331254920869419)
      ·
        refine ⟨249310264029496882381304129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166206842686331254920869419 249310264029496882381304129)
        ·
          refine ⟨186982698022122661785978097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 249310264029496882381304129 186982698022122661785978097)
          ·
            refine ⟨140237023516591996339483573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 186982698022122661785978097 140237023516591996339483573)
            ·
              refine ⟨13147220954680499656826585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 140237023516591996339483573 13147220954680499656826585)
              ·
                refine ⟨9860415716010374742619939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13147220954680499656826585 9860415716010374742619939)
                ·
                  refine ⟨14790623574015562113929909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9860415716010374742619939 14790623574015562113929909)
                  ·
                    refine ⟨1386620960063958948180929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14790623574015562113929909 1386620960063958948180929)
                    ·
                      rfl

theorem cell23_8101304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 5, 2, 1, 5].length) (baseStart_8101304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8101304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8101304 prefixEnd_8101304 := by exact prefixLift 8101304
  have htrace : WordTrace (prefixWord ++ tailWord_8101304) baseStart_8101304 baseEnd_8101304 := by
    simpa [prefixWord, tailWord_8101304, baseEnd_8101304] using wordTrace_append hprefix tailTrace_8101304
  have hstable : (prefixWord ++ tailWord_8101304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8101304).length < 2 ^ (prefixWord ++ tailWord_8101304).sum := by decide
  have hdescent : baseEnd_8101304 < baseStart_8101304 := by decide
  rcases family_descends (prefixWord ++ tailWord_8101304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8101351 : List Nat := [1, 1, 5, 2, 1, 2, 2, 3, 2, 4]
def baseStart_8101351 : Nat := 118140960795 + 8101351 * 2 ^ 59
def prefixEnd_8101351 : Nat := 4983230072969 + 3 ^ 40 * 8101351 * 2
def baseEnd_8101351 : Nat := 1386629004594212720218357

theorem tailTrace_8101351 : CollatzResearch.WordTrace tailWord_8101351 prefixEnd_8101351 1386629004594212720218357 := by
  unfold tailWord_8101351
  simp only [CollatzResearch.WordTrace]
  refine ⟨295480545673196402441839907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196987030448797601627893271 295480545673196402441839907)
  ·
    refine ⟨443220818509794603662759861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 295480545673196402441839907 443220818509794603662759861)
    ·
      refine ⟨41551951735293244093383737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 443220818509794603662759861 41551951735293244093383737)
      ·
        refine ⟨31163963801469933070037803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41551951735293244093383737 31163963801469933070037803)
        ·
          refine ⟨46745945702204899605056705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31163963801469933070037803 46745945702204899605056705)
          ·
            refine ⟨35059459276653674703792529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46745945702204899605056705 35059459276653674703792529)
            ·
              refine ⟨26294594457490256027844397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35059459276653674703792529 26294594457490256027844397)
              ·
                refine ⟨9860472921558846010441649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26294594457490256027844397 9860472921558846010441649)
                ·
                  refine ⟨7395354691169134507831237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9860472921558846010441649 7395354691169134507831237)
                  ·
                    refine ⟨1386629004594212720218357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7395354691169134507831237 1386629004594212720218357)
                    ·
                      rfl

theorem cell23_8101351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 2, 3, 2, 4].length) (baseStart_8101351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8101351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8101351 prefixEnd_8101351 := by exact prefixLift 8101351
  have htrace : WordTrace (prefixWord ++ tailWord_8101351) baseStart_8101351 baseEnd_8101351 := by
    simpa [prefixWord, tailWord_8101351, baseEnd_8101351] using wordTrace_append hprefix tailTrace_8101351
  have hstable : (prefixWord ++ tailWord_8101351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8101351).length < 2 ^ (prefixWord ++ tailWord_8101351).sum := by decide
  have hdescent : baseEnd_8101351 < baseStart_8101351 := by decide
  rcases family_descends (prefixWord ++ tailWord_8101351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8101358 : List Nat := [4, 1, 2, 1, 2, 1, 3, 2, 3, 2, 2]
def baseStart_8101358 : Nat := 118140960795 + 8101358 * 2 ^ 59
def prefixEnd_8101358 : Nat := 4983230072969 + 3 ^ 40 * 8101358 * 2
def baseEnd_8101358 : Nat := 4159890608147219633267539

theorem tailTrace_8101358 : CollatzResearch.WordTrace tailWord_8101358 prefixEnd_8101358 4159890608147219633267539 := by
  unfold tailWord_8101358
  simp only [CollatzResearch.WordTrace]
  refine ⟨36935100123021380329668091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 196987200656114028424896485 36935100123021380329668091)
  ·
    refine ⟨55402650184532070494502137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36935100123021380329668091 55402650184532070494502137)
    ·
      refine ⟨41551987638399052870876603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55402650184532070494502137 41551987638399052870876603)
      ·
        refine ⟨62327981457598579306314905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41551987638399052870876603 62327981457598579306314905)
        ·
          refine ⟨46745986093198934479736179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62327981457598579306314905 46745986093198934479736179)
          ·
            refine ⟨70118979139798401719604269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46745986093198934479736179 70118979139798401719604269)
            ·
              refine ⟨26294617177424400644851601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 70118979139798401719604269 26294617177424400644851601)
              ·
                refine ⟨19720962883068300483638701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26294617177424400644851601 19720962883068300483638701)
                ·
                  refine ⟨7395361081150612681364513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19720962883068300483638701 7395361081150612681364513)
                  ·
                    refine ⟨5546520810862959511023385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7395361081150612681364513 5546520810862959511023385)
                    ·
                      refine ⟨4159890608147219633267539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5546520810862959511023385 4159890608147219633267539)
                      ·
                        rfl

theorem cell23_8101358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 3, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 3, 2, 3, 2, 2].length) (baseStart_8101358 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8101358 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8101358 prefixEnd_8101358 := by exact prefixLift 8101358
  have htrace : WordTrace (prefixWord ++ tailWord_8101358) baseStart_8101358 baseEnd_8101358 := by
    simpa [prefixWord, tailWord_8101358, baseEnd_8101358] using wordTrace_append hprefix tailTrace_8101358
  have hstable : (prefixWord ++ tailWord_8101358).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8101358).length < 2 ^ (prefixWord ++ tailWord_8101358).sum := by decide
  have hdescent : baseEnd_8101358 < baseStart_8101358 := by decide
  rcases family_descends (prefixWord ++ tailWord_8101358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8101408 : List Nat := [2, 1, 1, 6, 1, 3, 1, 1, 1, 3, 3]
def baseStart_8101408 : Nat := 118140960795 + 8101408 * 2 ^ 59
def prefixEnd_8101408 : Nat := 4983230072969 + 3 ^ 40 * 8101408 * 2
def baseEnd_8101408 : Nat := 4159916282179944437642309

theorem tailTrace_8101408 : CollatzResearch.WordTrace tailWord_8101408 prefixEnd_8101408 4159916282179944437642309 := by
  unfold tailWord_8101408
  simp only [CollatzResearch.WordTrace]
  refine ⟨147741312316994950588332439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196988416422659934117776585 147741312316994950588332439)
  ·
    refine ⟨221611968475492425882498659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147741312316994950588332439 221611968475492425882498659)
    ·
      refine ⟨332417952713238638823747989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 221611968475492425882498659 332417952713238638823747989)
      ·
        refine ⟨15582091533433061194863187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 332417952713238638823747989 15582091533433061194863187)
        ·
          refine ⟨23373137300149591792294781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15582091533433061194863187 23373137300149591792294781)
          ·
            refine ⟨8764926487556096922110543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23373137300149591792294781 8764926487556096922110543)
            ·
              refine ⟨13147389731334145383165815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8764926487556096922110543 13147389731334145383165815)
              ·
                refine ⟨19721084597001218074748723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13147389731334145383165815 19721084597001218074748723)
                ·
                  refine ⟨29581626895501827112123085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19721084597001218074748723 29581626895501827112123085)
                  ·
                    refine ⟨11093110085813185167046157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29581626895501827112123085 11093110085813185167046157)
                    ·
                      refine ⟨4159916282179944437642309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11093110085813185167046157 4159916282179944437642309)
                      ·
                        rfl

theorem cell23_8101408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 3, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 3, 1, 1, 1, 3, 3].length) (baseStart_8101408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8101408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8101408 prefixEnd_8101408 := by exact prefixLift 8101408
  have htrace : WordTrace (prefixWord ++ tailWord_8101408) baseStart_8101408 baseEnd_8101408 := by
    simpa [prefixWord, tailWord_8101408, baseEnd_8101408] using wordTrace_append hprefix tailTrace_8101408
  have hstable : (prefixWord ++ tailWord_8101408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8101408).length < 2 ^ (prefixWord ++ tailWord_8101408).sum := by decide
  have hdescent : baseEnd_8101408 < baseStart_8101408 := by decide
  rcases family_descends (prefixWord ++ tailWord_8101408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8101434 : List Nat := [3, 1, 1, 1, 3, 2, 3, 1, 2, 1, 5]
def baseStart_8101434 : Nat := 118140960795 + 8101434 * 2 ^ 59
def prefixEnd_8101434 : Nat := 4983230072969 + 3 ^ 40 * 8101434 * 2
def baseEnd_8101434 : Nat := 4159929632676961335917189

theorem tailTrace_8101434 : CollatzResearch.WordTrace tailWord_8101434 prefixEnd_8101434 4159929632676961335917189 := by
  unfold tailWord_8101434
  simp only [CollatzResearch.WordTrace]
  refine ⟨73870893232973926904277839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 196989048621263805078074237 73870893232973926904277839)
  ·
    refine ⟨110806339849460890356416759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73870893232973926904277839 110806339849460890356416759)
    ·
      refine ⟨166209509774191335534625139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110806339849460890356416759 166209509774191335534625139)
      ·
        refine ⟨249314264661287003301937709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166209509774191335534625139 249314264661287003301937709)
        ·
          refine ⟨93492849247982626238226641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 249314264661287003301937709 93492849247982626238226641)
          ·
            refine ⟨70119636935986969678669981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 93492849247982626238226641 70119636935986969678669981)
            ·
              refine ⟨26294863850995113629501243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 70119636935986969678669981 26294863850995113629501243)
              ·
                refine ⟨39442295776492670444251865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26294863850995113629501243 39442295776492670444251865)
                ·
                  refine ⟨29581721832369502833188899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39442295776492670444251865 29581721832369502833188899)
                  ·
                    refine ⟨44372582748554254249783349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29581721832369502833188899 44372582748554254249783349)
                    ·
                      refine ⟨4159929632676961335917189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44372582748554254249783349 4159929632676961335917189)
                      ·
                        rfl

theorem cell23_8101434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 3, 1, 2, 1, 5].length) (baseStart_8101434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8101434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8101434 prefixEnd_8101434 := by exact prefixLift 8101434
  have htrace : WordTrace (prefixWord ++ tailWord_8101434) baseStart_8101434 baseEnd_8101434 := by
    simpa [prefixWord, tailWord_8101434, baseEnd_8101434] using wordTrace_append hprefix tailTrace_8101434
  have hstable : (prefixWord ++ tailWord_8101434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8101434).length < 2 ^ (prefixWord ++ tailWord_8101434).sum := by decide
  have hdescent : baseEnd_8101434 < baseStart_8101434 := by decide
  rcases family_descends (prefixWord ++ tailWord_8101434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8101464 : List Nat := [2, 1, 2, 2, 1, 2, 1, 3, 1, 5, 3]
def baseStart_8101464 : Nat := 118140960795 + 8101464 * 2 ^ 59
def prefixEnd_8101464 : Nat := 4983230072969 + 3 ^ 40 * 8101464 * 2
def baseEnd_8101464 : Nat := 4159945037096596218542051

theorem tailTrace_8101464 : CollatzResearch.WordTrace tailWord_8101464 prefixEnd_8101464 4159945037096596218542051 := by
  unfold tailWord_8101464
  simp only [CollatzResearch.WordTrace]
  refine ⟨147742333560893511370351723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196989778081191348493802297 147742333560893511370351723)
  ·
    refine ⟨221613500341340267055527585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147742333560893511370351723 221613500341340267055527585)
    ·
      refine ⟨166210125256005200291645689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 221613500341340267055527585 166210125256005200291645689)
      ·
        refine ⟨124657593942003900218734267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 166210125256005200291645689 124657593942003900218734267)
        ·
          refine ⟨186986390913005850328101401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124657593942003900218734267 186986390913005850328101401)
          ·
            refine ⟨140239793184754387746076051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 186986390913005850328101401 140239793184754387746076051)
            ·
              refine ⟨210359689777131581619114077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 140239793184754387746076051 210359689777131581619114077)
              ·
                refine ⟨78884883666424343107167779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 210359689777131581619114077 78884883666424343107167779)
                ·
                  refine ⟨118327325499636514660751669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 78884883666424343107167779 118327325499636514660751669)
                  ·
                    refine ⟨11093186765590923249445469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 118327325499636514660751669 11093186765590923249445469)
                    ·
                      refine ⟨4159945037096596218542051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11093186765590923249445469 4159945037096596218542051)
                      ·
                        rfl

theorem cell23_8101464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 3, 1, 5, 3].length) (baseStart_8101464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8101464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8101464 prefixEnd_8101464 := by exact prefixLift 8101464
  have htrace : WordTrace (prefixWord ++ tailWord_8101464) baseStart_8101464 baseEnd_8101464 := by
    simpa [prefixWord, tailWord_8101464, baseEnd_8101464] using wordTrace_append hprefix tailTrace_8101464
  have hstable : (prefixWord ++ tailWord_8101464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8101464).length < 2 ^ (prefixWord ++ tailWord_8101464).sum := by decide
  have hdescent : baseEnd_8101464 < baseStart_8101464 := by decide
  rcases family_descends (prefixWord ++ tailWord_8101464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
