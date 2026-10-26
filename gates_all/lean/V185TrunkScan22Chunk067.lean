import V185TrunkScan22Chunk066

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_603528 : List Nat := [2, 1, 3, 3, 1, 2, 4, 1, 2, 3]
def baseStart_603528 : Nat := 118140960795 + 603528 * 2 ^ 59
def prefixEnd_603528 : Nat := 4983230072969 + 3 ^ 40 * 603528 * 2
def baseEnd_603528 : Nat := 206599968297879951749621

theorem tailTrace_603528 : CollatzResearch.WordTrace tailWord_603528 prefixEnd_603528 206599968297879951749621 := by
  unfold tailWord_603528
  simp only [CollatzResearch.WordTrace]
  refine ⟨11006237278764302610669619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14674983038352403480892825 11006237278764302610669619)
  ·
    refine ⟨16509355918146453916004429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11006237278764302610669619 16509355918146453916004429)
    ·
      refine ⟨6191008469304920218501661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16509355918146453916004429 6191008469304920218501661)
      ·
        refine ⟨2321628175989345081938123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6191008469304920218501661 2321628175989345081938123)
        ·
          refine ⟨3482442263984017622907185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2321628175989345081938123 3482442263984017622907185)
          ·
            refine ⟨2611831697988013217180389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3482442263984017622907185 2611831697988013217180389)
            ·
              refine ⟨489718443372752478221323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2611831697988013217180389 489718443372752478221323)
              ·
                refine ⟨734577665059128717331985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 489718443372752478221323 734577665059128717331985)
                ·
                  refine ⟨550933248794346537998989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 734577665059128717331985 550933248794346537998989)
                  ·
                    refine ⟨206599968297879951749621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 550933248794346537998989 206599968297879951749621)
                    ·
                      rfl

theorem cell22_603528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 4, 1, 2, 3].length) (baseStart_603528 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_603528 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_603528 prefixEnd_603528 := by exact prefixLift 603528
  have htrace : WordTrace (prefixWord ++ tailWord_603528) baseStart_603528 baseEnd_603528 := by
    simpa [prefixWord, tailWord_603528, baseEnd_603528] using wordTrace_append hprefix tailTrace_603528
  have hstable : (prefixWord ++ tailWord_603528).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_603528).length < 2 ^ (prefixWord ++ tailWord_603528).sum := by decide
  have hdescent : baseEnd_603528 < baseStart_603528 := by decide
  rcases family_descends (prefixWord ++ tailWord_603528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_603537 : List Nat := [1, 2, 2, 1, 1, 1, 2, 4, 2, 6]
def baseStart_603537 : Nat := 118140960795 + 603537 * 2 ^ 59
def prefixEnd_603537 : Nat := 4983230072969 + 3 ^ 40 * 603537 * 2
def baseEnd_603537 : Nat := 206603049181806928274593

theorem tailTrace_603537 : CollatzResearch.WordTrace tailWord_603537 prefixEnd_603537 206603049181806928274593 := by
  unfold tailWord_603537
  simp only [CollatzResearch.WordTrace]
  refine ⟨22012802814495999758416865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14675201876330666505611243 22012802814495999758416865)
  ·
    refine ⟨16509602110871999818812649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22012802814495999758416865 16509602110871999818812649)
    ·
      refine ⟨12382201583153999864109487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16509602110871999818812649 12382201583153999864109487)
      ·
        refine ⟨18573302374730999796164231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12382201583153999864109487 18573302374730999796164231)
        ·
          refine ⟨27859953562096499694246347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18573302374730999796164231 27859953562096499694246347)
          ·
            refine ⟨41789930343144749541369521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27859953562096499694246347 41789930343144749541369521)
            ·
              refine ⟨31342447757358562156027141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41789930343144749541369521 31342447757358562156027141)
              ·
                refine ⟨5876708954504730404255089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 31342447757358562156027141 5876708954504730404255089)
                ·
                  refine ⟨4407531715878547803191317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5876708954504730404255089 4407531715878547803191317)
                  ·
                    refine ⟨206603049181806928274593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4407531715878547803191317 206603049181806928274593)
                    ·
                      rfl

theorem cell22_603537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 6].length) (baseStart_603537 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_603537 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_603537 prefixEnd_603537 := by exact prefixLift 603537
  have htrace : WordTrace (prefixWord ++ tailWord_603537) baseStart_603537 baseEnd_603537 := by
    simpa [prefixWord, tailWord_603537, baseEnd_603537] using wordTrace_append hprefix tailTrace_603537
  have hstable : (prefixWord ++ tailWord_603537).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_603537).length < 2 ^ (prefixWord ++ tailWord_603537).sum := by decide
  have hdescent : baseEnd_603537 < baseStart_603537 := by decide
  rcases family_descends (prefixWord ++ tailWord_603537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_603567 : List Nat := [1, 1, 2, 1, 2, 2, 1, 2, 3, 7]
def baseStart_603567 : Nat := 118140960795 + 603567 * 2 ^ 59
def prefixEnd_603567 : Nat := 4983230072969 + 3 ^ 40 * 603567 * 2
def baseEnd_603567 : Nat := 206613318794896850024501

theorem tailTrace_603567 : CollatzResearch.WordTrace tailWord_603567 prefixEnd_603567 206613318794896850024501 := by
  unfold tailWord_603567
  simp only [CollatzResearch.WordTrace]
  refine ⟨22013897004387314882008955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14675931336258209921339303 22013897004387314882008955)
  ·
    refine ⟨33020845506580972323013433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22013897004387314882008955 33020845506580972323013433)
    ·
      refine ⟨24765634129935729242260075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33020845506580972323013433 24765634129935729242260075)
      ·
        refine ⟨37148451194903593863390113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24765634129935729242260075 37148451194903593863390113)
        ·
          refine ⟨27861338396177695397542585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37148451194903593863390113 27861338396177695397542585)
          ·
            refine ⟨20896003797133271548156939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27861338396177695397542585 20896003797133271548156939)
            ·
              refine ⟨31344005695699907322235409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20896003797133271548156939 31344005695699907322235409)
              ·
                refine ⟨23508004271774930491676557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31344005695699907322235409 23508004271774930491676557)
                ·
                  refine ⟨8815501601915598934378709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23508004271774930491676557 8815501601915598934378709)
                  ·
                    refine ⟨206613318794896850024501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 8815501601915598934378709 206613318794896850024501)
                    ·
                      rfl

theorem cell22_603567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 2, 3, 7].length) (baseStart_603567 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_603567 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_603567 prefixEnd_603567 := by exact prefixLift 603567
  have htrace : WordTrace (prefixWord ++ tailWord_603567) baseStart_603567 baseEnd_603567 := by
    simpa [prefixWord, tailWord_603567, baseEnd_603567] using wordTrace_append hprefix tailTrace_603567
  have hstable : (prefixWord ++ tailWord_603567).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_603567).length < 2 ^ (prefixWord ++ tailWord_603567).sum := by decide
  have hdescent : baseEnd_603567 < baseStart_603567 := by decide
  rcases family_descends (prefixWord ++ tailWord_603567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_603599 : List Nat := [1, 1, 2, 1, 1, 4, 4, 1, 3, 4]
def baseStart_603599 : Nat := 118140960795 + 603599 * 2 ^ 59
def prefixEnd_603599 : Nat := 4983230072969 + 3 ^ 40 * 603599 * 2
def baseEnd_603599 : Nat := 206624273048859433224403

theorem tailTrace_603599 : CollatzResearch.WordTrace tailWord_603599 prefixEnd_603599 206624273048859433224403 := by
  unfold tailWord_603599
  simp only [CollatzResearch.WordTrace]
  refine ⟨22015064140271384347173851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14676709426847589564782567 22015064140271384347173851)
  ·
    refine ⟨33022596210407076520760777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22015064140271384347173851 33022596210407076520760777)
    ·
      refine ⟨24766947157805307390570583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33022596210407076520760777 24766947157805307390570583)
      ·
        refine ⟨37150420736707961085855875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24766947157805307390570583 37150420736707961085855875)
        ·
          refine ⟨55725631105061941628783813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37150420736707961085855875 55725631105061941628783813)
          ·
            refine ⟨10448555832199114055396965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 55725631105061941628783813 10448555832199114055396965)
            ·
              refine ⟨1959104218537333885386931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10448555832199114055396965 1959104218537333885386931)
              ·
                refine ⟨2938656327806000828080397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1959104218537333885386931 2938656327806000828080397)
                ·
                  refine ⟨1101996122927250310530149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2938656327806000828080397 1101996122927250310530149)
                  ·
                    refine ⟨206624273048859433224403, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1101996122927250310530149 206624273048859433224403)
                    ·
                      rfl

theorem cell22_603599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 4, 1, 3, 4].length) (baseStart_603599 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_603599 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_603599 prefixEnd_603599 := by exact prefixLift 603599
  have htrace : WordTrace (prefixWord ++ tailWord_603599) baseStart_603599 baseEnd_603599 := by
    simpa [prefixWord, tailWord_603599, baseEnd_603599] using wordTrace_append hprefix tailTrace_603599
  have hstable : (prefixWord ++ tailWord_603599).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_603599).length < 2 ^ (prefixWord ++ tailWord_603599).sum := by decide
  have hdescent : baseEnd_603599 < baseStart_603599 := by decide
  rcases family_descends (prefixWord ++ tailWord_603599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_603631 : List Nat := [1, 1, 2, 1, 4, 1, 4, 4, 4]
def baseStart_603631 : Nat := 118140960795 + 603631 * 2 ^ 59
def prefixEnd_603631 : Nat := 4983230072969 + 3 ^ 40 * 603631 * 2
def baseEnd_603631 : Nat := 68878409100940672141435

theorem tailTrace_603631 : CollatzResearch.WordTrace tailWord_603631 prefixEnd_603631 68878409100940672141435 := by
  unfold tailWord_603631
  simp only [CollatzResearch.WordTrace]
  refine ⟨22016231276155453812338747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14677487517436969208225831 22016231276155453812338747)
  ·
    refine ⟨33024346914233180718508121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22016231276155453812338747 33024346914233180718508121)
    ·
      refine ⟨24768260185674885538881091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33024346914233180718508121 24768260185674885538881091)
      ·
        refine ⟨37152390278512328308321637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24768260185674885538881091 37152390278512328308321637)
        ·
          refine ⟨6966073177221061557810307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 37152390278512328308321637 6966073177221061557810307)
          ·
            refine ⟨10449109765831592336715461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6966073177221061557810307 10449109765831592336715461)
            ·
              refine ⟨1959208081093423563134149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10449109765831592336715461 1959208081093423563134149)
              ·
                refine ⟨367351515205016918087653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1959208081093423563134149 367351515205016918087653)
                ·
                  refine ⟨68878409100940672141435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 367351515205016918087653 68878409100940672141435)
                  ·
                    rfl

theorem cell22_603631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 4, 4, 4].length) (baseStart_603631 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_603631 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_603631 prefixEnd_603631 := by exact prefixLift 603631
  have htrace : WordTrace (prefixWord ++ tailWord_603631) baseStart_603631 baseEnd_603631 := by
    simpa [prefixWord, tailWord_603631, baseEnd_603631] using wordTrace_append hprefix tailTrace_603631
  have hstable : (prefixWord ++ tailWord_603631).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_603631).length < 2 ^ (prefixWord ++ tailWord_603631).sum := by decide
  have hdescent : baseEnd_603631 < baseStart_603631 := by decide
  rcases family_descends (prefixWord ++ tailWord_603631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_603644 : List Nat := [2, 2, 2, 1, 2, 1, 3, 2, 1, 6]
def baseStart_603644 : Nat := 118140960795 + 603644 * 2 ^ 59
def prefixEnd_603644 : Nat := 4983230072969 + 3 ^ 40 * 603644 * 2
def baseEnd_603644 : Nat := 206639677468494315849265

theorem tailTrace_603644 : CollatzResearch.WordTrace tailWord_603644 prefixEnd_603644 206639677468494315849265 := by
  unfold tailWord_603644
  simp only [CollatzResearch.WordTrace]
  refine ⟨11008352712554178516280993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14677803616738904688374657 11008352712554178516280993)
  ·
    refine ⟨8256264534415633887210745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11008352712554178516280993 8256264534415633887210745)
    ·
      refine ⟨6192198400811725415408059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8256264534415633887210745 6192198400811725415408059)
      ·
        refine ⟨9288297601217588123112089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6192198400811725415408059 9288297601217588123112089)
        ·
          refine ⟨6966223200913191092334067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9288297601217588123112089 6966223200913191092334067)
          ·
            refine ⟨10449334801369786638501101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6966223200913191092334067 10449334801369786638501101)
            ·
              refine ⟨3918500550513669989437913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10449334801369786638501101 3918500550513669989437913)
              ·
                refine ⟨2938875412885252492078435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3918500550513669989437913 2938875412885252492078435)
                ·
                  refine ⟨4408313119327878738117653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2938875412885252492078435 4408313119327878738117653)
                  ·
                    refine ⟨206639677468494315849265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4408313119327878738117653 206639677468494315849265)
                    ·
                      rfl

theorem cell22_603644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 3, 2, 1, 6].length) (baseStart_603644 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_603644 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_603644 prefixEnd_603644 := by exact prefixLift 603644
  have htrace : WordTrace (prefixWord ++ tailWord_603644) baseStart_603644 baseEnd_603644 := by
    simpa [prefixWord, tailWord_603644, baseEnd_603644] using wordTrace_append hprefix tailTrace_603644
  have hstable : (prefixWord ++ tailWord_603644).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_603644).length < 2 ^ (prefixWord ++ tailWord_603644).sum := by decide
  have hdescent : baseEnd_603644 < baseStart_603644 := by decide
  rcases family_descends (prefixWord ++ tailWord_603644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_603650 : List Nat := [3, 4, 1, 2, 1, 2, 2, 2, 1, 4]
def baseStart_603650 : Nat := 118140960795 + 603650 * 2 ^ 59
def prefixEnd_603650 : Nat := 4983230072969 + 3 ^ 40 * 603650 * 2
def baseEnd_603650 : Nat := 206641731391112300199247

theorem tailTrace_603650 : CollatzResearch.WordTrace tailWord_603650 prefixEnd_603650 206641731391112300199247 := by
  unfold tailWord_603650
  simp only [CollatzResearch.WordTrace]
  refine ⟨5504231065771655014320101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14677949508724413371520269 5504231065771655014320101)
  ·
    refine ⟨1032043324832185315185019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5504231065771655014320101 1032043324832185315185019)
    ·
      refine ⟨1548064987248277972777529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1032043324832185315185019 1548064987248277972777529)
      ·
        refine ⟨1161048740436208479583147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1548064987248277972777529 1161048740436208479583147)
        ·
          refine ⟨1741573110654312719374721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1161048740436208479583147 1741573110654312719374721)
          ·
            refine ⟨1306179832990734539531041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1741573110654312719374721 1306179832990734539531041)
            ·
              refine ⟨979634874743050904648281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1306179832990734539531041 979634874743050904648281)
              ·
                refine ⟨734726156057288178486211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 979634874743050904648281 734726156057288178486211)
                ·
                  refine ⟨1102089234085932267729317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 734726156057288178486211 1102089234085932267729317)
                  ·
                    refine ⟨206641731391112300199247, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1102089234085932267729317 206641731391112300199247)
                    ·
                      rfl

theorem cell22_603650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 2, 2, 2, 1, 4].length) (baseStart_603650 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_603650 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_603650 prefixEnd_603650 := by exact prefixLift 603650
  have htrace : WordTrace (prefixWord ++ tailWord_603650) baseStart_603650 baseEnd_603650 := by
    simpa [prefixWord, tailWord_603650, baseEnd_603650] using wordTrace_append hprefix tailTrace_603650
  have hstable : (prefixWord ++ tailWord_603650).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_603650).length < 2 ^ (prefixWord ++ tailWord_603650).sum := by decide
  have hdescent : baseEnd_603650 < baseStart_603650 := by decide
  rcases family_descends (prefixWord ++ tailWord_603650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_603751 : List Nat := [1, 1, 5, 1, 1, 1, 3, 2, 3, 4]
def baseStart_603751 : Nat := 118140960795 + 603751 * 2 ^ 59
def prefixEnd_603751 : Nat := 4983230072969 + 3 ^ 40 * 603751 * 2
def baseEnd_603751 : Nat := 206676305755181703423937

theorem tailTrace_603751 : CollatzResearch.WordTrace tailWord_603751 prefixEnd_603751 206676305755181703423937 := by
  unfold tailWord_603751
  simp only [CollatzResearch.WordTrace]
  refine ⟨22020608035720714306707107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14680405357147142871138071 22020608035720714306707107)
  ·
    refine ⟨33030912053581071460060661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22020608035720714306707107 33030912053581071460060661)
    ·
      refine ⟨3096648005023225449380687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 33030912053581071460060661 3096648005023225449380687)
      ·
        refine ⟨4644972007534838174071031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3096648005023225449380687 4644972007534838174071031)
        ·
          refine ⟨6967458011302257261106547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4644972007534838174071031 6967458011302257261106547)
          ·
            refine ⟨10451187016953385891659821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6967458011302257261106547 10451187016953385891659821)
            ·
              refine ⟨3919195131357519709372433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10451187016953385891659821 3919195131357519709372433)
              ·
                refine ⟨2939396348518139782029325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3919195131357519709372433 2939396348518139782029325)
                ·
                  refine ⟨1102273630694302418260997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2939396348518139782029325 1102273630694302418260997)
                  ·
                    refine ⟨206676305755181703423937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1102273630694302418260997 206676305755181703423937)
                    ·
                      rfl

theorem cell22_603751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 3, 2, 3, 4].length) (baseStart_603751 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_603751 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_603751 prefixEnd_603751 := by exact prefixLift 603751
  have htrace : WordTrace (prefixWord ++ tailWord_603751) baseStart_603751 baseEnd_603751 := by
    simpa [prefixWord, tailWord_603751, baseEnd_603751] using wordTrace_append hprefix tailTrace_603751
  have hstable : (prefixWord ++ tailWord_603751).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_603751).length < 2 ^ (prefixWord ++ tailWord_603751).sum := by decide
  have hdescent : baseEnd_603751 < baseStart_603751 := by decide
  rcases family_descends (prefixWord ++ tailWord_603751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_603781 : List Nat := [1, 3, 1, 1, 4, 1, 1, 4, 1, 5]
def baseStart_603781 : Nat := 118140960795 + 603781 * 2 ^ 59
def prefixEnd_603781 : Nat := 4983230072969 + 3 ^ 40 * 603781 * 2
def baseEnd_603781 : Nat := 206686575368271625173845

theorem tailTrace_603781 : CollatzResearch.WordTrace tailWord_603781 prefixEnd_603781 206686575368271625173845 := by
  unfold tailWord_603781
  simp only [CollatzResearch.WordTrace]
  refine ⟨22021702225612029430299197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14681134817074686286866131 22021702225612029430299197)
  ·
    refine ⟨8258138334604511036362199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22021702225612029430299197 8258138334604511036362199)
    ·
      refine ⟨12387207501906766554543299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8258138334604511036362199 12387207501906766554543299)
      ·
        refine ⟨18580811252860149831814949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12387207501906766554543299 18580811252860149831814949)
        ·
          refine ⟨3483902109911278093465303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18580811252860149831814949 3483902109911278093465303)
          ·
            refine ⟨5225853164866917140197955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3483902109911278093465303 5225853164866917140197955)
            ·
              refine ⟨7838779747300375710296933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5225853164866917140197955 7838779747300375710296933)
              ·
                refine ⟨1469771202618820445680675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7838779747300375710296933 1469771202618820445680675)
                ·
                  refine ⟨2204656803928230668521013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1469771202618820445680675 2204656803928230668521013)
                  ·
                    refine ⟨206686575368271625173845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2204656803928230668521013 206686575368271625173845)
                    ·
                      rfl

theorem cell22_603781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 1, 4, 1, 5].length) (baseStart_603781 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_603781 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_603781 prefixEnd_603781 := by exact prefixLift 603781
  have htrace : WordTrace (prefixWord ++ tailWord_603781) baseStart_603781 baseEnd_603781 := by
    simpa [prefixWord, tailWord_603781, baseEnd_603781] using wordTrace_append hprefix tailTrace_603781
  have hstable : (prefixWord ++ tailWord_603781).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_603781).length < 2 ^ (prefixWord ++ tailWord_603781).sum := by decide
  have hdescent : baseEnd_603781 < baseStart_603781 := by decide
  rcases family_descends (prefixWord ++ tailWord_603781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_603783 : List Nat := [1, 1, 4, 2, 1, 3, 1, 5, 4]
def baseStart_603783 : Nat := 118140960795 + 603783 * 2 ^ 59
def prefixEnd_603783 : Nat := 4983230072969 + 3 ^ 40 * 603783 * 2
def baseEnd_603783 : Nat := 68895753336381428874613

theorem tailTrace_603783 : CollatzResearch.WordTrace tailWord_603783 prefixEnd_603783 68895753336381428874613 := by
  unfold tailWord_603783
  simp only [CollatzResearch.WordTrace]
  refine ⟨22021775171604783771872003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14681183447736522514581335 22021775171604783771872003)
  ·
    refine ⟨33032662757407175657808005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22021775171604783771872003 33032662757407175657808005)
    ·
      refine ⟨6193624267013845435839001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 33032662757407175657808005 6193624267013845435839001)
      ·
        refine ⟨4645218200260384076879251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6193624267013845435839001 4645218200260384076879251)
        ·
          refine ⟨6967827300390576115318877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4645218200260384076879251 6967827300390576115318877)
          ·
            refine ⟨2612935237646466043244579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6967827300390576115318877 2612935237646466043244579)
            ·
              refine ⟨3919402856469699064866869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2612935237646466043244579 3919402856469699064866869)
              ·
                refine ⟨367444017794034287331269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3919402856469699064866869 367444017794034287331269)
                ·
                  refine ⟨68895753336381428874613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 367444017794034287331269 68895753336381428874613)
                  ·
                    rfl

theorem cell22_603783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 1, 5, 4].length) (baseStart_603783 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_603783 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_603783 prefixEnd_603783 := by exact prefixLift 603783
  have htrace : WordTrace (prefixWord ++ tailWord_603783) baseStart_603783 baseEnd_603783 := by
    simpa [prefixWord, tailWord_603783, baseEnd_603783] using wordTrace_append hprefix tailTrace_603783
  have hstable : (prefixWord ++ tailWord_603783).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_603783).length < 2 ^ (prefixWord ++ tailWord_603783).sum := by decide
  have hdescent : baseEnd_603783 < baseStart_603783 := by decide
  rcases family_descends (prefixWord ++ tailWord_603783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_603830 : List Nat := [5, 1, 3, 1, 1, 1, 2, 1, 1, 6]
def baseStart_603830 : Nat := 118140960795 + 603830 * 2 ^ 59
def prefixEnd_603830 : Nat := 4983230072969 + 3 ^ 40 * 603830 * 2
def baseEnd_603830 : Nat := 206703349069651830698695

theorem tailTrace_603830 : CollatzResearch.WordTrace tailWord_603830 prefixEnd_603830 206703349069651830698695 := by
  unfold tailWord_603830
  simp only [CollatzResearch.WordTrace]
  refine ⟨1376468087652156924927059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 14682326268289673865888629 1376468087652156924927059)
  ·
    refine ⟨2064702131478235387390589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1376468087652156924927059 2064702131478235387390589)
    ·
      refine ⟨774263299304338270271471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2064702131478235387390589 774263299304338270271471)
      ·
        refine ⟨1161394948956507405407207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 774263299304338270271471 1161394948956507405407207)
        ·
          refine ⟨1742092423434761108110811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1161394948956507405407207 1742092423434761108110811)
          ·
            refine ⟨2613138635152141662166217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1742092423434761108110811 2613138635152141662166217)
            ·
              refine ⟨1959853976364106246624663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2613138635152141662166217 1959853976364106246624663)
              ·
                refine ⟨2939780964546159369936995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1959853976364106246624663 2939780964546159369936995)
                ·
                  refine ⟨4409671446819239054905493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2939780964546159369936995 4409671446819239054905493)
                  ·
                    refine ⟨206703349069651830698695, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4409671446819239054905493 206703349069651830698695)
                    ·
                      rfl

theorem cell22_603830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 2, 1, 1, 6].length) (baseStart_603830 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_603830 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_603830 prefixEnd_603830 := by exact prefixLift 603830
  have htrace : WordTrace (prefixWord ++ tailWord_603830) baseStart_603830 baseEnd_603830 := by
    simpa [prefixWord, tailWord_603830, baseEnd_603830] using wordTrace_append hprefix tailTrace_603830
  have hstable : (prefixWord ++ tailWord_603830).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_603830).length < 2 ^ (prefixWord ++ tailWord_603830).sum := by decide
  have hdescent : baseEnd_603830 < baseStart_603830 := by decide
  rcases family_descends (prefixWord ++ tailWord_603830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_603862 : List Nat := [5, 2, 1, 3, 1, 1, 2, 7]
def baseStart_603862 : Nat := 118140960795 + 603862 * 2 ^ 59
def prefixEnd_603862 : Nat := 4983230072969 + 3 ^ 40 * 603862 * 2
def baseEnd_603862 : Nat := 22968255924846045988733

theorem tailTrace_603862 : CollatzResearch.WordTrace tailWord_603862 prefixEnd_603862 22968255924846045988733 := by
  unfold tailWord_603862
  simp only [CollatzResearch.WordTrace]
  refine ⟨1376541033644911266499865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 14683104358879053509331893 1376541033644911266499865)
  ·
    refine ⟨1032405775233683449874899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1376541033644911266499865 1032405775233683449874899)
    ·
      refine ⟨1548608662850525174812349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1032405775233683449874899 1548608662850525174812349)
      ·
        refine ⟨580728248568946940554631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1548608662850525174812349 580728248568946940554631)
        ·
          refine ⟨871092372853420410831947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 580728248568946940554631 871092372853420410831947)
          ·
            refine ⟨1306638559280130616247921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 871092372853420410831947 1306638559280130616247921)
            ·
              refine ⟨979978919460097962185941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1306638559280130616247921 979978919460097962185941)
              ·
                refine ⟨22968255924846045988733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 979978919460097962185941 22968255924846045988733)
                ·
                  rfl

theorem cell22_603862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 1, 2, 7].length) (baseStart_603862 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_603862 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_603862 prefixEnd_603862 := by exact prefixLift 603862
  have htrace : WordTrace (prefixWord ++ tailWord_603862) baseStart_603862 baseEnd_603862 := by
    simpa [prefixWord, tailWord_603862, baseEnd_603862] using wordTrace_append hprefix tailTrace_603862
  have hstable : (prefixWord ++ tailWord_603862).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_603862).length < 2 ^ (prefixWord ++ tailWord_603862).sum := by decide
  have hdescent : baseEnd_603862 < baseStart_603862 := by decide
  rcases family_descends (prefixWord ++ tailWord_603862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_603871 : List Nat := [1, 1, 2, 3, 2, 2, 2, 1, 1, 7]
def baseStart_603871 : Nat := 118140960795 + 603871 * 2 ^ 59
def prefixEnd_603871 : Nat := 4983230072969 + 3 ^ 40 * 603871 * 2
def baseEnd_603871 : Nat := 206717384207541390423569

theorem tailTrace_603871 : CollatzResearch.WordTrace tailWord_603871 prefixEnd_603871 206717384207541390423569 := by
  unfold tailWord_603871
  simp only [CollatzResearch.WordTrace]
  refine ⟨22024984795285974801075467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14683323196857316534050311 22024984795285974801075467)
  ·
    refine ⟨33037477192928962201613201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22024984795285974801075467 33037477192928962201613201)
    ·
      refine ⟨24778107894696721651209901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33037477192928962201613201 24778107894696721651209901)
      ·
        refine ⟨9291790460511270619203713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24778107894696721651209901 9291790460511270619203713)
        ·
          refine ⟨6968842845383452964402785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9291790460511270619203713 6968842845383452964402785)
          ·
            refine ⟨5226632134037589723302089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6968842845383452964402785 5226632134037589723302089)
            ·
              refine ⟨3919974100528192292476567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5226632134037589723302089 3919974100528192292476567)
              ·
                refine ⟨5879961150792288438714851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3919974100528192292476567 5879961150792288438714851)
                ·
                  refine ⟨8819941726188432658072277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5879961150792288438714851 8819941726188432658072277)
                  ·
                    refine ⟨206717384207541390423569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 8819941726188432658072277 206717384207541390423569)
                    ·
                      rfl

theorem cell22_603871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 2, 1, 1, 7].length) (baseStart_603871 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_603871 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_603871 prefixEnd_603871 := by exact prefixLift 603871
  have htrace : WordTrace (prefixWord ++ tailWord_603871) baseStart_603871 baseEnd_603871 := by
    simpa [prefixWord, tailWord_603871, baseEnd_603871] using wordTrace_append hprefix tailTrace_603871
  have hstable : (prefixWord ++ tailWord_603871).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_603871).length < 2 ^ (prefixWord ++ tailWord_603871).sum := by decide
  have hdescent : baseEnd_603871 < baseStart_603871 := by decide
  rcases family_descends (prefixWord ++ tailWord_603871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_603901 : List Nat := [1, 4, 1, 1, 1, 1, 2, 1, 10]
def baseStart_603901 : Nat := 118140960795 + 603901 * 2 ^ 59
def prefixEnd_603901 : Nat := 4983230072969 + 3 ^ 40 * 603901 * 2
def baseEnd_603901 : Nat := 68909217940210437391159

theorem tailTrace_603901 : CollatzResearch.WordTrace tailWord_603901 prefixEnd_603901 68909217940210437391159 := by
  unfold tailWord_603901
  simp only [CollatzResearch.WordTrace]
  refine ⟨22026078985177289924667557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14684052656784859949778371 22026078985177289924667557)
  ·
    refine ⟨4129889809720741860875167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 22026078985177289924667557 4129889809720741860875167)
    ·
      refine ⟨6194834714581112791312751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4129889809720741860875167 6194834714581112791312751)
      ·
        refine ⟨9292252071871669186969127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6194834714581112791312751 9292252071871669186969127)
        ·
          refine ⟨13938378107807503780453691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9292252071871669186969127 13938378107807503780453691)
          ·
            refine ⟨20907567161711255670680537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13938378107807503780453691 20907567161711255670680537)
            ·
              refine ⟨15680675371283441753010403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20907567161711255670680537 15680675371283441753010403)
              ·
                refine ⟨23521013056925162629515605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15680675371283441753010403 23521013056925162629515605)
                ·
                  refine ⟨68909217940210437391159, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 23521013056925162629515605 68909217940210437391159)
                  ·
                    rfl

theorem cell22_603901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 1, 10].length) (baseStart_603901 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_603901 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_603901 prefixEnd_603901 := by exact prefixLift 603901
  have htrace : WordTrace (prefixWord ++ tailWord_603901) baseStart_603901 baseEnd_603901 := by
    simpa [prefixWord, tailWord_603901, baseEnd_603901] using wordTrace_append hprefix tailTrace_603901
  have hstable : (prefixWord ++ tailWord_603901).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_603901).length < 2 ^ (prefixWord ++ tailWord_603901).sum := by decide
  have hdescent : baseEnd_603901 < baseStart_603901 := by decide
  rcases family_descends (prefixWord ++ tailWord_603901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_603903 : List Nat := [1, 1, 2, 2, 1, 3, 2, 5, 1, 4]
def baseStart_603903 : Nat := 118140960795 + 603903 * 2 ^ 59
def prefixEnd_603903 : Nat := 4983230072969 + 3 ^ 40 * 603903 * 2
def baseEnd_603903 : Nat := 206728338461503973623471

theorem tailTrace_603903 : CollatzResearch.WordTrace tailWord_603903 prefixEnd_603903 206728338461503973623471 := by
  unfold tailWord_603903
  simp only [CollatzResearch.WordTrace]
  refine ⟨22026151931170044266240363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14684101287446696177493575 22026151931170044266240363)
  ·
    refine ⟨33039227896755066399360545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22026151931170044266240363 33039227896755066399360545)
    ·
      refine ⟨24779420922566299799520409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33039227896755066399360545 24779420922566299799520409)
      ·
        refine ⟨18584565691924724849640307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24779420922566299799520409 18584565691924724849640307)
        ·
          refine ⟨27876848537887087274460461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18584565691924724849640307 27876848537887087274460461)
          ·
            refine ⟨10453818201707657727922673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27876848537887087274460461 10453818201707657727922673)
            ·
              refine ⟨7840363651280743295942005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10453818201707657727922673 7840363651280743295942005)
              ·
                refine ⟨735034092307569683994563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 7840363651280743295942005 735034092307569683994563)
                ·
                  refine ⟨1102551138461354525991845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 735034092307569683994563 1102551138461354525991845)
                  ·
                    refine ⟨206728338461503973623471, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1102551138461354525991845 206728338461503973623471)
                    ·
                      rfl

theorem cell22_603903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 2, 5, 1, 4].length) (baseStart_603903 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_603903 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_603903 prefixEnd_603903 := by exact prefixLift 603903
  have htrace : WordTrace (prefixWord ++ tailWord_603903) baseStart_603903 baseEnd_603903 := by
    simpa [prefixWord, tailWord_603903, baseEnd_603903] using wordTrace_append hprefix tailTrace_603903
  have hstable : (prefixWord ++ tailWord_603903).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_603903).length < 2 ^ (prefixWord ++ tailWord_603903).sum := by decide
  have hdescent : baseEnd_603903 < baseStart_603903 := by decide
  rcases family_descends (prefixWord ++ tailWord_603903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_603911 : List Nat := [1, 1, 4, 4, 2, 2, 2, 2, 1, 3]
def baseStart_603911 : Nat := 118140960795 + 603911 * 2 ^ 59
def prefixEnd_603911 : Nat := 4983230072969 + 3 ^ 40 * 603911 * 2
def baseEnd_603911 : Nat := 206731077024994619423447

theorem tailTrace_603911 : CollatzResearch.WordTrace tailWord_603911 prefixEnd_603911 206731077024994619423447 := by
  unfold tailWord_603911
  simp only [CollatzResearch.WordTrace]
  refine ⟨22026443715141061632531587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14684295810094041088354391 22026443715141061632531587)
  ·
    refine ⟨33039665572711592448797381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22026443715141061632531587 33039665572711592448797381)
    ·
      refine ⟨6194937294883423584149509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 33039665572711592448797381 6194937294883423584149509)
      ·
        refine ⟨1161550742790641922028033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6194937294883423584149509 1161550742790641922028033)
        ·
          refine ⟨871163057092981441521025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1161550742790641922028033 871163057092981441521025)
          ·
            refine ⟨653372292819736081140769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 871163057092981441521025 653372292819736081140769)
            ·
              refine ⟨490029219614802060855577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 653372292819736081140769 490029219614802060855577)
              ·
                refine ⟨367521914711101545641683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 490029219614802060855577 367521914711101545641683)
                ·
                  refine ⟨551282872066652318462525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 367521914711101545641683 551282872066652318462525)
                  ·
                    refine ⟨206731077024994619423447, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 551282872066652318462525 206731077024994619423447)
                    ·
                      rfl

theorem cell22_603911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 2, 2, 2, 1, 3].length) (baseStart_603911 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_603911 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_603911 prefixEnd_603911 := by exact prefixLift 603911
  have htrace : WordTrace (prefixWord ++ tailWord_603911) baseStart_603911 baseEnd_603911 := by
    simpa [prefixWord, tailWord_603911, baseEnd_603911] using wordTrace_append hprefix tailTrace_603911
  have hstable : (prefixWord ++ tailWord_603911).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_603911).length < 2 ^ (prefixWord ++ tailWord_603911).sum := by decide
  have hdescent : baseEnd_603911 < baseStart_603911 := by decide
  rcases family_descends (prefixWord ++ tailWord_603911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_603931 : List Nat := [1, 1, 1, 1, 1, 1, 4, 3, 3, 6]
def baseStart_603931 : Nat := 118140960795 + 603931 * 2 ^ 59
def prefixEnd_603931 : Nat := 4983230072969 + 3 ^ 40 * 603931 * 2
def baseEnd_603931 : Nat := 206737923433721233923385

theorem tailTrace_603931 : CollatzResearch.WordTrace tailWord_603931 prefixEnd_603931 206737923433721233923385 := by
  unfold tailWord_603931
  simp only [CollatzResearch.WordTrace]
  refine ⟨22027173175068605048259647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14684782116712403365506431 22027173175068605048259647)
  ·
    refine ⟨33040759762602907572389471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22027173175068605048259647 33040759762602907572389471)
    ·
      refine ⟨49561139643904361358584207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33040759762602907572389471 49561139643904361358584207)
      ·
        refine ⟨74341709465856542037876311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49561139643904361358584207 74341709465856542037876311)
        ·
          refine ⟨111512564198784813056814467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74341709465856542037876311 111512564198784813056814467)
          ·
            refine ⟨167268846298177219585221701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 111512564198784813056814467 167268846298177219585221701)
            ·
              refine ⟨31362908680908228672229069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 167268846298177219585221701 31362908680908228672229069)
              ·
                refine ⟨11761090755340585752085901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31362908680908228672229069 11761090755340585752085901)
                ·
                  refine ⟨4410409033252719657032213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11761090755340585752085901 4410409033252719657032213)
                  ·
                    refine ⟨206737923433721233923385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4410409033252719657032213 206737923433721233923385)
                    ·
                      rfl

theorem cell22_603931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 3, 3, 6].length) (baseStart_603931 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_603931 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_603931 prefixEnd_603931 := by exact prefixLift 603931
  have htrace : WordTrace (prefixWord ++ tailWord_603931) baseStart_603931 baseEnd_603931 := by
    simpa [prefixWord, tailWord_603931, baseEnd_603931] using wordTrace_append hprefix tailTrace_603931
  have hstable : (prefixWord ++ tailWord_603931).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_603931).length < 2 ^ (prefixWord ++ tailWord_603931).sum := by decide
  have hdescent : baseEnd_603931 < baseStart_603931 := by decide
  rcases family_descends (prefixWord ++ tailWord_603931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_603948 : List Nat := [2, 2, 1, 1, 1, 6, 1, 1, 1, 6]
def baseStart_603948 : Nat := 118140960795 + 603948 * 2 ^ 59
def prefixEnd_603948 : Nat := 4983230072969 + 3 ^ 40 * 603948 * 2
def baseEnd_603948 : Nat := 206743742881138856248333

theorem tailTrace_603948 : CollatzResearch.WordTrace tailWord_603948 prefixEnd_603948 206743742881138856248333 := by
  unfold tailWord_603948
  simp only [CollatzResearch.WordTrace]
  refine ⟨11013896608003508475814249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14685195477338011301085665 11013896608003508475814249)
  ·
    refine ⟨8260422456002631356860687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11013896608003508475814249 8260422456002631356860687)
    ·
      refine ⟨12390633684003947035291031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8260422456002631356860687 12390633684003947035291031)
      ·
        refine ⟨18585950526005920552936547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12390633684003947035291031 18585950526005920552936547)
        ·
          refine ⟨27878925789008880829404821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18585950526005920552936547 27878925789008880829404821)
          ·
            refine ⟨1306824646359791288878351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 27878925789008880829404821 1306824646359791288878351)
            ·
              refine ⟨1960236969539686933317527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1306824646359791288878351 1960236969539686933317527)
              ·
                refine ⟨2940355454309530399976291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1960236969539686933317527 2940355454309530399976291)
                ·
                  refine ⟨4410533181464295599964437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2940355454309530399976291 4410533181464295599964437)
                  ·
                    refine ⟨206743742881138856248333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4410533181464295599964437 206743742881138856248333)
                    ·
                      rfl

theorem cell22_603948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 6].length) (baseStart_603948 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_603948 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_603948 prefixEnd_603948 := by exact prefixLift 603948
  have htrace : WordTrace (prefixWord ++ tailWord_603948) baseStart_603948 baseEnd_603948 := by
    simpa [prefixWord, tailWord_603948, baseEnd_603948] using wordTrace_append hprefix tailTrace_603948
  have hstable : (prefixWord ++ tailWord_603948).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_603948).length < 2 ^ (prefixWord ++ tailWord_603948).sum := by decide
  have hdescent : baseEnd_603948 < baseStart_603948 := by decide
  rcases family_descends (prefixWord ++ tailWord_603948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_604008 : List Nat := [2, 1, 4, 2, 1, 1, 1, 1, 9]
def baseStart_604008 : Nat := 118140960795 + 604008 * 2 ^ 59
def prefixEnd_604008 : Nat := 4983230072969 + 3 ^ 40 * 604008 * 2
def baseEnd_604008 : Nat := 68921427369106233249383

theorem tailTrace_604008 : CollatzResearch.WordTrace tailWord_604008 prefixEnd_604008 68921427369106233249383 := by
  unfold tailWord_604008
  simp only [CollatzResearch.WordTrace]
  refine ⟨11014990797894823599406339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14686654397193098132541785 11014990797894823599406339)
  ·
    refine ⟨16522486196842235399109509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11014990797894823599406339 16522486196842235399109509)
    ·
      refine ⟨3097966161907919137333033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 16522486196842235399109509 3097966161907919137333033)
      ·
        refine ⟨2323474621430939352999775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3097966161907919137333033 2323474621430939352999775)
        ·
          refine ⟨3485211932146409029499663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2323474621430939352999775 3485211932146409029499663)
          ·
            refine ⟨5227817898219613544249495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3485211932146409029499663 5227817898219613544249495)
            ·
              refine ⟨7841726847329420316374243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5227817898219613544249495 7841726847329420316374243)
              ·
                refine ⟨11762590270994130474561365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7841726847329420316374243 11762590270994130474561365)
                ·
                  refine ⟨68921427369106233249383, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 11762590270994130474561365 68921427369106233249383)
                  ·
                    rfl

theorem cell22_604008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 1, 1, 9].length) (baseStart_604008 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_604008 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_604008 prefixEnd_604008 := by exact prefixLift 604008
  have htrace : WordTrace (prefixWord ++ tailWord_604008) baseStart_604008 baseEnd_604008 := by
    simpa [prefixWord, tailWord_604008, baseEnd_604008] using wordTrace_append hprefix tailTrace_604008
  have hstable : (prefixWord ++ tailWord_604008).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_604008).length < 2 ^ (prefixWord ++ tailWord_604008).sum := by decide
  have hdescent : baseEnd_604008 < baseStart_604008 := by decide
  rcases family_descends (prefixWord ++ tailWord_604008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_604042 : List Nat := [3, 1, 2, 4, 2, 1, 1, 3, 5]
def baseStart_604042 : Nat := 118140960795 + 604042 * 2 ^ 59
def prefixEnd_604042 : Nat := 4983230072969 + 3 ^ 40 * 604042 * 2
def baseEnd_604042 : Nat := 68925307000717981466015

theorem tailTrace_604042 : CollatzResearch.WordTrace tailWord_604042 prefixEnd_604042 68925307000717981466015 := by
  unfold tailWord_604042
  simp only [CollatzResearch.WordTrace]
  refine ⟨5507805419416617751387595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14687481118444314003700253 5507805419416617751387595)
  ·
    refine ⟨8261708129124926627081393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5507805419416617751387595 8261708129124926627081393)
    ·
      refine ⟨6196281096843694970311045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8261708129124926627081393 6196281096843694970311045)
      ·
        refine ⟨1161802705658192806933321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6196281096843694970311045 1161802705658192806933321)
        ·
          refine ⟨871352029243644605199991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1161802705658192806933321 871352029243644605199991)
          ·
            refine ⟨1307028043865466907799987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 871352029243644605199991 1307028043865466907799987)
            ·
              refine ⟨1960542065798200361699981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1307028043865466907799987 1960542065798200361699981)
              ·
                refine ⟨735203274674325135637493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1960542065798200361699981 735203274674325135637493)
                ·
                  refine ⟨68925307000717981466015, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 735203274674325135637493 68925307000717981466015)
                  ·
                    rfl

theorem cell22_604042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 1, 1, 3, 5].length) (baseStart_604042 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_604042 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_604042 prefixEnd_604042 := by exact prefixLift 604042
  have htrace : WordTrace (prefixWord ++ tailWord_604042) baseStart_604042 baseEnd_604042 := by
    simpa [prefixWord, tailWord_604042, baseEnd_604042] using wordTrace_append hprefix tailTrace_604042
  have hstable : (prefixWord ++ tailWord_604042).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_604042).length < 2 ^ (prefixWord ++ tailWord_604042).sum := by decide
  have hdescent : baseEnd_604042 < baseStart_604042 := by decide
  rcases family_descends (prefixWord ++ tailWord_604042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_604053 : List Nat := [1, 3, 2, 1, 1, 3, 2, 1, 8]
def baseStart_604053 : Nat := 118140960795 + 604053 * 2 ^ 59
def prefixEnd_604053 : Nat := 4983230072969 + 3 ^ 40 * 604053 * 2
def baseEnd_604053 : Nat := 68926562175651194124337

theorem tailTrace_604053 : CollatzResearch.WordTrace tailWord_604053 prefixEnd_604053 68926562175651194124337 := by
  unfold tailWord_604053
  simp only [CollatzResearch.WordTrace]
  refine ⟨22031622880626619884200813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14687748587084413256133875 22031622880626619884200813)
  ·
    refine ⟨8261858580234982456575305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22031622880626619884200813 8261858580234982456575305)
    ·
      refine ⟨6196393935176236842431479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8261858580234982456575305 6196393935176236842431479)
      ·
        refine ⟨9294590902764355263647219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6196393935176236842431479 9294590902764355263647219)
        ·
          refine ⟨13941886354146532895470829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9294590902764355263647219 13941886354146532895470829)
          ·
            refine ⟨5228207382804949835801561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13941886354146532895470829 5228207382804949835801561)
            ·
              refine ⟨3921155537103712376851171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5228207382804949835801561 3921155537103712376851171)
              ·
                refine ⟨5881733305655568565276757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3921155537103712376851171 5881733305655568565276757)
                ·
                  refine ⟨68926562175651194124337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 5881733305655568565276757 68926562175651194124337)
                  ·
                    rfl

theorem cell22_604053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 2, 1, 8].length) (baseStart_604053 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_604053 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_604053 prefixEnd_604053 := by exact prefixLift 604053
  have htrace : WordTrace (prefixWord ++ tailWord_604053) baseStart_604053 baseEnd_604053 := by
    simpa [prefixWord, tailWord_604053, baseEnd_604053] using wordTrace_append hprefix tailTrace_604053
  have hstable : (prefixWord ++ tailWord_604053).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_604053).length < 2 ^ (prefixWord ++ tailWord_604053).sum := by decide
  have hdescent : baseEnd_604053 < baseStart_604053 := by decide
  rcases family_descends (prefixWord ++ tailWord_604053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_604055 : List Nat := [1, 1, 3, 3, 1, 4, 1, 1, 3, 4]
def baseStart_604055 : Nat := 118140960795 + 604055 * 2 ^ 59
def prefixEnd_604055 : Nat := 4983230072969 + 3 ^ 40 * 604055 * 2
def baseEnd_604055 : Nat := 206780371167826243823005

theorem tailTrace_604055 : CollatzResearch.WordTrace tailWord_604055 prefixEnd_604055 206780371167826243823005 := by
  unfold tailWord_604055
  simp only [CollatzResearch.WordTrace]
  refine ⟨22031695826619374225773619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14687797217746249483849079 22031695826619374225773619)
  ·
    refine ⟨33047543739929061338660429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22031695826619374225773619 33047543739929061338660429)
    ·
      refine ⟨12392828902473398001997661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33047543739929061338660429 12392828902473398001997661)
      ·
        refine ⟨4647310838427524250749123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12392828902473398001997661 4647310838427524250749123)
        ·
          refine ⟨6970966257641286376123685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4647310838427524250749123 6970966257641286376123685)
          ·
            refine ⟨1307056173307741195523191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6970966257641286376123685 1307056173307741195523191)
            ·
              refine ⟨1960584259961611793284787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1307056173307741195523191 1960584259961611793284787)
              ·
                refine ⟨2940876389942417689927181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1960584259961611793284787 2940876389942417689927181)
                ·
                  refine ⟨1102828646228406633722693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2940876389942417689927181 1102828646228406633722693)
                  ·
                    refine ⟨206780371167826243823005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1102828646228406633722693 206780371167826243823005)
                    ·
                      rfl

theorem cell22_604055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 4, 1, 1, 3, 4].length) (baseStart_604055 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_604055 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_604055 prefixEnd_604055 := by exact prefixLift 604055
  have htrace : WordTrace (prefixWord ++ tailWord_604055) baseStart_604055 baseEnd_604055 := by
    simpa [prefixWord, tailWord_604055, baseEnd_604055] using wordTrace_append hprefix tailTrace_604055
  have hstable : (prefixWord ++ tailWord_604055).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_604055).length < 2 ^ (prefixWord ++ tailWord_604055).sum := by decide
  have hdescent : baseEnd_604055 < baseStart_604055 := by decide
  rcases family_descends (prefixWord ++ tailWord_604055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_604113 : List Nat := [1, 2, 2, 1, 2, 1, 2, 1, 1, 9]
def baseStart_604113 : Nat := 118140960795 + 604113 * 2 ^ 59
def prefixEnd_604113 : Nat := 4983230072969 + 3 ^ 40 * 604113 * 2
def baseEnd_604113 : Nat := 206800225753133425872827

theorem tailTrace_604113 : CollatzResearch.WordTrace tailWord_604113 prefixEnd_604113 206800225753133425872827 := by
  unfold tailWord_604113
  simp only [CollatzResearch.WordTrace]
  refine ⟨22033811260409250131384993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14689207506939500087589995 22033811260409250131384993)
  ·
    refine ⟨16525358445306937598538745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22033811260409250131384993 16525358445306937598538745)
    ·
      refine ⟨12394018833980203198904059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16525358445306937598538745 12394018833980203198904059)
      ·
        refine ⟨18591028250970304798356089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12394018833980203198904059 18591028250970304798356089)
        ·
          refine ⟨13943271188227728598767067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18591028250970304798356089 13943271188227728598767067)
          ·
            refine ⟨20914906782341592898150601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13943271188227728598767067 20914906782341592898150601)
            ·
              refine ⟨15686180086756194673612951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20914906782341592898150601 15686180086756194673612951)
              ·
                refine ⟨23529270130134292010419427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15686180086756194673612951 23529270130134292010419427)
                ·
                  refine ⟨35293905195201438015629141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23529270130134292010419427 35293905195201438015629141)
                  ·
                    refine ⟨206800225753133425872827, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 35293905195201438015629141 206800225753133425872827)
                    ·
                      rfl

theorem cell22_604113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 1, 1, 9].length) (baseStart_604113 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_604113 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_604113 prefixEnd_604113 := by exact prefixLift 604113
  have htrace : WordTrace (prefixWord ++ tailWord_604113) baseStart_604113 baseEnd_604113 := by
    simpa [prefixWord, tailWord_604113, baseEnd_604113] using wordTrace_append hprefix tailTrace_604113
  have hstable : (prefixWord ++ tailWord_604113).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_604113).length < 2 ^ (prefixWord ++ tailWord_604113).sum := by decide
  have hdescent : baseEnd_604113 < baseStart_604113 := by decide
  rcases family_descends (prefixWord ++ tailWord_604113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_604117 : List Nat := [1, 3, 2, 3, 2, 1, 3, 1, 2, 4]
def baseStart_604117 : Nat := 118140960795 + 604117 * 2 ^ 59
def prefixEnd_604117 : Nat := 4983230072969 + 3 ^ 40 * 604117 * 2
def baseEnd_604117 : Nat := 206801595034878748772815

theorem tailTrace_604117 : CollatzResearch.WordTrace tailWord_604117 prefixEnd_604117 206801595034878748772815 := by
  unfold tailWord_604117
  simp only [CollatzResearch.WordTrace]
  refine ⟨22033957152394758814530605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14689304768263172543020403 22033957152394758814530605)
  ·
    refine ⟨8262733932148034555448977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22033957152394758814530605 8262733932148034555448977)
    ·
      refine ⟨6197050449111025916586733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8262733932148034555448977 6197050449111025916586733)
      ·
        refine ⟨2323893918416634718720025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6197050449111025916586733 2323893918416634718720025)
        ·
          refine ⟨1742920438812476039040019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2323893918416634718720025 1742920438812476039040019)
          ·
            refine ⟨2614380658218714058560029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1742920438812476039040019 2614380658218714058560029)
            ·
              refine ⟨980392746832017771960011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2614380658218714058560029 980392746832017771960011)
              ·
                refine ⟨1470589120248026657940017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 980392746832017771960011 1470589120248026657940017)
                ·
                  refine ⟨1102941840186019993455013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1470589120248026657940017 1102941840186019993455013)
                  ·
                    refine ⟨206801595034878748772815, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1102941840186019993455013 206801595034878748772815)
                    ·
                      rfl

theorem cell22_604117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 3, 1, 2, 4].length) (baseStart_604117 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_604117 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_604117 prefixEnd_604117 := by exact prefixLift 604117
  have htrace : WordTrace (prefixWord ++ tailWord_604117) baseStart_604117 baseEnd_604117 := by
    simpa [prefixWord, tailWord_604117, baseEnd_604117] using wordTrace_append hprefix tailTrace_604117
  have hstable : (prefixWord ++ tailWord_604117).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_604117).length < 2 ^ (prefixWord ++ tailWord_604117).sum := by decide
  have hdescent : baseEnd_604117 < baseStart_604117 := by decide
  rcases family_descends (prefixWord ++ tailWord_604117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_604224 : List Nat := [2, 1, 1, 2, 2, 6, 1, 2, 1, 4]
def baseStart_604224 : Nat := 118140960795 + 604224 * 2 ^ 59
def prefixEnd_604224 : Nat := 4983230072969 + 3 ^ 40 * 604224 * 2
def baseEnd_604224 : Nat := 206838223321566136347487

theorem tailTrace_604224 : CollatzResearch.WordTrace tailWord_604224 prefixEnd_604224 206838223321566136347487 := by
  unfold tailWord_604224
  simp only [CollatzResearch.WordTrace]
  refine ⟨11018929881503558044337863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14691906508671410725783817 11018929881503558044337863)
  ·
    refine ⟨16528394822255337066506795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11018929881503558044337863 16528394822255337066506795)
    ·
      refine ⟨24792592233383005599760193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16528394822255337066506795 24792592233383005599760193)
      ·
        refine ⟨18594444175037254199820145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24792592233383005599760193 18594444175037254199820145)
        ·
          refine ⟨13945833131277940649865109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18594444175037254199820145 13945833131277940649865109)
          ·
            refine ⟨653710928028653467962427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 13945833131277940649865109 653710928028653467962427)
            ·
              refine ⟨980566392042980201943641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 653710928028653467962427 980566392042980201943641)
              ·
                refine ⟨735424794032235151457731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 980566392042980201943641 735424794032235151457731)
                ·
                  refine ⟨1103137191048352727186597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 735424794032235151457731 1103137191048352727186597)
                  ·
                    refine ⟨206838223321566136347487, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1103137191048352727186597 206838223321566136347487)
                    ·
                      rfl

theorem cell22_604224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 6, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 6, 1, 2, 1, 4].length) (baseStart_604224 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_604224 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_604224 prefixEnd_604224 := by exact prefixLift 604224
  have htrace : WordTrace (prefixWord ++ tailWord_604224) baseStart_604224 baseEnd_604224 := by
    simpa [prefixWord, tailWord_604224, baseEnd_604224] using wordTrace_append hprefix tailTrace_604224
  have hstable : (prefixWord ++ tailWord_604224).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_604224).length < 2 ^ (prefixWord ++ tailWord_604224).sum := by decide
  have hdescent : baseEnd_604224 < baseStart_604224 := by decide
  rcases family_descends (prefixWord ++ tailWord_604224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_604235 : List Nat := [1, 1, 1, 1, 3, 1, 2, 2, 6, 4]
def baseStart_604235 : Nat := 118140960795 + 604235 * 2 ^ 59
def prefixEnd_604235 : Nat := 4983230072969 + 3 ^ 40 * 604235 * 2
def baseEnd_604235 : Nat := 206841988846365774322453

theorem tailTrace_604235 : CollatzResearch.WordTrace tailWord_604235 prefixEnd_604235 206841988846365774322453 := by
  unfold tailWord_604235
  simp only [CollatzResearch.WordTrace]
  refine ⟨22038260965967264967326159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14692173977311509978217439 22038260965967264967326159)
  ·
    refine ⟨33057391448950897450989239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22038260965967264967326159 33057391448950897450989239)
    ·
      refine ⟨49586087173426346176483859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33057391448950897450989239 49586087173426346176483859)
      ·
        refine ⟨74379130760139519264725789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49586087173426346176483859 74379130760139519264725789)
        ·
          refine ⟨27892174035052319724272171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 74379130760139519264725789 27892174035052319724272171)
          ·
            refine ⟨41838261052578479586408257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27892174035052319724272171 41838261052578479586408257)
            ·
              refine ⟨31378695789433859689806193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41838261052578479586408257 31378695789433859689806193)
              ·
                refine ⟨23534021842075394767354645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31378695789433859689806193 23534021842075394767354645)
                ·
                  refine ⟨1103157273847284129719749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 23534021842075394767354645 1103157273847284129719749)
                  ·
                    refine ⟨206841988846365774322453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1103157273847284129719749 206841988846365774322453)
                    ·
                      rfl

theorem cell22_604235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 2, 6, 4].length) (baseStart_604235 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_604235 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_604235 prefixEnd_604235 := by exact prefixLift 604235
  have htrace : WordTrace (prefixWord ++ tailWord_604235) baseStart_604235 baseEnd_604235 := by
    simpa [prefixWord, tailWord_604235, baseEnd_604235] using wordTrace_append hprefix tailTrace_604235
  have hstable : (prefixWord ++ tailWord_604235).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_604235).length < 2 ^ (prefixWord ++ tailWord_604235).sum := by decide
  have hdescent : baseEnd_604235 < baseStart_604235 := by decide
  rcases family_descends (prefixWord ++ tailWord_604235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_604256 : List Nat := [2, 1, 1, 3, 2, 5, 2, 2, 4]
def baseStart_604256 : Nat := 118140960795 + 604256 * 2 ^ 59
def prefixEnd_604256 : Nat := 4983230072969 + 3 ^ 40 * 604256 * 2
def baseEnd_604256 : Nat := 68949725858509573182463

theorem tailTrace_604256 : CollatzResearch.WordTrace tailWord_604256 prefixEnd_604256 68949725858509573182463 := by
  unfold tailWord_604256
  simp only [CollatzResearch.WordTrace]
  refine ⟨11019513449445592776920311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14692684599260790369227081 11019513449445592776920311)
  ·
    refine ⟨16529270174168389165380467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11019513449445592776920311 16529270174168389165380467)
    ·
      refine ⟨24793905261252583748070701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16529270174168389165380467 24793905261252583748070701)
      ·
        refine ⟨9297714472969718905526513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24793905261252583748070701 9297714472969718905526513)
        ·
          refine ⟨6973285854727289179144885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9297714472969718905526513 6973285854727289179144885)
          ·
            refine ⟨653745548880683360544833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 6973285854727289179144885 653745548880683360544833)
            ·
              refine ⟨490309161660512520408625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 653745548880683360544833 490309161660512520408625)
              ·
                refine ⟨367731871245384390306469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 490309161660512520408625 367731871245384390306469)
                ·
                  refine ⟨68949725858509573182463, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 367731871245384390306469 68949725858509573182463)
                  ·
                    rfl

theorem cell22_604256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 5, 2, 2, 4].length) (baseStart_604256 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_604256 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_604256 prefixEnd_604256 := by exact prefixLift 604256
  have htrace : WordTrace (prefixWord ++ tailWord_604256) baseStart_604256 baseEnd_604256 := by
    simpa [prefixWord, tailWord_604256, baseEnd_604256] using wordTrace_append hprefix tailTrace_604256
  have hstable : (prefixWord ++ tailWord_604256).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_604256).length < 2 ^ (prefixWord ++ tailWord_604256).sum := by decide
  have hdescent : baseEnd_604256 < baseStart_604256 := by decide
  rcases family_descends (prefixWord ++ tailWord_604256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_604280 : List Nat := [2, 1, 2, 1, 1, 1, 3, 1, 4, 6]
def baseStart_604280 : Nat := 118140960795 + 604280 * 2 ^ 59
def prefixEnd_604280 : Nat := 4983230072969 + 3 ^ 40 * 604280 * 2
def baseEnd_604280 : Nat := 206857393266000656947315

theorem tailTrace_604280 : CollatzResearch.WordTrace tailWord_604280 prefixEnd_604280 206857393266000656947315 := by
  unfold tailWord_604280
  simp only [CollatzResearch.WordTrace]
  refine ⟨11019951125402118826357147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14693268167202825101809529 11019951125402118826357147)
  ·
    refine ⟨16529926688103178239535721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11019951125402118826357147 16529926688103178239535721)
    ·
      refine ⟨12397445016077383679651791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16529926688103178239535721 12397445016077383679651791)
      ·
        refine ⟨18596167524116075519477687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12397445016077383679651791 18596167524116075519477687)
        ·
          refine ⟨27894251286174113279216531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18596167524116075519477687 27894251286174113279216531)
          ·
            refine ⟨41841376929261169918824797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27894251286174113279216531 41841376929261169918824797)
            ·
              refine ⟨15690516348472938719559299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 41841376929261169918824797 15690516348472938719559299)
              ·
                refine ⟨23535774522709408079338949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15690516348472938719559299 23535774522709408079338949)
                ·
                  refine ⟨4412957723008014014876053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23535774522709408079338949 4412957723008014014876053)
                  ·
                    refine ⟨206857393266000656947315, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4412957723008014014876053 206857393266000656947315)
                    ·
                      rfl

theorem cell22_604280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 1, 4, 6].length) (baseStart_604280 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_604280 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_604280 prefixEnd_604280 := by exact prefixLift 604280
  have htrace : WordTrace (prefixWord ++ tailWord_604280) baseStart_604280 baseEnd_604280 := by
    simpa [prefixWord, tailWord_604280, baseEnd_604280] using wordTrace_append hprefix tailTrace_604280
  have hstable : (prefixWord ++ tailWord_604280).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_604280).length < 2 ^ (prefixWord ++ tailWord_604280).sum := by decide
  have hdescent : baseEnd_604280 < baseStart_604280 := by decide
  rcases family_descends (prefixWord ++ tailWord_604280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_604316 : List Nat := [2, 2, 3, 2, 1, 1, 1, 6, 1, 3]
def baseStart_604316 : Nat := 118140960795 + 604316 * 2 ^ 59
def prefixEnd_604316 : Nat := 4983230072969 + 3 ^ 40 * 604316 * 2
def baseEnd_604316 : Nat := 206869716801708563047205

theorem tailTrace_604316 : CollatzResearch.WordTrace tailWord_604316 prefixEnd_604316 206869716801708563047205 := by
  unfold tailWord_604316
  simp only [CollatzResearch.WordTrace]
  refine ⟨11020607639336907900512401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14694143519115877200683201 11020607639336907900512401)
  ·
    refine ⟨8265455729502680925384301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11020607639336907900512401 8265455729502680925384301)
    ·
      refine ⟨3099545898563505347019113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8265455729502680925384301 3099545898563505347019113)
      ·
        refine ⟨2324659423922629010264335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3099545898563505347019113 2324659423922629010264335)
        ·
          refine ⟨3486989135883943515396503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2324659423922629010264335 3486989135883943515396503)
          ·
            refine ⟨5230483703825915273094755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3486989135883943515396503 5230483703825915273094755)
            ·
              refine ⟨7845725555738872909642133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5230483703825915273094755 7845725555738872909642133)
              ·
                refine ⟨367768385425259667639475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 7845725555738872909642133 367768385425259667639475)
                ·
                  refine ⟨551652578137889501459213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 367768385425259667639475 551652578137889501459213)
                  ·
                    refine ⟨206869716801708563047205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 551652578137889501459213 206869716801708563047205)
                    ·
                      rfl

theorem cell22_604316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 1, 6, 1, 3].length) (baseStart_604316 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_604316 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_604316 prefixEnd_604316 := by exact prefixLift 604316
  have htrace : WordTrace (prefixWord ++ tailWord_604316) baseStart_604316 baseEnd_604316 := by
    simpa [prefixWord, tailWord_604316, baseEnd_604316] using wordTrace_append hprefix tailTrace_604316
  have hstable : (prefixWord ++ tailWord_604316).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_604316).length < 2 ^ (prefixWord ++ tailWord_604316).sum := by decide
  have hdescent : baseEnd_604316 < baseStart_604316 := by decide
  rcases family_descends (prefixWord ++ tailWord_604316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_604350 : List Nat := [4, 2, 1, 1, 4, 2, 1, 3, 1, 3]
def baseStart_604350 : Nat := 118140960795 + 604350 * 2 ^ 59
def prefixEnd_604350 : Nat := 4983230072969 + 3 ^ 40 * 604350 * 2
def baseEnd_604350 : Nat := 206881355696543807697101

theorem tailTrace_604350 : CollatzResearch.WordTrace tailWord_604350 prefixEnd_604350 206881355696543807697101 := by
  unfold tailWord_604350
  simp only [CollatzResearch.WordTrace]
  refine ⟨2755306920068829950970313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14694970240367093071841669 2755306920068829950970313)
  ·
    refine ⟨2066480190051622463227735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2755306920068829950970313 2066480190051622463227735)
    ·
      refine ⟨3099720285077433694841603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2066480190051622463227735 3099720285077433694841603)
      ·
        refine ⟨4649580427616150542262405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3099720285077433694841603 4649580427616150542262405)
        ·
          refine ⟨871796330178028226674201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4649580427616150542262405 871796330178028226674201)
          ·
            refine ⟨653847247633521170005651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 871796330178028226674201 653847247633521170005651)
            ·
              refine ⟨980770871450281755008477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 653847247633521170005651 980770871450281755008477)
              ·
                refine ⟨367789076793855658128179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 980770871450281755008477 367789076793855658128179)
                ·
                  refine ⟨551683615190783487192269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 367789076793855658128179 551683615190783487192269)
                  ·
                    refine ⟨206881355696543807697101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 551683615190783487192269 206881355696543807697101)
                    ·
                      rfl

theorem cell22_604350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 2, 1, 3, 1, 3].length) (baseStart_604350 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_604350 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_604350 prefixEnd_604350 := by exact prefixLift 604350
  have htrace : WordTrace (prefixWord ++ tailWord_604350) baseStart_604350 baseEnd_604350 := by
    simpa [prefixWord, tailWord_604350, baseEnd_604350] using wordTrace_append hprefix tailTrace_604350
  have hstable : (prefixWord ++ tailWord_604350).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_604350).length < 2 ^ (prefixWord ++ tailWord_604350).sum := by decide
  have hdescent : baseEnd_604350 < baseStart_604350 := by decide
  rcases family_descends (prefixWord ++ tailWord_604350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_604380 : List Nat := [2, 2, 5, 2, 1, 2, 2, 1, 5]
def baseStart_604380 : Nat := 118140960795 + 604380 * 2 ^ 59
def prefixEnd_604380 : Nat := 4983230072969 + 3 ^ 40 * 604380 * 2
def baseEnd_604380 : Nat := 68963875103211243149003

theorem tailTrace_604380 : CollatzResearch.WordTrace tailWord_604380 prefixEnd_604380 68963875103211243149003 := by
  unfold tailWord_604380
  simp only [CollatzResearch.WordTrace]
  refine ⟨11021774775220977365677297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14695699700294636487569729 11021774775220977365677297)
  ·
    refine ⟨8266331081415733024257973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11021774775220977365677297 8266331081415733024257973)
    ·
      refine ⟨774968538882724971024185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 8266331081415733024257973 774968538882724971024185)
      ·
        refine ⟨581226404162043728268139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 774968538882724971024185 581226404162043728268139)
        ·
          refine ⟨871839606243065592402209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 581226404162043728268139 871839606243065592402209)
          ·
            refine ⟨653879704682299194301657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 871839606243065592402209 653879704682299194301657)
            ·
              refine ⟨490409778511724395726243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 653879704682299194301657 490409778511724395726243)
              ·
                refine ⟨735614667767586593589365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 490409778511724395726243 735614667767586593589365)
                ·
                  refine ⟨68963875103211243149003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 735614667767586593589365 68963875103211243149003)
                  ·
                    rfl

theorem cell22_604380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 2, 2, 1, 5].length) (baseStart_604380 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_604380 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_604380 prefixEnd_604380 := by exact prefixLift 604380
  have htrace : WordTrace (prefixWord ++ tailWord_604380) baseStart_604380 baseEnd_604380 := by
    simpa [prefixWord, tailWord_604380, baseEnd_604380] using wordTrace_append hprefix tailTrace_604380
  have hstable : (prefixWord ++ tailWord_604380).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_604380).length < 2 ^ (prefixWord ++ tailWord_604380).sum := by decide
  have hdescent : baseEnd_604380 < baseStart_604380 := by decide
  rcases family_descends (prefixWord ++ tailWord_604380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_604481 : List Nat := [1, 2, 5, 2, 2, 1, 1, 1, 7]
def baseStart_604481 : Nat := 118140960795 + 604481 * 2 ^ 59
def prefixEnd_604481 : Nat := 4983230072969 + 3 ^ 40 * 604481 * 2
def baseEnd_604481 : Nat := 68975399891234377557233

theorem tailTrace_604481 : CollatzResearch.WordTrace tailWord_604481 prefixEnd_604481 68975399891234377557233 := by
  unfold tailWord_604481
  simp only [CollatzResearch.WordTrace]
  refine ⟨22047233323076048980781297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14698155548717365987187531 22047233323076048980781297)
  ·
    refine ⟨16535424992307036735585973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22047233323076048980781297 16535424992307036735585973)
    ·
      refine ⟨1550196093028784693961185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 16535424992307036735585973 1550196093028784693961185)
      ·
        refine ⟨1162647069771588520470889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1550196093028784693961185 1162647069771588520470889)
        ·
          refine ⟨871985302328691390353167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1162647069771588520470889 871985302328691390353167)
          ·
            refine ⟨1307977953493037085529751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 871985302328691390353167 1307977953493037085529751)
            ·
              refine ⟨1961966930239555628294627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1307977953493037085529751 1961966930239555628294627)
              ·
                refine ⟨2942950395359333442441941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1961966930239555628294627 2942950395359333442441941)
                ·
                  refine ⟨68975399891234377557233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2942950395359333442441941 68975399891234377557233)
                  ·
                    rfl

theorem cell22_604481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 1, 1, 1, 7].length) (baseStart_604481 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_604481 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_604481 prefixEnd_604481 := by exact prefixLift 604481
  have htrace : WordTrace (prefixWord ++ tailWord_604481) baseStart_604481 baseEnd_604481 := by
    simpa [prefixWord, tailWord_604481, baseEnd_604481] using wordTrace_append hprefix tailTrace_604481
  have hstable : (prefixWord ++ tailWord_604481).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_604481).length < 2 ^ (prefixWord ++ tailWord_604481).sum := by decide
  have hdescent : baseEnd_604481 < baseStart_604481 := by decide
  rcases family_descends (prefixWord ++ tailWord_604481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_604494 : List Nat := [4, 1, 1, 1, 1, 1, 2, 4, 3, 4]
def baseStart_604494 : Nat := 118140960795 + 604494 * 2 ^ 59
def prefixEnd_604494 : Nat := 4983230072969 + 3 ^ 40 * 604494 * 2
def baseEnd_604494 : Nat := 206930649839375432096659

theorem tailTrace_604494 : CollatzResearch.WordTrace tailWord_604494 prefixEnd_604494 206930649839375432096659 := by
  unfold tailWord_604494
  simp only [CollatzResearch.WordTrace]
  refine ⟨2755963434003619025125567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14698471648019301467336357 2755963434003619025125567)
  ·
    refine ⟨4133945151005428537688351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2755963434003619025125567 4133945151005428537688351)
    ·
      refine ⟨6200917726508142806532527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4133945151005428537688351 6200917726508142806532527)
      ·
        refine ⟨9301376589762214209798791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6200917726508142806532527 9301376589762214209798791)
        ·
          refine ⟨13952064884643321314698187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9301376589762214209798791 13952064884643321314698187)
          ·
            refine ⟨20928097326964981972047281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13952064884643321314698187 20928097326964981972047281)
            ·
              refine ⟨15696072995223736479035461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20928097326964981972047281 15696072995223736479035461)
              ·
                refine ⟨2943013686604450589819149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15696072995223736479035461 2943013686604450589819149)
                ·
                  refine ⟨1103630132476668971182181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2943013686604450589819149 1103630132476668971182181)
                  ·
                    refine ⟨206930649839375432096659, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1103630132476668971182181 206930649839375432096659)
                    ·
                      rfl

theorem cell22_604494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 4, 3, 4].length) (baseStart_604494 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_604494 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_604494 prefixEnd_604494 := by exact prefixLift 604494
  have htrace : WordTrace (prefixWord ++ tailWord_604494) baseStart_604494 baseEnd_604494 := by
    simpa [prefixWord, tailWord_604494, baseEnd_604494] using wordTrace_append hprefix tailTrace_604494
  have hstable : (prefixWord ++ tailWord_604494).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_604494).length < 2 ^ (prefixWord ++ tailWord_604494).sum := by decide
  have hdescent : baseEnd_604494 < baseStart_604494 := by decide
  rcases family_descends (prefixWord ++ tailWord_604494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_604539 : List Nat := [1, 1, 1, 1, 1, 7, 1, 1, 4, 4]
def baseStart_604539 : Nat := 118140960795 + 604539 * 2 ^ 59
def prefixEnd_604539 : Nat := 4983230072969 + 3 ^ 40 * 604539 * 2
def baseEnd_604539 : Nat := 206946054259010314721521

theorem tailTrace_604539 : CollatzResearch.WordTrace tailWord_604539 prefixEnd_604539 206946054259010314721521 := by
  unfold tailWord_604539
  simp only [CollatzResearch.WordTrace]
  refine ⟨22049348756865924886392671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14699565837910616590928447 22049348756865924886392671)
  ·
    refine ⟨33074023135298887329589007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22049348756865924886392671 33074023135298887329589007)
    ·
      refine ⟨49611034702948330994383511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33074023135298887329589007 49611034702948330994383511)
      ·
        refine ⟨74416552054422496491575267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49611034702948330994383511 74416552054422496491575267)
        ·
          refine ⟨111624828081633744737362901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74416552054422496491575267 111624828081633744737362901)
          ·
            refine ⟨2616206908163290892281943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 111624828081633744737362901 2616206908163290892281943)
            ·
              refine ⟨3924310362244936338422915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2616206908163290892281943 3924310362244936338422915)
              ·
                refine ⟨5886465543367404507634373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3924310362244936338422915 5886465543367404507634373)
                ·
                  refine ⟨1103712289381388345181445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5886465543367404507634373 1103712289381388345181445)
                  ·
                    refine ⟨206946054259010314721521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1103712289381388345181445 206946054259010314721521)
                    ·
                      rfl

theorem cell22_604539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 1, 1, 4, 4].length) (baseStart_604539 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_604539 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_604539 prefixEnd_604539 := by exact prefixLift 604539
  have htrace : WordTrace (prefixWord ++ tailWord_604539) baseStart_604539 baseEnd_604539 := by
    simpa [prefixWord, tailWord_604539, baseEnd_604539] using wordTrace_append hprefix tailTrace_604539
  have hstable : (prefixWord ++ tailWord_604539).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_604539).length < 2 ^ (prefixWord ++ tailWord_604539).sum := by decide
  have hdescent : baseEnd_604539 < baseStart_604539 := by decide
  rcases family_descends (prefixWord ++ tailWord_604539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_604541 : List Nat := [1, 4, 1, 1, 2, 3, 2, 1, 4, 3]
def baseStart_604541 : Nat := 118140960795 + 604541 * 2 ^ 59
def prefixEnd_604541 : Nat := 4983230072969 + 3 ^ 40 * 604541 * 2
def baseEnd_604541 : Nat := 206946738899882976171515

theorem tailTrace_604541 : CollatzResearch.WordTrace tailWord_604541 prefixEnd_604541 206946738899882976171515 := by
  unfold tailWord_604541
  simp only [CollatzResearch.WordTrace]
  refine ⟨22049421702858679227965477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14699614468572452818643651 22049421702858679227965477)
  ·
    refine ⟨4134266569286002355243527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 22049421702858679227965477 4134266569286002355243527)
    ·
      refine ⟨6201399853929003532865291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4134266569286002355243527 6201399853929003532865291)
      ·
        refine ⟨9302099780893505299297937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6201399853929003532865291 9302099780893505299297937)
        ·
          refine ⟨6976574835670128974473453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9302099780893505299297937 6976574835670128974473453)
          ·
            refine ⟨2616215563376298365427545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6976574835670128974473453 2616215563376298365427545)
            ·
              refine ⟨1962161672532223774070659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2616215563376298365427545 1962161672532223774070659)
              ·
                refine ⟨2943242508798335661105989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1962161672532223774070659 2943242508798335661105989)
                ·
                  refine ⟨551857970399687936457373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2943242508798335661105989 551857970399687936457373)
                  ·
                    refine ⟨206946738899882976171515, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 551857970399687936457373 206946738899882976171515)
                    ·
                      rfl

theorem cell22_604541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 2, 1, 4, 3].length) (baseStart_604541 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_604541 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_604541 prefixEnd_604541 := by exact prefixLift 604541
  have htrace : WordTrace (prefixWord ++ tailWord_604541) baseStart_604541 baseEnd_604541 := by
    simpa [prefixWord, tailWord_604541, baseEnd_604541] using wordTrace_append hprefix tailTrace_604541
  have hstable : (prefixWord ++ tailWord_604541).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_604541).length < 2 ^ (prefixWord ++ tailWord_604541).sum := by decide
  have hdescent : baseEnd_604541 < baseStart_604541 := by decide
  rcases family_descends (prefixWord ++ tailWord_604541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_604573 : List Nat := [1, 4, 2, 1, 4, 1, 2, 1, 2, 4]
def baseStart_604573 : Nat := 118140960795 + 604573 * 2 ^ 59
def prefixEnd_604573 : Nat := 4983230072969 + 3 ^ 40 * 604573 * 2
def baseEnd_604573 : Nat := 206957693153845559371417

theorem tailTrace_604573 : CollatzResearch.WordTrace tailWord_604573 prefixEnd_604573 206957693153845559371417 := by
  unfold tailWord_604573
  simp only [CollatzResearch.WordTrace]
  refine ⟨22050588838742748693130373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14700392559161832462086915 22050588838742748693130373)
  ·
    refine ⟨4134485407264265379961945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 22050588838742748693130373 4134485407264265379961945)
    ·
      refine ⟨3100864055448199034971459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4134485407264265379961945 3100864055448199034971459)
      ·
        refine ⟨4651296083172298552457189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3100864055448199034971459 4651296083172298552457189)
        ·
          refine ⟨872118015594805978585723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4651296083172298552457189 872118015594805978585723)
          ·
            refine ⟨1308177023392208967878585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 872118015594805978585723 1308177023392208967878585)
            ·
              refine ⟨981132767544156725908939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1308177023392208967878585 981132767544156725908939)
              ·
                refine ⟨1471699151316235088863409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 981132767544156725908939 1471699151316235088863409)
                ·
                  refine ⟨1103774363487176316647557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1471699151316235088863409 1103774363487176316647557)
                  ·
                    refine ⟨206957693153845559371417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1103774363487176316647557 206957693153845559371417)
                    ·
                      rfl

theorem cell22_604573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 1, 2, 1, 2, 4].length) (baseStart_604573 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_604573 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_604573 prefixEnd_604573 := by exact prefixLift 604573
  have htrace : WordTrace (prefixWord ++ tailWord_604573) baseStart_604573 baseEnd_604573 := by
    simpa [prefixWord, tailWord_604573, baseEnd_604573] using wordTrace_append hprefix tailTrace_604573
  have hstable : (prefixWord ++ tailWord_604573).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_604573).length < 2 ^ (prefixWord ++ tailWord_604573).sum := by decide
  have hdescent : baseEnd_604573 < baseStart_604573 := by decide
  rcases family_descends (prefixWord ++ tailWord_604573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_604616 : List Nat := [2, 1, 3, 1, 3, 2, 2, 3, 5]
def baseStart_604616 : Nat := 118140960795 + 604616 * 2 ^ 59
def prefixEnd_604616 : Nat := 4983230072969 + 3 ^ 40 * 604616 * 2
def baseEnd_604616 : Nat := 68990804310869260182095

theorem tailTrace_604616 : CollatzResearch.WordTrace tailWord_604616 prefixEnd_604616 68990804310869260182095 := by
  unfold tailWord_604616
  simp only [CollatzResearch.WordTrace]
  refine ⟨11026078588793483518472851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14701438118391311357963801 11026078588793483518472851)
  ·
    refine ⟨16539117883190225277709277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11026078588793483518472851 16539117883190225277709277)
    ·
      refine ⟨6202169206196334479140979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16539117883190225277709277 6202169206196334479140979)
      ·
        refine ⟨9303253809294501718711469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6202169206196334479140979 9303253809294501718711469)
        ·
          refine ⟨3488720178485438144516801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9303253809294501718711469 3488720178485438144516801)
          ·
            refine ⟨2616540133864078608387601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3488720178485438144516801 2616540133864078608387601)
            ·
              refine ⟨1962405100398058956290701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2616540133864078608387601 1962405100398058956290701)
              ·
                refine ⟨735901912649272108609013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1962405100398058956290701 735901912649272108609013)
                ·
                  refine ⟨68990804310869260182095, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 735901912649272108609013 68990804310869260182095)
                  ·
                    rfl

theorem cell22_604616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 2, 3, 5].length) (baseStart_604616 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_604616 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_604616 prefixEnd_604616 := by exact prefixLift 604616
  have htrace : WordTrace (prefixWord ++ tailWord_604616) baseStart_604616 baseEnd_604616 := by
    simpa [prefixWord, tailWord_604616, baseEnd_604616] using wordTrace_append hprefix tailTrace_604616
  have hstable : (prefixWord ++ tailWord_604616).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_604616).length < 2 ^ (prefixWord ++ tailWord_604616).sum := by decide
  have hdescent : baseEnd_604616 < baseStart_604616 := by decide
  rcases family_descends (prefixWord ++ tailWord_604616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_604691 : List Nat := [1, 1, 1, 2, 1, 5, 2, 3, 2, 4]
def baseStart_604691 : Nat := 118140960795 + 604691 * 2 ^ 59
def prefixEnd_604691 : Nat := 4983230072969 + 3 ^ 40 * 604691 * 2
def baseEnd_604691 : Nat := 206998086965332584921055

theorem tailTrace_604691 : CollatzResearch.WordTrace tailWord_604691 prefixEnd_604691 206998086965332584921055 := by
  unfold tailWord_604691
  simp only [CollatzResearch.WordTrace]
  refine ⟨22054892652315254845925927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14703261768210169897283951 22054892652315254845925927)
  ·
    refine ⟨33082338978472882268888891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22054892652315254845925927 33082338978472882268888891)
    ·
      refine ⟨49623508467709323403333337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33082338978472882268888891 49623508467709323403333337)
      ·
        refine ⟨37217631350781992552500003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49623508467709323403333337 37217631350781992552500003)
        ·
          refine ⟨55826447026172988828750005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37217631350781992552500003 55826447026172988828750005)
          ·
            refine ⟨5233729408703717702695313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 55826447026172988828750005 5233729408703717702695313)
            ·
              refine ⟨3925297056527788277021485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5233729408703717702695313 3925297056527788277021485)
              ·
                refine ⟨1471986396197920603883057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3925297056527788277021485 1471986396197920603883057)
                ·
                  refine ⟨1103989797148440452912293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1471986396197920603883057 1103989797148440452912293)
                  ·
                    refine ⟨206998086965332584921055, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1103989797148440452912293 206998086965332584921055)
                    ·
                      rfl

theorem cell22_604691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 2, 3, 2, 4].length) (baseStart_604691 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_604691 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_604691 prefixEnd_604691 := by exact prefixLift 604691
  have htrace : WordTrace (prefixWord ++ tailWord_604691) baseStart_604691 baseEnd_604691 := by
    simpa [prefixWord, tailWord_604691, baseEnd_604691] using wordTrace_append hprefix tailTrace_604691
  have hstable : (prefixWord ++ tailWord_604691).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_604691).length < 2 ^ (prefixWord ++ tailWord_604691).sum := by decide
  have hdescent : baseEnd_604691 < baseStart_604691 := by decide
  rcases family_descends (prefixWord ++ tailWord_604691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_604712 : List Nat := [2, 1, 5, 2, 1, 2, 3, 2, 4]
def baseStart_604712 : Nat := 118140960795 + 604712 * 2 ^ 59
def prefixEnd_604712 : Nat := 4983230072969 + 3 ^ 40 * 604712 * 2
def baseEnd_604712 : Nat := 69001758564831843381997

theorem tailTrace_604712 : CollatzResearch.WordTrace tailWord_604712 prefixEnd_604712 69001758564831843381997 := by
  unfold tailWord_604712
  simp only [CollatzResearch.WordTrace]
  refine ⟨11027829292619587716220195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14703772390159450288293593 11027829292619587716220195)
  ·
    refine ⟨16541743938929381574330293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11027829292619587716220195 16541743938929381574330293)
    ·
      refine ⟨1550788494274629522593465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 16541743938929381574330293 1550788494274629522593465)
      ·
        refine ⟨1163091370705972141945099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1550788494274629522593465 1163091370705972141945099)
        ·
          refine ⟨1744637056058958212917649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1163091370705972141945099 1744637056058958212917649)
          ·
            refine ⟨1308477792044218659688237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1744637056058958212917649 1308477792044218659688237)
            ·
              refine ⟨490679172016581997383089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1308477792044218659688237 490679172016581997383089)
              ·
                refine ⟨368009379012436498037317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 490679172016581997383089 368009379012436498037317)
                ·
                  refine ⟨69001758564831843381997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 368009379012436498037317 69001758564831843381997)
                  ·
                    rfl

theorem cell22_604712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 2, 3, 2, 4].length) (baseStart_604712 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_604712 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_604712 prefixEnd_604712 := by exact prefixLift 604712
  have htrace : WordTrace (prefixWord ++ tailWord_604712) baseStart_604712 baseEnd_604712 := by
    simpa [prefixWord, tailWord_604712, baseEnd_604712] using wordTrace_append hprefix tailTrace_604712
  have hstable : (prefixWord ++ tailWord_604712).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_604712).length < 2 ^ (prefixWord ++ tailWord_604712).sum := by decide
  have hdescent : baseEnd_604712 < baseStart_604712 := by decide
  rcases family_descends (prefixWord ++ tailWord_604712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_604742 : List Nat := [6, 1, 1, 1, 2, 2, 2, 1, 2, 4]
def baseStart_604742 : Nat := 118140960795 + 604742 * 2 ^ 59
def prefixEnd_604742 : Nat := 4983230072969 + 3 ^ 40 * 604742 * 2
def baseEnd_604742 : Nat := 207015545307585451895899

theorem tailTrace_604742 : CollatzResearch.WordTrace tailWord_604742 prefixEnd_604742 207015545307585451895899 := by
  unfold tailWord_604742
  simp only [CollatzResearch.WordTrace]
  refine ⟨689273524222827829876015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 14704501850086993704021653 689273524222827829876015)
  ·
    refine ⟨1033910286334241744814023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 689273524222827829876015 1033910286334241744814023)
    ·
      refine ⟨1550865429501362617221035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1033910286334241744814023 1550865429501362617221035)
      ·
        refine ⟨2326298144252043925831553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1550865429501362617221035 2326298144252043925831553)
        ·
          refine ⟨1744723608189032944373665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2326298144252043925831553 1744723608189032944373665)
          ·
            refine ⟨1308542706141774708280249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1744723608189032944373665 1308542706141774708280249)
            ·
              refine ⟨981407029606331031210187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1308542706141774708280249 981407029606331031210187)
              ·
                refine ⟨1472110544409496546815281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 981407029606331031210187 1472110544409496546815281)
                ·
                  refine ⟨1104082908307122410111461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1472110544409496546815281 1104082908307122410111461)
                  ·
                    refine ⟨207015545307585451895899, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1104082908307122410111461 207015545307585451895899)
                    ·
                      rfl

theorem cell22_604742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 2, 2, 1, 2, 4].length) (baseStart_604742 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_604742 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_604742 prefixEnd_604742 := by exact prefixLift 604742
  have htrace : WordTrace (prefixWord ++ tailWord_604742) baseStart_604742 baseEnd_604742 := by
    simpa [prefixWord, tailWord_604742, baseEnd_604742] using wordTrace_append hprefix tailTrace_604742
  have hstable : (prefixWord ++ tailWord_604742).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_604742).length < 2 ^ (prefixWord ++ tailWord_604742).sum := by decide
  have hdescent : baseEnd_604742 < baseStart_604742 := by decide
  rcases family_descends (prefixWord ++ tailWord_604742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_604796 : List Nat := [2, 2, 2, 1, 1, 2, 3, 1, 8]
def baseStart_604796 : Nat := 118140960795 + 604796 * 2 ^ 59
def prefixEnd_604796 : Nat := 4983230072969 + 3 ^ 40 * 604796 * 2
def baseEnd_604796 : Nat := 69011343537049103681911

theorem tailTrace_604796 : CollatzResearch.WordTrace tailWord_604796 prefixEnd_604796 69011343537049103681911 := by
  unfold tailWord_604796
  simp only [CollatzResearch.WordTrace]
  refine ⟨11029361158467428889249121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14705814877956571852332161 11029361158467428889249121)
  ·
    refine ⟨8272020868850571666936841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11029361158467428889249121 8272020868850571666936841)
    ·
      refine ⟨6204015651637928750202631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8272020868850571666936841 6204015651637928750202631)
      ·
        refine ⟨9306023477456893125303947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6204015651637928750202631 9306023477456893125303947)
        ·
          refine ⟨13959035216185339687955921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9306023477456893125303947 13959035216185339687955921)
          ·
            refine ⟨10469276412139004765966941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13959035216185339687955921 10469276412139004765966941)
            ·
              refine ⟨3925978654552126787237603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10469276412139004765966941 3925978654552126787237603)
              ·
                refine ⟨5888967981828190180856405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3925978654552126787237603 5888967981828190180856405)
                ·
                  refine ⟨69011343537049103681911, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 5888967981828190180856405 69011343537049103681911)
                  ·
                    rfl

theorem cell22_604796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 3, 1, 8].length) (baseStart_604796 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_604796 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_604796 prefixEnd_604796 := by exact prefixLift 604796
  have htrace : WordTrace (prefixWord ++ tailWord_604796) baseStart_604796 baseEnd_604796 := by
    simpa [prefixWord, tailWord_604796, baseEnd_604796] using wordTrace_append hprefix tailTrace_604796
  have hstable : (prefixWord ++ tailWord_604796).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_604796).length < 2 ^ (prefixWord ++ tailWord_604796).sum := by decide
  have hdescent : baseEnd_604796 < baseStart_604796 := by decide
  rcases family_descends (prefixWord ++ tailWord_604796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_604811 : List Nat := [1, 1, 1, 1, 4, 1, 2, 3, 3, 5]
def baseStart_604811 : Nat := 118140960795 + 604811 * 2 ^ 59
def prefixEnd_604811 : Nat := 4983230072969 + 3 ^ 40 * 604811 * 2
def baseEnd_604811 : Nat := 207039165417692271920687

theorem tailTrace_604811 : CollatzResearch.WordTrace tailWord_604811 prefixEnd_604811 207039165417692271920687 := by
  unfold tailWord_604811
  simp only [CollatzResearch.WordTrace]
  refine ⟨22059269411880515340294287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14706179607920343560196191 22059269411880515340294287)
  ·
    refine ⟨33088904117820773010441431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22059269411880515340294287 33088904117820773010441431)
    ·
      refine ⟨49633356176731159515662147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33088904117820773010441431 49633356176731159515662147)
      ·
        refine ⟨74450034265096739273493221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49633356176731159515662147 74450034265096739273493221)
        ·
          refine ⟨13959381424705638613779979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 74450034265096739273493221 13959381424705638613779979)
          ·
            refine ⟨20939072137058457920669969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13959381424705638613779979 20939072137058457920669969)
            ·
              refine ⟨15704304102793843440502477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20939072137058457920669969 15704304102793843440502477)
              ·
                refine ⟨5889114038547691290188429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15704304102793843440502477 5889114038547691290188429)
                ·
                  refine ⟨2208417764455384233820661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5889114038547691290188429 2208417764455384233820661)
                  ·
                    refine ⟨207039165417692271920687, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2208417764455384233820661 207039165417692271920687)
                    ·
                      rfl

theorem cell22_604811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 3, 3, 5].length) (baseStart_604811 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_604811 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_604811 prefixEnd_604811 := by exact prefixLift 604811
  have htrace : WordTrace (prefixWord ++ tailWord_604811) baseStart_604811 baseEnd_604811 := by
    simpa [prefixWord, tailWord_604811, baseEnd_604811] using wordTrace_append hprefix tailTrace_604811
  have hstable : (prefixWord ++ tailWord_604811).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_604811).length < 2 ^ (prefixWord ++ tailWord_604811).sum := by decide
  have hdescent : baseEnd_604811 < baseStart_604811 := by decide
  rcases family_descends (prefixWord ++ tailWord_604811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_604830 : List Nat := [4, 3, 1, 1, 1, 1, 4, 1, 6]
def baseStart_604830 : Nat := 118140960795 + 604830 * 2 ^ 59
def prefixEnd_604830 : Nat := 4983230072969 + 3 ^ 40 * 604830 * 2
def baseEnd_604830 : Nat := 69015223168660851898543

theorem tailTrace_604830 : CollatzResearch.WordTrace tailWord_604830 prefixEnd_604830 69015223168660851898543 := by
  unfold tailWord_604830
  simp only [CollatzResearch.WordTrace]
  refine ⟨2757495299851460198154493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14706641599207787723490629 2757495299851460198154493)
  ·
    refine ⟨1034060737444297574307935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2757495299851460198154493 1034060737444297574307935)
    ·
      refine ⟨1551091106166446361461903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1034060737444297574307935 1551091106166446361461903)
      ·
        refine ⟨2326636659249669542192855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1551091106166446361461903 2326636659249669542192855)
        ·
          refine ⟨3489954988874504313289283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2326636659249669542192855 3489954988874504313289283)
          ·
            refine ⟨5234932483311756469933925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3489954988874504313289283 5234932483311756469933925)
            ·
              refine ⟨981549840620954338112611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5234932483311756469933925 981549840620954338112611)
              ·
                refine ⟨1472324760931431507168917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 981549840620954338112611 1472324760931431507168917)
                ·
                  refine ⟨69015223168660851898543, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1472324760931431507168917 69015223168660851898543)
                  ·
                    rfl

theorem cell22_604830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 4, 1, 6].length) (baseStart_604830 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_604830 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_604830 prefixEnd_604830 := by exact prefixLift 604830
  have htrace : WordTrace (prefixWord ++ tailWord_604830) baseStart_604830 baseEnd_604830 := by
    simpa [prefixWord, tailWord_604830, baseEnd_604830] using wordTrace_append hprefix tailTrace_604830
  have hstable : (prefixWord ++ tailWord_604830).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_604830).length < 2 ^ (prefixWord ++ tailWord_604830).sum := by decide
  have hdescent : baseEnd_604830 < baseStart_604830 := by decide
  rcases family_descends (prefixWord ++ tailWord_604830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_604845 : List Nat := [1, 5, 2, 1, 1, 2, 3, 1, 1, 5]
def baseStart_604845 : Nat := 118140960795 + 604845 * 2 ^ 59
def prefixEnd_604845 : Nat := 4983230072969 + 3 ^ 40 * 604845 * 2
def baseEnd_604845 : Nat := 207050804312527516570583

theorem tailTrace_604845 : CollatzResearch.WordTrace tailWord_604845 prefixEnd_604845 207050804312527516570583 := by
  unfold tailWord_604845
  simp only [CollatzResearch.WordTrace]
  refine ⟨22060509493757339147031989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14707006329171559431354659 22060509493757339147031989)
  ·
    refine ⟨2068172765039750545034249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 22060509493757339147031989 2068172765039750545034249)
    ·
      refine ⟨1551129573779812908775687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2068172765039750545034249 1551129573779812908775687)
      ·
        refine ⟨2326694360669719363163531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1551129573779812908775687 2326694360669719363163531)
        ·
          refine ⟨3490041541004579044745297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2326694360669719363163531 3490041541004579044745297)
          ·
            refine ⟨2617531155753434283558973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3490041541004579044745297 2617531155753434283558973)
            ·
              refine ⟨981574183407537856334615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2617531155753434283558973 981574183407537856334615)
              ·
                refine ⟨1472361275111306784501923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 981574183407537856334615 1472361275111306784501923)
                ·
                  refine ⟨2208541912666960176752885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1472361275111306784501923 2208541912666960176752885)
                  ·
                    refine ⟨207050804312527516570583, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2208541912666960176752885 207050804312527516570583)
                    ·
                      rfl

theorem cell22_604845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 3, 1, 1, 5].length) (baseStart_604845 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_604845 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_604845 prefixEnd_604845 := by exact prefixLift 604845
  have htrace : WordTrace (prefixWord ++ tailWord_604845) baseStart_604845 baseEnd_604845 := by
    simpa [prefixWord, tailWord_604845, baseEnd_604845] using wordTrace_append hprefix tailTrace_604845
  have hstable : (prefixWord ++ tailWord_604845).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_604845).length < 2 ^ (prefixWord ++ tailWord_604845).sum := by decide
  have hdescent : baseEnd_604845 < baseStart_604845 := by decide
  rcases family_descends (prefixWord ++ tailWord_604845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_605025 : List Nat := [1, 2, 3, 1, 1, 1, 2, 3, 5, 3]
def baseStart_605025 : Nat := 118140960795 + 605025 * 2 ^ 59
def prefixEnd_605025 : Nat := 4983230072969 + 3 ^ 40 * 605025 * 2
def baseEnd_605025 : Nat := 207112421991067047070031

theorem tailTrace_605025 : CollatzResearch.WordTrace tailWord_605025 prefixEnd_605025 207112421991067047070031 := by
  unfold tailWord_605025
  simp only [CollatzResearch.WordTrace]
  refine ⟨22067074633105229888584529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14711383088736819925723019 22067074633105229888584529)
  ·
    refine ⟨16550305974828922416438397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22067074633105229888584529 16550305974828922416438397)
    ·
      refine ⟨6206364740560845906164399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16550305974828922416438397 6206364740560845906164399)
      ·
        refine ⟨9309547110841268859246599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6206364740560845906164399 9309547110841268859246599)
        ·
          refine ⟨13964320666261903288869899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9309547110841268859246599 13964320666261903288869899)
          ·
            refine ⟨20946480999392854933304849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13964320666261903288869899 20946480999392854933304849)
            ·
              refine ⟨15709860749544641199978637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20946480999392854933304849 15709860749544641199978637)
              ·
                refine ⟨5891197781079240449991989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15709860749544641199978637 5891197781079240449991989)
                ·
                  refine ⟨552299791976178792186749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5891197781079240449991989 552299791976178792186749)
                  ·
                    refine ⟨207112421991067047070031, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 552299791976178792186749 207112421991067047070031)
                    ·
                      rfl

theorem cell22_605025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 3, 5, 3].length) (baseStart_605025 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_605025 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_605025 prefixEnd_605025 := by exact prefixLift 605025
  have htrace : WordTrace (prefixWord ++ tailWord_605025) baseStart_605025 baseEnd_605025 := by
    simpa [prefixWord, tailWord_605025, baseEnd_605025] using wordTrace_append hprefix tailTrace_605025
  have hstable : (prefixWord ++ tailWord_605025).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_605025).length < 2 ^ (prefixWord ++ tailWord_605025).sum := by decide
  have hdescent : baseEnd_605025 < baseStart_605025 := by decide
  rcases family_descends (prefixWord ++ tailWord_605025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_605027 : List Nat := [1, 1, 1, 5, 3, 3, 2, 6]
def baseStart_605027 : Nat := 118140960795 + 605027 * 2 ^ 59
def prefixEnd_605027 : Nat := 4983230072969 + 3 ^ 40 * 605027 * 2
def baseEnd_605027 : Nat := 23012567403548856502225

theorem tailTrace_605027 : CollatzResearch.WordTrace tailWord_605027 prefixEnd_605027 23012567403548856502225 := by
  unfold tailWord_605027
  simp only [CollatzResearch.WordTrace]
  refine ⟨22067147579097984230157335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14711431719398656153438223 22067147579097984230157335)
  ·
    refine ⟨33100721368646976345236003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22067147579097984230157335 33100721368646976345236003)
    ·
      refine ⟨49651082052970464517854005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33100721368646976345236003 49651082052970464517854005)
      ·
        refine ⟨4654788942465981048548813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 49651082052970464517854005 4654788942465981048548813)
        ·
          refine ⟨1745545853424742893205805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4654788942465981048548813 1745545853424742893205805)
          ·
            refine ⟨654579695034278584952177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1745545853424742893205805 654579695034278584952177)
            ·
              refine ⟨490934771275708938714133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 654579695034278584952177 490934771275708938714133)
              ·
                refine ⟨23012567403548856502225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 490934771275708938714133 23012567403548856502225)
                ·
                  rfl

theorem cell22_605027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 3, 2, 6].length) (baseStart_605027 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_605027 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_605027 prefixEnd_605027 := by exact prefixLift 605027
  have htrace : WordTrace (prefixWord ++ tailWord_605027) baseStart_605027 baseEnd_605027 := by
    simpa [prefixWord, tailWord_605027, baseEnd_605027] using wordTrace_append hprefix tailTrace_605027
  have hstable : (prefixWord ++ tailWord_605027).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_605027).length < 2 ^ (prefixWord ++ tailWord_605027).sum := by decide
  have hdescent : baseEnd_605027 < baseStart_605027 := by decide
  rcases family_descends (prefixWord ++ tailWord_605027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_605130 : List Nat := [3, 1, 2, 1, 2, 1, 1, 4, 1, 6]
def baseStart_605130 : Nat := 118140960795 + 605130 * 2 ^ 59
def prefixEnd_605130 : Nat := 4983230072969 + 3 ^ 40 * 605130 * 2
def baseEnd_605130 : Nat := 207148365636881773194709

theorem tailTrace_605130 : CollatzResearch.WordTrace tailWord_605130 prefixEnd_605130 207148365636881773194709 := by
  unfold tailWord_605130
  simp only [CollatzResearch.WordTrace]
  refine ⟨5517726074431208205289211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14713936198483221880771229 5517726074431208205289211)
  ·
    refine ⟨8276589111646812307933817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5517726074431208205289211 8276589111646812307933817)
    ·
      refine ⟨6207441833735109230950363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8276589111646812307933817 6207441833735109230950363)
      ·
        refine ⟨9311162750602663846425545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6207441833735109230950363 9311162750602663846425545)
        ·
          refine ⟨6983372062951997884819159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9311162750602663846425545 6983372062951997884819159)
          ·
            refine ⟨10475058094427996827228739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6983372062951997884819159 10475058094427996827228739)
            ·
              refine ⟨15712587141641995240843109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10475058094427996827228739 15712587141641995240843109)
              ·
                refine ⟨2946110089057874107658083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15712587141641995240843109 2946110089057874107658083)
                ·
                  refine ⟨4419165133586811161487125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2946110089057874107658083 4419165133586811161487125)
                  ·
                    refine ⟨207148365636881773194709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4419165133586811161487125 207148365636881773194709)
                    ·
                      rfl

theorem cell22_605130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 4, 1, 6].length) (baseStart_605130 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_605130 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_605130 prefixEnd_605130 := by exact prefixLift 605130
  have htrace : WordTrace (prefixWord ++ tailWord_605130) baseStart_605130 baseEnd_605130 := by
    simpa [prefixWord, tailWord_605130, baseEnd_605130] using wordTrace_append hprefix tailTrace_605130
  have hstable : (prefixWord ++ tailWord_605130).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_605130).length < 2 ^ (prefixWord ++ tailWord_605130).sum := by decide
  have hdescent : baseEnd_605130 < baseStart_605130 := by decide
  rcases family_descends (prefixWord ++ tailWord_605130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_605132 : List Nat := [2, 2, 1, 4, 1, 1, 4, 1, 1, 5]
def baseStart_605132 : Nat := 118140960795 + 605132 * 2 ^ 59
def prefixEnd_605132 : Nat := 4983230072969 + 3 ^ 40 * 605132 * 2
def baseEnd_605132 : Nat := 207149050277754434644703

theorem tailTrace_605132 : CollatzResearch.WordTrace tailWord_605132 prefixEnd_605132 207149050277754434644703 := by
  unfold tailWord_605132
  simp only [CollatzResearch.WordTrace]
  refine ⟨11035488621858793581364825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14713984829145058108486433 11035488621858793581364825)
  ·
    refine ⟨8276616466394095186023619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11035488621858793581364825 8276616466394095186023619)
    ·
      refine ⟨12414924699591142779035429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8276616466394095186023619 12414924699591142779035429)
      ·
        refine ⟨2327798381173339271069143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12414924699591142779035429 2327798381173339271069143)
        ·
          refine ⟨3491697571760008906603715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2327798381173339271069143 3491697571760008906603715)
          ·
            refine ⟨5237546357640013359905573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3491697571760008906603715 5237546357640013359905573)
            ·
              refine ⟨982039942057502504982295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5237546357640013359905573 982039942057502504982295)
              ·
                refine ⟨1473059913086253757473443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 982039942057502504982295 1473059913086253757473443)
                ·
                  refine ⟨2209589869629380636210165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1473059913086253757473443 2209589869629380636210165)
                  ·
                    refine ⟨207149050277754434644703, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2209589869629380636210165 207149050277754434644703)
                    ·
                      rfl

theorem cell22_605132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 4, 1, 1, 5].length) (baseStart_605132 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_605132 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_605132 prefixEnd_605132 := by exact prefixLift 605132
  have htrace : WordTrace (prefixWord ++ tailWord_605132) baseStart_605132 baseEnd_605132 := by
    simpa [prefixWord, tailWord_605132, baseEnd_605132] using wordTrace_append hprefix tailTrace_605132
  have hstable : (prefixWord ++ tailWord_605132).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_605132).length < 2 ^ (prefixWord ++ tailWord_605132).sum := by decide
  have hdescent : baseEnd_605132 < baseStart_605132 := by decide
  rcases family_descends (prefixWord ++ tailWord_605132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_605194 : List Nat := [3, 1, 2, 2, 3, 1, 2, 2, 3, 3]
def baseStart_605194 : Nat := 118140960795 + 605194 * 2 ^ 59
def prefixEnd_605194 : Nat := 4983230072969 + 3 ^ 40 * 605194 * 2
def baseEnd_605194 : Nat := 207170274144806939594513

theorem tailTrace_605194 : CollatzResearch.WordTrace tailWord_605194 prefixEnd_605194 207170274144806939594513 := by
  unfold tailWord_605194
  simp only [CollatzResearch.WordTrace]
  refine ⟨5518309642373242937871659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14715492379661981167657757 5518309642373242937871659)
  ·
    refine ⟨8277464463559864406807489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5518309642373242937871659 8277464463559864406807489)
    ·
      refine ⟨6208098347669898305105617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8277464463559864406807489 6208098347669898305105617)
      ·
        refine ⟨4656073760752423728829213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6208098347669898305105617 4656073760752423728829213)
        ·
          refine ⟨1746027660282158898310955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4656073760752423728829213 1746027660282158898310955)
          ·
            refine ⟨2619041490423238347466433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1746027660282158898310955 2619041490423238347466433)
            ·
              refine ⟨1964281117817428760599825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2619041490423238347466433 1964281117817428760599825)
              ·
                refine ⟨1473210838363071570449869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1964281117817428760599825 1473210838363071570449869)
                ·
                  refine ⟨552454064386151838918701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1473210838363071570449869 552454064386151838918701)
                  ·
                    refine ⟨207170274144806939594513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 552454064386151838918701 207170274144806939594513)
                    ·
                      rfl

theorem cell22_605194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 2, 2, 3, 3].length) (baseStart_605194 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_605194 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_605194 prefixEnd_605194 := by exact prefixLift 605194
  have htrace : WordTrace (prefixWord ++ tailWord_605194) baseStart_605194 baseEnd_605194 := by
    simpa [prefixWord, tailWord_605194, baseEnd_605194] using wordTrace_append hprefix tailTrace_605194
  have hstable : (prefixWord ++ tailWord_605194).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_605194).length < 2 ^ (prefixWord ++ tailWord_605194).sum := by decide
  have hdescent : baseEnd_605194 < baseStart_605194 := by decide
  rcases family_descends (prefixWord ++ tailWord_605194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_605202 : List Nat := [3, 2, 5, 1, 2, 1, 1, 3, 4]
def baseStart_605202 : Nat := 118140960795 + 605202 * 2 ^ 59
def prefixEnd_605202 : Nat := 4983230072969 + 3 ^ 40 * 605202 * 2
def baseEnd_605202 : Nat := 69057670902765861798163

theorem tailTrace_605202 : CollatzResearch.WordTrace tailWord_605202 prefixEnd_605202 69057670902765861798163 := by
  unfold tailWord_605202
  simp only [CollatzResearch.WordTrace]
  refine ⟨5518382588365997279444465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14715686902309326078518573 5518382588365997279444465)
  ·
    refine ⟨4138786941274497959583349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5518382588365997279444465 4138786941274497959583349)
    ·
      refine ⟨388011275744484183710939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 4138786941274497959583349 388011275744484183710939)
      ·
        refine ⟨582016913616726275566409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 388011275744484183710939 582016913616726275566409)
        ·
          refine ⟨436512685212544706674807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 582016913616726275566409 436512685212544706674807)
          ·
            refine ⟨654769027818817060012211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 436512685212544706674807 654769027818817060012211)
            ·
              refine ⟨982153541728225590018317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 654769027818817060012211 982153541728225590018317)
              ·
                refine ⟨368307578148084596256869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 982153541728225590018317 368307578148084596256869)
                ·
                  refine ⟨69057670902765861798163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 368307578148084596256869 69057670902765861798163)
                  ·
                    rfl

theorem cell22_605202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 2, 1, 1, 3, 4].length) (baseStart_605202 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_605202 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_605202 prefixEnd_605202 := by exact prefixLift 605202
  have htrace : WordTrace (prefixWord ++ tailWord_605202) baseStart_605202 baseEnd_605202 := by
    simpa [prefixWord, tailWord_605202, baseEnd_605202] using wordTrace_append hprefix tailTrace_605202
  have hstable : (prefixWord ++ tailWord_605202).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_605202).length < 2 ^ (prefixWord ++ tailWord_605202).sum := by decide
  have hdescent : baseEnd_605202 < baseStart_605202 := by decide
  rcases family_descends (prefixWord ++ tailWord_605202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_605207 : List Nat := [1, 1, 3, 5, 1, 1, 1, 2, 7]
def baseStart_605207 : Nat := 118140960795 + 605207 * 2 ^ 59
def prefixEnd_605207 : Nat := 4983230072969 + 3 ^ 40 * 605207 * 2
def baseEnd_605207 : Nat := 69058241436826413006491

theorem tailTrace_605207 : CollatzResearch.WordTrace tailWord_605207 prefixEnd_605207 69058241436826413006491 := by
  unfold tailWord_605207
  simp only [CollatzResearch.WordTrace]
  refine ⟨22073712718445874971709875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14715808478963916647806583 22073712718445874971709875)
  ·
    refine ⟨33110569077668812457564813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22073712718445874971709875 33110569077668812457564813)
    ·
      refine ⟨12416463404125804671586805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33110569077668812457564813 12416463404125804671586805)
      ·
        refine ⟨1164043444136794187961263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 12416463404125804671586805 1164043444136794187961263)
        ·
          refine ⟨1746065166205191281941895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1164043444136794187961263 1746065166205191281941895)
          ·
            refine ⟨2619097749307786922912843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1746065166205191281941895 2619097749307786922912843)
            ·
              refine ⟨3928646623961680384369265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2619097749307786922912843 3928646623961680384369265)
              ·
                refine ⟨2946484967971260288276949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3928646623961680384369265 2946484967971260288276949)
                ·
                  refine ⟨69058241436826413006491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2946484967971260288276949 69058241436826413006491)
                  ·
                    rfl

theorem cell22_605207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 1, 2, 7].length) (baseStart_605207 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_605207 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_605207 prefixEnd_605207 := by exact prefixLift 605207
  have htrace : WordTrace (prefixWord ++ tailWord_605207) baseStart_605207 baseEnd_605207 := by
    simpa [prefixWord, tailWord_605207, baseEnd_605207] using wordTrace_append hprefix tailTrace_605207
  have hstable : (prefixWord ++ tailWord_605207).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_605207).length < 2 ^ (prefixWord ++ tailWord_605207).sum := by decide
  have hdescent : baseEnd_605207 < baseStart_605207 := by decide
  rcases family_descends (prefixWord ++ tailWord_605207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_605237 : List Nat := [1, 3, 3, 1, 1, 1, 1, 4, 3, 4]
def baseStart_605237 : Nat := 118140960795 + 605237 * 2 ^ 59
def prefixEnd_605237 : Nat := 4983230072969 + 3 ^ 40 * 605237 * 2
def baseEnd_605237 : Nat := 207184993923569160769381

theorem tailTrace_605237 : CollatzResearch.WordTrace tailWord_605237 prefixEnd_605237 207184993923569160769381 := by
  unfold tailWord_605237
  simp only [CollatzResearch.WordTrace]
  refine ⟨22074806908337190095301965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14716537938891460063534643 22074806908337190095301965)
  ·
    refine ⟨8278052590626446285738237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22074806908337190095301965 8278052590626446285738237)
    ·
      refine ⟨3104269721484917357151839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8278052590626446285738237 3104269721484917357151839)
      ·
        refine ⟨4656404582227376035727759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3104269721484917357151839 4656404582227376035727759)
        ·
          refine ⟨6984606873341064053591639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4656404582227376035727759 6984606873341064053591639)
          ·
            refine ⟨10476910310011596080387459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6984606873341064053591639 10476910310011596080387459)
            ·
              refine ⟨15715365465017394120581189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10476910310011596080387459 15715365465017394120581189)
              ·
                refine ⟨2946631024690761397608973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15715365465017394120581189 2946631024690761397608973)
                ·
                  refine ⟨1104986634259035524103365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2946631024690761397608973 1104986634259035524103365)
                  ·
                    refine ⟨207184993923569160769381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1104986634259035524103365 207184993923569160769381)
                    ·
                      rfl

theorem cell22_605237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 4, 3, 4].length) (baseStart_605237 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_605237 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_605237 prefixEnd_605237 := by exact prefixLift 605237
  have htrace : WordTrace (prefixWord ++ tailWord_605237) baseStart_605237 baseEnd_605237 := by
    simpa [prefixWord, tailWord_605237, baseEnd_605237] using wordTrace_append hprefix tailTrace_605237
  have hstable : (prefixWord ++ tailWord_605237).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_605237).length < 2 ^ (prefixWord ++ tailWord_605237).sum := by decide
  have hdescent : baseEnd_605237 < baseStart_605237 := by decide
  rcases family_descends (prefixWord ++ tailWord_605237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_605241 : List Nat := [1, 2, 1, 5, 2, 3, 2, 1, 5]
def baseStart_605241 : Nat := 118140960795 + 605241 * 2 ^ 59
def prefixEnd_605241 : Nat := 4983230072969 + 3 ^ 40 * 605241 * 2
def baseEnd_605241 : Nat := 69062121068438161223123

theorem tailTrace_605241 : CollatzResearch.WordTrace tailWord_605241 prefixEnd_605241 69062121068438161223123 := by
  unfold tailWord_605241
  simp only [CollatzResearch.WordTrace]
  refine ⟨22074952800322698778447577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14716635200215132518965051 22074952800322698778447577)
  ·
    refine ⟨16556214600242024083835683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22074952800322698778447577 16556214600242024083835683)
    ·
      refine ⟨24834321900363036125753525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16556214600242024083835683 24834321900363036125753525)
      ·
        refine ⟨2328217678159034636789393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 24834321900363036125753525 2328217678159034636789393)
        ·
          refine ⟨1746163258619275977592045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2328217678159034636789393 1746163258619275977592045)
          ·
            refine ⟨654811221982228491597017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1746163258619275977592045 654811221982228491597017)
            ·
              refine ⟨491108416486671368697763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 654811221982228491597017 491108416486671368697763)
              ·
                refine ⟨736662624730007053046645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 491108416486671368697763 736662624730007053046645)
                ·
                  refine ⟨69062121068438161223123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 736662624730007053046645 69062121068438161223123)
                  ·
                    rfl

theorem cell22_605241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 3, 2, 1, 5].length) (baseStart_605241 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_605241 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_605241 prefixEnd_605241 := by exact prefixLift 605241
  have htrace : WordTrace (prefixWord ++ tailWord_605241) baseStart_605241 baseEnd_605241 := by
    simpa [prefixWord, tailWord_605241, baseEnd_605241] using wordTrace_append hprefix tailTrace_605241
  have hstable : (prefixWord ++ tailWord_605241).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_605241).length < 2 ^ (prefixWord ++ tailWord_605241).sum := by decide
  have hdescent : baseEnd_605241 < baseStart_605241 := by decide
  rcases family_descends (prefixWord ++ tailWord_605241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_605269 : List Nat := [1, 3, 2, 2, 1, 2, 2, 5, 4]
def baseStart_605269 : Nat := 118140960795 + 605269 * 2 ^ 59
def prefixEnd_605269 : Nat := 4983230072969 + 3 ^ 40 * 605269 * 2
def baseEnd_605269 : Nat := 69065316059177247989761

theorem tailTrace_605269 : CollatzResearch.WordTrace tailWord_605269 prefixEnd_605269 69065316059177247989761 := by
  unfold tailWord_605269
  simp only [CollatzResearch.WordTrace]
  refine ⟨22075974044221259560466861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14717316029480839706977907 22075974044221259560466861)
  ·
    refine ⟨8278490266582972335175073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22075974044221259560466861 8278490266582972335175073)
    ·
      refine ⟨6208867699937229251381305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8278490266582972335175073 6208867699937229251381305)
      ·
        refine ⟨4656650774952921938535979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6208867699937229251381305 4656650774952921938535979)
        ·
          refine ⟨6984976162429382907803969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4656650774952921938535979 6984976162429382907803969)
          ·
            refine ⟨5238732121822037180852977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6984976162429382907803969 5238732121822037180852977)
            ·
              refine ⟨3929049091366527885639733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5238732121822037180852977 3929049091366527885639733)
              ·
                refine ⟨368348352315611989278725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3929049091366527885639733 368348352315611989278725)
                ·
                  refine ⟨69065316059177247989761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 368348352315611989278725 69065316059177247989761)
                  ·
                    rfl

theorem cell22_605269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 2, 5, 4].length) (baseStart_605269 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_605269 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_605269 prefixEnd_605269 := by exact prefixLift 605269
  have htrace : WordTrace (prefixWord ++ tailWord_605269) baseStart_605269 baseEnd_605269 := by
    simpa [prefixWord, tailWord_605269, baseEnd_605269] using wordTrace_append hprefix tailTrace_605269
  have hstable : (prefixWord ++ tailWord_605269).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_605269).length < 2 ^ (prefixWord ++ tailWord_605269).sum := by decide
  have hdescent : baseEnd_605269 < baseStart_605269 := by decide
  rcases family_descends (prefixWord ++ tailWord_605269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_605316 : List Nat := [2, 3, 2, 1, 2, 4, 1, 1, 2, 4]
def baseStart_605316 : Nat := 118140960795 + 605316 * 2 ^ 59
def prefixEnd_605316 : Nat := 4983230072969 + 3 ^ 40 * 605316 * 2
def baseEnd_605316 : Nat := 207212037238039288044139

theorem tailTrace_605316 : CollatzResearch.WordTrace tailWord_605316 prefixEnd_605316 207212037238039288044139 := by
  unfold tailWord_605316
  simp only [CollatzResearch.WordTrace]
  refine ⟨11038844137525493293713901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14718458850033991058285201 11038844137525493293713901)
  ·
    refine ⟨4139566551572059985142713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11038844137525493293713901 4139566551572059985142713)
    ·
      refine ⟨3104674913679044988857035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4139566551572059985142713 3104674913679044988857035)
      ·
        refine ⟨4657012370518567483285553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3104674913679044988857035 4657012370518567483285553)
        ·
          refine ⟨3492759277888925612464165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4657012370518567483285553 3492759277888925612464165)
          ·
            refine ⟨654892364604173552337031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3492759277888925612464165 654892364604173552337031)
            ·
              refine ⟨982338546906260328505547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 654892364604173552337031 982338546906260328505547)
              ·
                refine ⟨1473507820359390492758321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 982338546906260328505547 1473507820359390492758321)
                ·
                  refine ⟨1105130865269542869568741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1473507820359390492758321 1105130865269542869568741)
                  ·
                    refine ⟨207212037238039288044139, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1105130865269542869568741 207212037238039288044139)
                    ·
                      rfl

theorem cell22_605316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 4, 1, 1, 2, 4].length) (baseStart_605316 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_605316 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_605316 prefixEnd_605316 := by exact prefixLift 605316
  have htrace : WordTrace (prefixWord ++ tailWord_605316) baseStart_605316 baseEnd_605316 := by
    simpa [prefixWord, tailWord_605316, baseEnd_605316] using wordTrace_append hprefix tailTrace_605316
  have hstable : (prefixWord ++ tailWord_605316).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_605316).length < 2 ^ (prefixWord ++ tailWord_605316).sum := by decide
  have hdescent : baseEnd_605316 < baseStart_605316 := by decide
  rcases family_descends (prefixWord ++ tailWord_605316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_605423 : List Nat := [1, 1, 2, 1, 7, 2, 1, 2, 1, 4]
def baseStart_605423 : Nat := 118140960795 + 605423 * 2 ^ 59
def prefixEnd_605423 : Nat := 4983230072969 + 3 ^ 40 * 605423 * 2
def baseEnd_605423 : Nat := 207248665524726675618811

theorem tailTrace_605423 : CollatzResearch.WordTrace tailWord_605423 prefixEnd_605423 207248665524726675618811 := by
  unfold tailWord_605423
  simp only [CollatzResearch.WordTrace]
  refine ⟨22081590885663343861572923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14721060590442229241048615 22081590885663343861572923)
  ·
    refine ⟨33122386328495015792359385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22081590885663343861572923 33122386328495015792359385)
    ·
      refine ⟨24841789746371261844269539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33122386328495015792359385 24841789746371261844269539)
      ·
        refine ⟨37262684619556892766404309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24841789746371261844269539 37262684619556892766404309)
        ·
          refine ⟨873344170770864674212601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 37262684619556892766404309 873344170770864674212601)
          ·
            refine ⟨655008128078148505659451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 873344170770864674212601 655008128078148505659451)
            ·
              refine ⟨982512192117222758489177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 655008128078148505659451 982512192117222758489177)
              ·
                refine ⟨736884144087917068866883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 982512192117222758489177 736884144087917068866883)
                ·
                  refine ⟨1105326216131875603300325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 736884144087917068866883 1105326216131875603300325)
                  ·
                    refine ⟨207248665524726675618811, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1105326216131875603300325 207248665524726675618811)
                    ·
                      rfl

theorem cell22_605423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 2, 1, 2, 1, 4].length) (baseStart_605423 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_605423 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_605423 prefixEnd_605423 := by exact prefixLift 605423
  have htrace : WordTrace (prefixWord ++ tailWord_605423) baseStart_605423 baseEnd_605423 := by
    simpa [prefixWord, tailWord_605423, baseEnd_605423] using wordTrace_append hprefix tailTrace_605423
  have hstable : (prefixWord ++ tailWord_605423).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_605423).length < 2 ^ (prefixWord ++ tailWord_605423).sum := by decide
  have hdescent : baseEnd_605423 < baseStart_605423 := by decide
  rcases family_descends (prefixWord ++ tailWord_605423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_605436 : List Nat := [2, 2, 2, 1, 5, 1, 1, 2, 1, 5]
def baseStart_605436 : Nat := 118140960795 + 605436 * 2 ^ 59
def prefixEnd_605436 : Nat := 4983230072969 + 3 ^ 40 * 605436 * 2
def baseEnd_605436 : Nat := 207253115690398975043771

theorem tailTrace_605436 : CollatzResearch.WordTrace tailWord_605436 prefixEnd_605436 207253115690398975043771 := by
  unfold tailWord_605436
  simp only [CollatzResearch.WordTrace]
  refine ⟨11041032517308123540898081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14721376689744164721197441 11041032517308123540898081)
  ·
    refine ⟨8280774387981092655673561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11041032517308123540898081 8280774387981092655673561)
    ·
      refine ⟨6210580790985819491755171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8280774387981092655673561 6210580790985819491755171)
      ·
        refine ⟨9315871186478729237632757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6210580790985819491755171 9315871186478729237632757)
        ·
          refine ⟨873362923732380866028071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 9315871186478729237632757 873362923732380866028071)
          ·
            refine ⟨1310044385598571299042107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 873362923732380866028071 1310044385598571299042107)
            ·
              refine ⟨1965066578397856948563161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1310044385598571299042107 1965066578397856948563161)
              ·
                refine ⟨1473799933798392711422371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1965066578397856948563161 1473799933798392711422371)
                ·
                  refine ⟨2210699900697589067133557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1473799933798392711422371 2210699900697589067133557)
                  ·
                    refine ⟨207253115690398975043771, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2210699900697589067133557 207253115690398975043771)
                    ·
                      rfl

theorem cell22_605436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 1, 1, 2, 1, 5].length) (baseStart_605436 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_605436 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_605436 prefixEnd_605436 := by exact prefixLift 605436
  have htrace : WordTrace (prefixWord ++ tailWord_605436) baseStart_605436 baseEnd_605436 := by
    simpa [prefixWord, tailWord_605436, baseEnd_605436] using wordTrace_append hprefix tailTrace_605436
  have hstable : (prefixWord ++ tailWord_605436).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_605436).length < 2 ^ (prefixWord ++ tailWord_605436).sum := by decide
  have hdescent : baseEnd_605436 < baseStart_605436 := by decide
  rcases family_descends (prefixWord ++ tailWord_605436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_605466 : List Nat := [3, 1, 1, 3, 3, 3, 1, 7]
def baseStart_605466 : Nat := 118140960795 + 605466 * 2 ^ 59
def prefixEnd_605466 : Nat := 4983230072969 + 3 ^ 40 * 605466 * 2
def baseEnd_605466 : Nat := 23029265033720988532631

theorem tailTrace_605466 : CollatzResearch.WordTrace tailWord_605466 prefixEnd_605466 23029265033720988532631 := by
  unfold tailWord_605466
  simp only [CollatzResearch.WordTrace]
  refine ⟨5520789806126890551347063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14722106149671708136925501 5520789806126890551347063)
  ·
    refine ⟨8281184709190335827020595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5520789806126890551347063 8281184709190335827020595)
    ·
      refine ⟨12421777063785503740530893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8281184709190335827020595 12421777063785503740530893)
      ·
        refine ⟨4658166398919563902699085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12421777063785503740530893 4658166398919563902699085)
        ·
          refine ⟨1746812399594836463512157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4658166398919563902699085 1746812399594836463512157)
          ·
            refine ⟨655054649848063673817059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1746812399594836463512157 655054649848063673817059)
            ·
              refine ⟨982581974772095510725589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 655054649848063673817059 982581974772095510725589)
              ·
                refine ⟨23029265033720988532631, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 982581974772095510725589 23029265033720988532631)
                ·
                  rfl

theorem cell22_605466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 3, 1, 7].length) (baseStart_605466 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_605466 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_605466 prefixEnd_605466 := by exact prefixLift 605466
  have htrace : WordTrace (prefixWord ++ tailWord_605466) baseStart_605466 baseEnd_605466 := by
    simpa [prefixWord, tailWord_605466, baseEnd_605466] using wordTrace_append hprefix tailTrace_605466
  have hstable : (prefixWord ++ tailWord_605466).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_605466).length < 2 ^ (prefixWord ++ tailWord_605466).sum := by decide
  have hdescent : baseEnd_605466 < baseStart_605466 := by decide
  rcases family_descends (prefixWord ++ tailWord_605466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_605470 : List Nat := [4, 3, 2, 1, 2, 1, 2, 1, 1, 5]
def baseStart_605470 : Nat := 118140960795 + 605470 * 2 ^ 59
def prefixEnd_605470 : Nat := 4983230072969 + 3 ^ 40 * 605470 * 2
def baseEnd_605470 : Nat := 207264754585234219693667

theorem tailTrace_605470 : CollatzResearch.WordTrace tailWord_605470 prefixEnd_605470 207264754585234219693667 := by
  unfold tailWord_605470
  simp only [CollatzResearch.WordTrace]
  refine ⟨2760413139561633861066733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14722203410995380592355909 2760413139561633861066733)
  ·
    refine ⟨1035154927335612697900025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2760413139561633861066733 1035154927335612697900025)
    ·
      refine ⟨776366195501709523425019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1035154927335612697900025 776366195501709523425019)
      ·
        refine ⟨1164549293252564285137529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 776366195501709523425019 1164549293252564285137529)
        ·
          refine ⟨873411969939423213853147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1164549293252564285137529 873411969939423213853147)
          ·
            refine ⟨1310117954909134820779721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 873411969939423213853147 1310117954909134820779721)
            ·
              refine ⟨982588466181851115584791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1310117954909134820779721 982588466181851115584791)
              ·
                refine ⟨1473882699272776673377187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 982588466181851115584791 1473882699272776673377187)
                ·
                  refine ⟨2210824048909165010065781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1473882699272776673377187 2210824048909165010065781)
                  ·
                    refine ⟨207264754585234219693667, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2210824048909165010065781 207264754585234219693667)
                    ·
                      rfl

theorem cell22_605470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 1, 2, 1, 1, 5].length) (baseStart_605470 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_605470 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_605470 prefixEnd_605470 := by exact prefixLift 605470
  have htrace : WordTrace (prefixWord ++ tailWord_605470) baseStart_605470 baseEnd_605470 := by
    simpa [prefixWord, tailWord_605470, baseEnd_605470] using wordTrace_append hprefix tailTrace_605470
  have hstable : (prefixWord ++ tailWord_605470).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_605470).length < 2 ^ (prefixWord ++ tailWord_605470).sum := by decide
  have hdescent : baseEnd_605470 < baseStart_605470 := by decide
  rcases family_descends (prefixWord ++ tailWord_605470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_605485 : List Nat := [1, 5, 3, 1, 1, 3, 1, 1, 2, 4]
def baseStart_605485 : Nat := 118140960795 + 605485 * 2 ^ 59
def prefixEnd_605485 : Nat := 4983230072969 + 3 ^ 40 * 605485 * 2
def baseEnd_605485 : Nat := 207269889391779180568621

theorem tailTrace_605485 : CollatzResearch.WordTrace tailWord_605485 prefixEnd_605485 207269889391779180568621 := by
  unfold tailWord_605485
  simp only [CollatzResearch.WordTrace]
  refine ⟨22083852211438728450329909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14722568140959152300219939 22083852211438728450329909)
  ·
    refine ⟨2070361144822380792218429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 22083852211438728450329909 2070361144822380792218429)
    ·
      refine ⟨776385429308392797081911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2070361144822380792218429 776385429308392797081911)
      ·
        refine ⟨1164578143962589195622867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 776385429308392797081911 1164578143962589195622867)
        ·
          refine ⟨1746867215943883793434301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1164578143962589195622867 1746867215943883793434301)
          ·
            refine ⟨655075205978956422537863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1746867215943883793434301 655075205978956422537863)
            ·
              refine ⟨982612808968434633806795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 655075205978956422537863 982612808968434633806795)
              ·
                refine ⟨1473919213452651950710193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 982612808968434633806795 1473919213452651950710193)
                ·
                  refine ⟨1105439410089488963032645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1473919213452651950710193 1105439410089488963032645)
                  ·
                    refine ⟨207269889391779180568621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1105439410089488963032645 207269889391779180568621)
                    ·
                      rfl

theorem cell22_605485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 3, 1, 1, 2, 4].length) (baseStart_605485 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_605485 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_605485 prefixEnd_605485 := by exact prefixLift 605485
  have htrace : WordTrace (prefixWord ++ tailWord_605485) baseStart_605485 baseEnd_605485 := by
    simpa [prefixWord, tailWord_605485, baseEnd_605485] using wordTrace_append hprefix tailTrace_605485
  have hstable : (prefixWord ++ tailWord_605485).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_605485).length < 2 ^ (prefixWord ++ tailWord_605485).sum := by decide
  have hdescent : baseEnd_605485 < baseStart_605485 := by decide
  rcases family_descends (prefixWord ++ tailWord_605485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_605511 : List Nat := [1, 1, 4, 1, 2, 3, 3, 2, 5]
def baseStart_605511 : Nat := 118140960795 + 605511 * 2 ^ 59
def prefixEnd_605511 : Nat := 4983230072969 + 3 ^ 40 * 605511 * 2
def baseEnd_605511 : Nat := 69092929907707926472847

theorem tailTrace_605511 : CollatzResearch.WordTrace tailWord_605511 prefixEnd_605511 69092929907707926472847 := by
  unfold tailWord_605511
  simp only [CollatzResearch.WordTrace]
  refine ⟨22084800509344534890776387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14723200339563023260517591 22084800509344534890776387)
  ·
    refine ⟨33127200764016802336164581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22084800509344534890776387 33127200764016802336164581)
    ·
      refine ⟨6211350143253150438030859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 33127200764016802336164581 6211350143253150438030859)
      ·
        refine ⟨9317025214879725657046289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6211350143253150438030859 9317025214879725657046289)
        ·
          refine ⟨6987768911159794242784717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9317025214879725657046289 6987768911159794242784717)
          ·
            refine ⟨2620413341684922841044269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6987768911159794242784717 2620413341684922841044269)
            ·
              refine ⟨982655003131846065391601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2620413341684922841044269 982655003131846065391601)
              ·
                refine ⟨736991252348884549043701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 982655003131846065391601 736991252348884549043701)
                ·
                  refine ⟨69092929907707926472847, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 736991252348884549043701 69092929907707926472847)
                  ·
                    rfl

theorem cell22_605511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 3, 2, 5].length) (baseStart_605511 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_605511 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_605511 prefixEnd_605511 := by exact prefixLift 605511
  have htrace : WordTrace (prefixWord ++ tailWord_605511) baseStart_605511 baseEnd_605511 := by
    simpa [prefixWord, tailWord_605511, baseEnd_605511] using wordTrace_append hprefix tailTrace_605511
  have hstable : (prefixWord ++ tailWord_605511).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_605511).length < 2 ^ (prefixWord ++ tailWord_605511).sum := by decide
  have hdescent : baseEnd_605511 < baseStart_605511 := by decide
  rcases family_descends (prefixWord ++ tailWord_605511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_605566 : List Nat := [4, 2, 3, 2, 1, 1, 3, 2, 1, 3]
def baseStart_605566 : Nat := 118140960795 + 605566 * 2 ^ 59
def prefixEnd_605566 : Nat := 4983230072969 + 3 ^ 40 * 605566 * 2
def baseEnd_605566 : Nat := 207297617347121969293373

theorem tailTrace_605566 : CollatzResearch.WordTrace tailWord_605566 prefixEnd_605566 207297617347121969293373 := by
  unfold tailWord_605566
  simp only [CollatzResearch.WordTrace]
  refine ⟨2760850815518159910503569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14724537682763519522685701 2760850815518159910503569)
  ·
    refine ⟨2070638111638619932877677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2760850815518159910503569 2070638111638619932877677)
    ·
      refine ⟨776489291864482474829129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2070638111638619932877677 776489291864482474829129)
      ·
        refine ⟨582366968898361856121847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 776489291864482474829129 582366968898361856121847)
        ·
          refine ⟨873550453347542784182771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 582366968898361856121847 873550453347542784182771)
          ·
            refine ⟨1310325680021314176274157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 873550453347542784182771 1310325680021314176274157)
            ·
              refine ⟨491372130007992816102809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1310325680021314176274157 491372130007992816102809)
              ·
                refine ⟨368529097505994612077107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 491372130007992816102809 368529097505994612077107)
                ·
                  refine ⟨552793646258991918115661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 368529097505994612077107 552793646258991918115661)
                  ·
                    refine ⟨207297617347121969293373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 552793646258991918115661 207297617347121969293373)
                    ·
                      rfl

theorem cell22_605566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 1, 3, 2, 1, 3].length) (baseStart_605566 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_605566 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_605566 prefixEnd_605566 := by exact prefixLift 605566
  have htrace : WordTrace (prefixWord ++ tailWord_605566) baseStart_605566 baseEnd_605566 := by
    simpa [prefixWord, tailWord_605566, baseEnd_605566] using wordTrace_append hprefix tailTrace_605566
  have hstable : (prefixWord ++ tailWord_605566).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_605566).length < 2 ^ (prefixWord ++ tailWord_605566).sum := by decide
  have hdescent : baseEnd_605566 < baseStart_605566 := by decide
  rcases family_descends (prefixWord ++ tailWord_605566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_605592 : List Nat := [2, 1, 2, 5, 3, 1, 1, 2, 1, 4]
def baseStart_605592 : Nat := 118140960795 + 605592 * 2 ^ 59
def prefixEnd_605592 : Nat := 4983230072969 + 3 ^ 40 * 605592 * 2
def baseEnd_605592 : Nat := 207306517678466568143293

theorem tailTrace_605592 : CollatzResearch.WordTrace tailWord_605592 prefixEnd_605592 207306517678466568143293 := by
  unfold tailWord_605592
  simp only [CollatzResearch.WordTrace]
  refine ⟨11043877411025542862237515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14725169881367390482983353 11043877411025542862237515)
  ·
    refine ⟨16565816116538314293356273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11043877411025542862237515 16565816116538314293356273)
    ·
      refine ⟨12424362087403735720017205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16565816116538314293356273 12424362087403735720017205)
      ·
        refine ⟨1164783945694100223751613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 12424362087403735720017205 1164783945694100223751613)
        ·
          refine ⟨436793979635287583906855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1164783945694100223751613 436793979635287583906855)
          ·
            refine ⟨655190969452931375860283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 436793979635287583906855 655190969452931375860283)
            ·
              refine ⟨982786454179397063790425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 655190969452931375860283 982786454179397063790425)
              ·
                refine ⟨737089840634547797842819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 982786454179397063790425 737089840634547797842819)
                ·
                  refine ⟨1105634760951821696764229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 737089840634547797842819 1105634760951821696764229)
                  ·
                    refine ⟨207306517678466568143293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1105634760951821696764229 207306517678466568143293)
                    ·
                      rfl

theorem cell22_605592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 3, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 3, 1, 1, 2, 1, 4].length) (baseStart_605592 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_605592 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_605592 prefixEnd_605592 := by exact prefixLift 605592
  have htrace : WordTrace (prefixWord ++ tailWord_605592) baseStart_605592 baseEnd_605592 := by
    simpa [prefixWord, tailWord_605592, baseEnd_605592] using wordTrace_append hprefix tailTrace_605592
  have hstable : (prefixWord ++ tailWord_605592).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_605592).length < 2 ^ (prefixWord ++ tailWord_605592).sum := by decide
  have hdescent : baseEnd_605592 < baseStart_605592 := by decide
  rcases family_descends (prefixWord ++ tailWord_605592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_605616 : List Nat := [2, 1, 1, 1, 2, 1, 1, 3, 7, 3]
def baseStart_605616 : Nat := 118140960795 + 605616 * 2 ^ 59
def prefixEnd_605616 : Nat := 4983230072969 + 3 ^ 40 * 605616 * 2
def baseEnd_605616 : Nat := 207314733368938505543219

theorem tailTrace_605616 : CollatzResearch.WordTrace tailWord_605616 prefixEnd_605616 207314733368938505543219 := by
  unfold tailWord_605616
  simp only [CollatzResearch.WordTrace]
  refine ⟨11044315086982068911674351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14725753449309425215565801 11044315086982068911674351)
  ·
    refine ⟨16566472630473103367511527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11044315086982068911674351 16566472630473103367511527)
    ·
      refine ⟨24849708945709655051267291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16566472630473103367511527 24849708945709655051267291)
      ·
        refine ⟨37274563418564482576900937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24849708945709655051267291 37274563418564482576900937)
        ·
          refine ⟨27955922563923361932675703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37274563418564482576900937 27955922563923361932675703)
          ·
            refine ⟨41933883845885042899013555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27955922563923361932675703 41933883845885042899013555)
            ·
              refine ⟨62900825768827564348520333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41933883845885042899013555 62900825768827564348520333)
              ·
                refine ⟨23587809663310336630695125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 62900825768827564348520333 23587809663310336630695125)
                ·
                  refine ⟨552839288983836014781917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 23587809663310336630695125 552839288983836014781917)
                  ·
                    refine ⟨207314733368938505543219, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 552839288983836014781917 207314733368938505543219)
                    ·
                      rfl

theorem cell22_605616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 3, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 3, 7, 3].length) (baseStart_605616 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_605616 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_605616 prefixEnd_605616 := by exact prefixLift 605616
  have htrace : WordTrace (prefixWord ++ tailWord_605616) baseStart_605616 baseEnd_605616 := by
    simpa [prefixWord, tailWord_605616, baseEnd_605616] using wordTrace_append hprefix tailTrace_605616
  have hstable : (prefixWord ++ tailWord_605616).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_605616).length < 2 ^ (prefixWord ++ tailWord_605616).sum := by decide
  have hdescent : baseEnd_605616 < baseStart_605616 := by decide
  rcases family_descends (prefixWord ++ tailWord_605616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_605667 : List Nat := [1, 1, 1, 6, 2, 2, 2, 3, 1, 3]
def baseStart_605667 : Nat := 118140960795 + 605667 * 2 ^ 59
def prefixEnd_605667 : Nat := 4983230072969 + 3 ^ 40 * 605667 * 2
def baseEnd_605667 : Nat := 207332191711191372518063

theorem tailTrace_605667 : CollatzResearch.WordTrace tailWord_605667 prefixEnd_605667 207332191711191372518063 := by
  unfold tailWord_605667
  simp only [CollatzResearch.WordTrace]
  refine ⟨22090490296779373533455255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14726993531186249022303503 22090490296779373533455255)
  ·
    refine ⟨33135735445169060300182883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22090490296779373533455255 33135735445169060300182883)
    ·
      refine ⟨49703603167753590450274325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33135735445169060300182883 49703603167753590450274325)
      ·
        refine ⟨2329856398488449552356609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 49703603167753590450274325 2329856398488449552356609)
        ·
          refine ⟨1747392298866337164267457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2329856398488449552356609 1747392298866337164267457)
          ·
            refine ⟨1310544224149752873200593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1747392298866337164267457 1310544224149752873200593)
            ·
              refine ⟨982908168112314654900445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1310544224149752873200593 982908168112314654900445)
              ·
                refine ⟨368590563042117995587667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 982908168112314654900445 368590563042117995587667)
                ·
                  refine ⟨552885844563176993381501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 368590563042117995587667 552885844563176993381501)
                  ·
                    refine ⟨207332191711191372518063, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 552885844563176993381501 207332191711191372518063)
                    ·
                      rfl

theorem cell22_605667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 2, 2, 3, 1, 3].length) (baseStart_605667 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_605667 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_605667 prefixEnd_605667 := by exact prefixLift 605667
  have htrace : WordTrace (prefixWord ++ tailWord_605667) baseStart_605667 baseEnd_605667 := by
    simpa [prefixWord, tailWord_605667, baseEnd_605667] using wordTrace_append hprefix tailTrace_605667
  have hstable : (prefixWord ++ tailWord_605667).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_605667).length < 2 ^ (prefixWord ++ tailWord_605667).sum := by decide
  have hdescent : baseEnd_605667 < baseStart_605667 := by decide
  rcases family_descends (prefixWord ++ tailWord_605667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_605676 : List Nat := [2, 2, 1, 1, 2, 1, 2, 2, 5, 4]
def baseStart_605676 : Nat := 118140960795 + 605676 * 2 ^ 59
def prefixEnd_605676 : Nat := 4983230072969 + 3 ^ 40 * 605676 * 2
def baseEnd_605676 : Nat := 207335272595118349043035

theorem tailTrace_605676 : CollatzResearch.WordTrace tailWord_605676 prefixEnd_605676 207335272595118349043035 := by
  unfold tailWord_605676
  simp only [CollatzResearch.WordTrace]
  refine ⟨11045409276873384035266441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14727212369164512047021921 11045409276873384035266441)
  ·
    refine ⟨8284056957655038026449831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11045409276873384035266441 8284056957655038026449831)
    ·
      refine ⟨12426085436482557039674747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8284056957655038026449831 12426085436482557039674747)
      ·
        refine ⟨18639128154723835559512121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12426085436482557039674747 18639128154723835559512121)
        ·
          refine ⟨13979346116042876669634091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18639128154723835559512121 13979346116042876669634091)
          ·
            refine ⟨20969019174064315004451137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13979346116042876669634091 20969019174064315004451137)
            ·
              refine ⟨15726764380548236253338353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20969019174064315004451137 15726764380548236253338353)
              ·
                refine ⟨11795073285411177190003765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15726764380548236253338353 11795073285411177190003765)
                ·
                  refine ⟨1105788120507297861562853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 11795073285411177190003765 1105788120507297861562853)
                  ·
                    refine ⟨207335272595118349043035, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1105788120507297861562853 207335272595118349043035)
                    ·
                      rfl

theorem cell22_605676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 4].length) (baseStart_605676 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_605676 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_605676 prefixEnd_605676 := by exact prefixLift 605676
  have htrace : WordTrace (prefixWord ++ tailWord_605676) baseStart_605676 baseEnd_605676 := by
    simpa [prefixWord, tailWord_605676, baseEnd_605676] using wordTrace_append hprefix tailTrace_605676
  have hstable : (prefixWord ++ tailWord_605676).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_605676).length < 2 ^ (prefixWord ++ tailWord_605676).sum := by decide
  have hdescent : baseEnd_605676 < baseStart_605676 := by decide
  rcases family_descends (prefixWord ++ tailWord_605676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_605753 : List Nat := [1, 2, 1, 5, 1, 3, 2, 7]
def baseStart_605753 : Nat := 118140960795 + 605753 * 2 ^ 59
def prefixEnd_605753 : Nat := 4983230072969 + 3 ^ 40 * 605753 * 2
def baseEnd_605753 : Nat := 23040181252079534985311

theorem tailTrace_605753 : CollatzResearch.WordTrace tailWord_605753 prefixEnd_605753 23040181252079534985311 := by
  unfold tailWord_605753
  simp only [CollatzResearch.WordTrace]
  refine ⟨22093626974467810221085913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14729084649645206814057275 22093626974467810221085913)
  ·
    refine ⟨16570220230850857665814435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22093626974467810221085913 16570220230850857665814435)
    ·
      refine ⟨24855330346276286498721653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16570220230850857665814435 24855330346276286498721653)
      ·
        refine ⟨2330187219963401859255155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 24855330346276286498721653 2330187219963401859255155)
        ·
          refine ⟨3495280829945102788882733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2330187219963401859255155 3495280829945102788882733)
          ·
            refine ⟨1310730311229413545831025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3495280829945102788882733 1310730311229413545831025)
            ·
              refine ⟨983047733422060159373269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1310730311229413545831025 983047733422060159373269)
              ·
                refine ⟨23040181252079534985311, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 983047733422060159373269 23040181252079534985311)
                ·
                  rfl

theorem cell22_605753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 3, 2, 7].length) (baseStart_605753 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_605753 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_605753 prefixEnd_605753 := by exact prefixLift 605753
  have htrace : WordTrace (prefixWord ++ tailWord_605753) baseStart_605753 baseEnd_605753 := by
    simpa [prefixWord, tailWord_605753, baseEnd_605753] using wordTrace_append hprefix tailTrace_605753
  have hstable : (prefixWord ++ tailWord_605753).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_605753).length < 2 ^ (prefixWord ++ tailWord_605753).sum := by decide
  have hdescent : baseEnd_605753 < baseStart_605753 := by decide
  rcases family_descends (prefixWord ++ tailWord_605753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_605757 : List Nat := [1, 4, 1, 3, 3, 1, 1, 3, 2, 3]
def baseStart_605757 : Nat := 118140960795 + 605757 * 2 ^ 59
def prefixEnd_605757 : Nat := 4983230072969 + 3 ^ 40 * 605757 * 2
def baseEnd_605757 : Nat := 207363000550461137767787

theorem tailTrace_605757 : CollatzResearch.WordTrace tailWord_605757 prefixEnd_605757 207363000550461137767787 := by
  unfold tailWord_605757
  simp only [CollatzResearch.WordTrace]
  refine ⟨22093772866453318904231525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14729181910968879269487683 22093772866453318904231525)
  ·
    refine ⟨4142582412459997294543411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 22093772866453318904231525 4142582412459997294543411)
    ·
      refine ⟨6213873618689995941815117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4142582412459997294543411 6213873618689995941815117)
      ·
        refine ⟨2330202607008748478180669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6213873618689995941815117 2330202607008748478180669)
        ·
          refine ⟨873825977628280679317751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2330202607008748478180669 873825977628280679317751)
          ·
            refine ⟨1310738966442421018976627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 873825977628280679317751 1310738966442421018976627)
            ·
              refine ⟨1966108449663631528464941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1310738966442421018976627 1966108449663631528464941)
              ·
                refine ⟨737290668623861823174353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1966108449663631528464941 737290668623861823174353)
                ·
                  refine ⟨552968001467896367380765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 737290668623861823174353 552968001467896367380765)
                  ·
                    refine ⟨207363000550461137767787, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 552968001467896367380765 207363000550461137767787)
                    ·
                      rfl

theorem cell22_605757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 1, 1, 3, 2, 3].length) (baseStart_605757 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_605757 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_605757 prefixEnd_605757 := by exact prefixLift 605757
  have htrace : WordTrace (prefixWord ++ tailWord_605757) baseStart_605757 baseEnd_605757 := by
    simpa [prefixWord, tailWord_605757, baseEnd_605757] using wordTrace_append hprefix tailTrace_605757
  have hstable : (prefixWord ++ tailWord_605757).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_605757).length < 2 ^ (prefixWord ++ tailWord_605757).sum := by decide
  have hdescent : baseEnd_605757 < baseStart_605757 := by decide
  rcases family_descends (prefixWord ++ tailWord_605757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_605860 : List Nat := [2, 3, 1, 2, 2, 3, 2, 1, 6]
def baseStart_605860 : Nat := 118140960795 + 605860 * 2 ^ 59
def prefixEnd_605860 : Nat := 4983230072969 + 3 ^ 40 * 605860 * 2
def baseEnd_605860 : Nat := 69132753185134400814157

theorem tailTrace_605860 : CollatzResearch.WordTrace tailWord_605860 prefixEnd_605860 69132753185134400814157 := by
  unfold tailWord_605860
  simp only [CollatzResearch.WordTrace]
  refine ⟨11048764792540083747615517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14731686390053444996820689 11048764792540083747615517)
  ·
    refine ⟨4143286797202531405355819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11048764792540083747615517 4143286797202531405355819)
    ·
      refine ⟨6214930195803797108033729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4143286797202531405355819 6214930195803797108033729)
      ·
        refine ⟨4661197646852847831025297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6214930195803797108033729 4661197646852847831025297)
        ·
          refine ⟨3495898235139635873268973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4661197646852847831025297 3495898235139635873268973)
          ·
            refine ⟨1310961838177363452475865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3495898235139635873268973 1310961838177363452475865)
            ·
              refine ⟨983221378633022589356899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1310961838177363452475865 983221378633022589356899)
              ·
                refine ⟨1474832067949533884035349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 983221378633022589356899 1474832067949533884035349)
                ·
                  refine ⟨69132753185134400814157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1474832067949533884035349 69132753185134400814157)
                  ·
                    rfl

theorem cell22_605860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 3, 2, 1, 6].length) (baseStart_605860 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_605860 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_605860 prefixEnd_605860 := by exact prefixLift 605860
  have htrace : WordTrace (prefixWord ++ tailWord_605860) baseStart_605860 baseEnd_605860 := by
    simpa [prefixWord, tailWord_605860, baseEnd_605860] using wordTrace_append hprefix tailTrace_605860
  have hstable : (prefixWord ++ tailWord_605860).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_605860).length < 2 ^ (prefixWord ++ tailWord_605860).sum := by decide
  have hdescent : baseEnd_605860 < baseStart_605860 := by decide
  rcases family_descends (prefixWord ++ tailWord_605860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_605888 : List Nat := [2, 1, 1, 2, 4, 1, 3, 8]
def baseStart_605888 : Nat := 118140960795 + 605888 * 2 ^ 59
def prefixEnd_605888 : Nat := 4983230072969 + 3 ^ 40 * 605888 * 2
def baseEnd_605888 : Nat := 23045316058624495860265

theorem tailTrace_605888 : CollatzResearch.WordTrace tailWord_605888 prefixEnd_605888 23045316058624495860265 := by
  unfold tailWord_605888
  simp only [CollatzResearch.WordTrace]
  refine ⟨11049275414489364138625159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14732367219319152184833545 11049275414489364138625159)
  ·
    refine ⟨16573913121734046207937739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11049275414489364138625159 16573913121734046207937739)
    ·
      refine ⟨24860869682601069311906609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16573913121734046207937739 24860869682601069311906609)
      ·
        refine ⟨18645652261950801983929957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24860869682601069311906609 18645652261950801983929957)
        ·
          refine ⟨3496059799115775371986867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18645652261950801983929957 3496059799115775371986867)
          ·
            refine ⟨5244089698673663057980301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3496059799115775371986867 5244089698673663057980301)
            ·
              refine ⟨1966533637002623646742613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5244089698673663057980301 1966533637002623646742613)
              ·
                refine ⟨23045316058624495860265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1966533637002623646742613 23045316058624495860265)
                ·
                  rfl

theorem cell22_605888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 3, 8].length) (baseStart_605888 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_605888 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_605888 prefixEnd_605888 := by exact prefixLift 605888
  have htrace : WordTrace (prefixWord ++ tailWord_605888) baseStart_605888 baseEnd_605888 := by
    simpa [prefixWord, tailWord_605888, baseEnd_605888] using wordTrace_append hprefix tailTrace_605888
  have hstable : (prefixWord ++ tailWord_605888).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_605888).length < 2 ^ (prefixWord ++ tailWord_605888).sum := by decide
  have hdescent : baseEnd_605888 < baseStart_605888 := by decide
  rcases family_descends (prefixWord ++ tailWord_605888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_605980 : List Nat := [2, 2, 3, 1, 1, 2, 1, 1, 5, 4]
def baseStart_605980 : Nat := 118140960795 + 605980 * 2 ^ 59
def prefixEnd_605980 : Nat := 4983230072969 + 3 ^ 40 * 605980 * 2
def baseEnd_605980 : Nat := 207439338007762889442103

theorem tailTrace_605980 : CollatzResearch.WordTrace tailWord_605980 prefixEnd_605980 207439338007762889442103 := by
  unfold tailWord_605980
  simp only [CollatzResearch.WordTrace]
  refine ⟨11050953172322713994799697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14734604229763618659732929 11050953172322713994799697)
  ·
    refine ⟨8288214879242035496099773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11050953172322713994799697 8288214879242035496099773)
    ·
      refine ⟨3108080579715763311037415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8288214879242035496099773 3108080579715763311037415)
      ·
        refine ⟨4662120869573644966556123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3108080579715763311037415 4662120869573644966556123)
        ·
          refine ⟨6993181304360467449834185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4662120869573644966556123 6993181304360467449834185)
          ·
            refine ⟨5244885978270350587375639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6993181304360467449834185 5244885978270350587375639)
            ·
              refine ⟨7867328967405525881063459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5244885978270350587375639 7867328967405525881063459)
              ·
                refine ⟨11800993451108288821595189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7867328967405525881063459 11800993451108288821595189)
                ·
                  refine ⟨1106343136041402077024549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 11800993451108288821595189 1106343136041402077024549)
                  ·
                    refine ⟨207439338007762889442103, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1106343136041402077024549 207439338007762889442103)
                    ·
                      rfl

theorem cell22_605980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 1, 1, 5, 4].length) (baseStart_605980 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_605980 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_605980 prefixEnd_605980 := by exact prefixLift 605980
  have htrace : WordTrace (prefixWord ++ tailWord_605980) baseStart_605980 baseEnd_605980 := by
    simpa [prefixWord, tailWord_605980, baseEnd_605980] using wordTrace_append hprefix tailTrace_605980
  have hstable : (prefixWord ++ tailWord_605980).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_605980).length < 2 ^ (prefixWord ++ tailWord_605980).sum := by decide
  have hdescent : baseEnd_605980 < baseStart_605980 := by decide
  rcases family_descends (prefixWord ++ tailWord_605980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_606012 : List Nat := [2, 2, 2, 2, 1, 1, 3, 5, 4]
def baseStart_606012 : Nat := 118140960795 + 606012 * 2 ^ 59
def prefixEnd_606012 : Nat := 4983230072969 + 3 ^ 40 * 606012 * 2
def baseEnd_606012 : Nat := 69150097420575157547335

theorem tailTrace_606012 : CollatzResearch.WordTrace tailWord_606012 prefixEnd_606012 69150097420575157547335 := by
  unfold tailWord_606012
  simp only [CollatzResearch.WordTrace]
  refine ⟨11051536740264748727382145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14735382320352998303176193 11051536740264748727382145)
  ·
    refine ⟨8288652555198561545536609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11051536740264748727382145 8288652555198561545536609)
    ·
      refine ⟨6216489416398921159152457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8288652555198561545536609 6216489416398921159152457)
      ·
        refine ⟨4662367062299190869364343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6216489416398921159152457 4662367062299190869364343)
        ·
          refine ⟨6993550593448786304046515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4662367062299190869364343 6993550593448786304046515)
          ·
            refine ⟨10490325890173179456069773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6993550593448786304046515 10490325890173179456069773)
            ·
              refine ⟨3933872208814942296026165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10490325890173179456069773 3933872208814942296026165)
              ·
                refine ⟨368800519576400840252453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3933872208814942296026165 368800519576400840252453)
                ·
                  refine ⟨69150097420575157547335, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 368800519576400840252453 69150097420575157547335)
                  ·
                    rfl

theorem cell22_606012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 3, 5, 4].length) (baseStart_606012 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_606012 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_606012 prefixEnd_606012 := by exact prefixLift 606012
  have htrace : WordTrace (prefixWord ++ tailWord_606012) baseStart_606012 baseEnd_606012 := by
    simpa [prefixWord, tailWord_606012, baseEnd_606012] using wordTrace_append hprefix tailTrace_606012
  have hstable : (prefixWord ++ tailWord_606012).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_606012).length < 2 ^ (prefixWord ++ tailWord_606012).sum := by decide
  have hdescent : baseEnd_606012 < baseStart_606012 := by decide
  rcases family_descends (prefixWord ++ tailWord_606012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_606014 : List Nat := [4, 2, 1, 2, 2, 2, 1, 3, 1, 4]
def baseStart_606014 : Nat := 118140960795 + 606014 * 2 ^ 59
def prefixEnd_606014 : Nat := 4983230072969 + 3 ^ 40 * 606014 * 2
def baseEnd_606014 : Nat := 207450976902598134091999

theorem tailTrace_606014 : CollatzResearch.WordTrace tailWord_606014 prefixEnd_606014 207450976902598134091999 := by
  unfold tailWord_606014
  simp only [CollatzResearch.WordTrace]
  refine ⟨2762893303315281474542137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14735430951014834530891397 2762893303315281474542137)
  ·
    refine ⟨2072169977486461105906603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2762893303315281474542137 2072169977486461105906603)
    ·
      refine ⟨3108254966229691658859905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2072169977486461105906603 3108254966229691658859905)
      ·
        refine ⟨2331191224672268744144929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3108254966229691658859905 2331191224672268744144929)
        ·
          refine ⟨1748393418504201558108697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2331191224672268744144929 1748393418504201558108697)
          ·
            refine ⟨1311295063878151168581523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1748393418504201558108697 1311295063878151168581523)
            ·
              refine ⟨1966942595817226752872285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1311295063878151168581523 1966942595817226752872285)
              ·
                refine ⟨737603473431460032327107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1966942595817226752872285 737603473431460032327107)
                ·
                  refine ⟨1106405210147190048490661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 737603473431460032327107 1106405210147190048490661)
                  ·
                    refine ⟨207450976902598134091999, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1106405210147190048490661 207450976902598134091999)
                    ·
                      rfl

theorem cell22_606014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 2, 1, 3, 1, 4].length) (baseStart_606014 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_606014 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_606014 prefixEnd_606014 := by exact prefixLift 606014
  have htrace : WordTrace (prefixWord ++ tailWord_606014) baseStart_606014 baseEnd_606014 := by
    simpa [prefixWord, tailWord_606014, baseEnd_606014] using wordTrace_append hprefix tailTrace_606014
  have hstable : (prefixWord ++ tailWord_606014).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_606014).length < 2 ^ (prefixWord ++ tailWord_606014).sum := by decide
  have hdescent : baseEnd_606014 < baseStart_606014 := by decide
  rcases family_descends (prefixWord ++ tailWord_606014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_606025 : List Nat := [1, 2, 1, 1, 2, 4, 2, 1, 4, 4]
def baseStart_606025 : Nat := 118140960795 + 606025 * 2 ^ 59
def prefixEnd_606025 : Nat := 4983230072969 + 3 ^ 40 * 606025 * 2
def baseEnd_606025 : Nat := 207454742427397772066965

theorem tailTrace_606025 : CollatzResearch.WordTrace tailWord_606025 prefixEnd_606025 207454742427397772066965 := by
  unfold tailWord_606025
  simp only [CollatzResearch.WordTrace]
  refine ⟨22103547629482400674987529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14735698419654933783325019 22103547629482400674987529)
  ·
    refine ⟨16577660722111800506240647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22103547629482400674987529 16577660722111800506240647)
    ·
      refine ⟨24866491083167700759360971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16577660722111800506240647 24866491083167700759360971)
      ·
        refine ⟨37299736624751551139041457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24866491083167700759360971 37299736624751551139041457)
        ·
          refine ⟨27974802468563663354281093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37299736624751551139041457 27974802468563663354281093)
          ·
            refine ⟨5245275462855686878927705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 27974802468563663354281093 5245275462855686878927705)
            ·
              refine ⟨3933956597141765159195779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5245275462855686878927705 3933956597141765159195779)
              ·
                refine ⟨5900934895712647738793669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3933956597141765159195779 5900934895712647738793669)
                ·
                  refine ⟨1106425292946121451023813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5900934895712647738793669 1106425292946121451023813)
                  ·
                    refine ⟨207454742427397772066965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1106425292946121451023813 207454742427397772066965)
                    ·
                      rfl

theorem cell22_606025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 2, 1, 4, 4].length) (baseStart_606025 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_606025 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_606025 prefixEnd_606025 := by exact prefixLift 606025
  have htrace : WordTrace (prefixWord ++ tailWord_606025) baseStart_606025 baseEnd_606025 := by
    simpa [prefixWord, tailWord_606025, baseEnd_606025] using wordTrace_append hprefix tailTrace_606025
  have hstable : (prefixWord ++ tailWord_606025).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_606025).length < 2 ^ (prefixWord ++ tailWord_606025).sum := by decide
  have hdescent : baseEnd_606025 < baseStart_606025 := by decide
  rcases family_descends (prefixWord ++ tailWord_606025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_606029 : List Nat := [1, 6, 1, 2, 1, 2, 2, 1, 6]
def baseStart_606029 : Nat := 118140960795 + 606029 * 2 ^ 59
def prefixEnd_606029 : Nat := 4983230072969 + 3 ^ 40 * 606029 * 2
def baseEnd_606029 : Nat := 69152037236381031655651

theorem tailTrace_606029 : CollatzResearch.WordTrace tailWord_606029 prefixEnd_606029 69152037236381031655651 := by
  unfold tailWord_606029
  simp only [CollatzResearch.WordTrace]
  refine ⟨22103693521467909358133141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14735795680978606238755427 22103693521467909358133141)
  ·
    refine ⟨1036110633818808251162491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 22103693521467909358133141 1036110633818808251162491)
    ·
      refine ⟨1554165950728212376743737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1036110633818808251162491 1554165950728212376743737)
      ·
        refine ⟨1165624463046159282557803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1554165950728212376743737 1165624463046159282557803)
        ·
          refine ⟨1748436694569238923836705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1165624463046159282557803 1748436694569238923836705)
          ·
            refine ⟨1311327520926929192877529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1748436694569238923836705 1311327520926929192877529)
            ·
              refine ⟨983495640695196894658147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1311327520926929192877529 983495640695196894658147)
              ·
                refine ⟨1475243461042795341987221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 983495640695196894658147 1475243461042795341987221)
                ·
                  refine ⟨69152037236381031655651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1475243461042795341987221 69152037236381031655651)
                  ·
                    rfl

theorem cell22_606029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 2, 2, 1, 6].length) (baseStart_606029 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_606029 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_606029 prefixEnd_606029 := by exact prefixLift 606029
  have htrace : WordTrace (prefixWord ++ tailWord_606029) baseStart_606029 baseEnd_606029 := by
    simpa [prefixWord, tailWord_606029, baseEnd_606029] using wordTrace_append hprefix tailTrace_606029
  have hstable : (prefixWord ++ tailWord_606029).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_606029).length < 2 ^ (prefixWord ++ tailWord_606029).sum := by decide
  have hdescent : baseEnd_606029 < baseStart_606029 := by decide
  rcases family_descends (prefixWord ++ tailWord_606029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_606055 : List Nat := [1, 1, 5, 1, 2, 1, 1, 1, 2, 7]
def baseStart_606055 : Nat := 118140960795 + 606055 * 2 ^ 59
def prefixEnd_606055 : Nat := 4983230072969 + 3 ^ 40 * 606055 * 2
def baseEnd_606055 : Nat := 207465012040487693816873

theorem tailTrace_606055 : CollatzResearch.WordTrace tailWord_606055 prefixEnd_606055 207465012040487693816873 := by
  unfold tailWord_606055
  simp only [CollatzResearch.WordTrace]
  refine ⟨22104641819373715798579619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14736427879582477199053079 22104641819373715798579619)
  ·
    refine ⟨33156962729060573697869429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22104641819373715798579619 33156962729060573697869429)
    ·
      refine ⟨3108465255849428784175259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 33156962729060573697869429 3108465255849428784175259)
      ·
        refine ⟨4662697883774143176262889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3108465255849428784175259 4662697883774143176262889)
        ·
          refine ⟨3497023412830607382197167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4662697883774143176262889 3497023412830607382197167)
          ·
            refine ⟨5245535119245911073295751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3497023412830607382197167 5245535119245911073295751)
            ·
              refine ⟨7868302678868866609943627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5245535119245911073295751 7868302678868866609943627)
              ·
                refine ⟨11802454018303299914915441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7868302678868866609943627 11802454018303299914915441)
                ·
                  refine ⟨8851840513727474936186581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11802454018303299914915441 8851840513727474936186581)
                  ·
                    refine ⟨207465012040487693816873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 8851840513727474936186581 207465012040487693816873)
                    ·
                      rfl

theorem cell22_606055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 1, 1, 2, 7].length) (baseStart_606055 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_606055 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_606055 prefixEnd_606055 := by exact prefixLift 606055
  have htrace : WordTrace (prefixWord ++ tailWord_606055) baseStart_606055 baseEnd_606055 := by
    simpa [prefixWord, tailWord_606055, baseEnd_606055] using wordTrace_append hprefix tailTrace_606055
  have hstable : (prefixWord ++ tailWord_606055).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_606055).length < 2 ^ (prefixWord ++ tailWord_606055).sum := by decide
  have hdescent : baseEnd_606055 < baseStart_606055 := by decide
  rcases family_descends (prefixWord ++ tailWord_606055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_606085 : List Nat := [1, 3, 1, 1, 3, 2, 1, 3, 7]
def baseStart_606085 : Nat := 118140960795 + 606085 * 2 ^ 59
def prefixEnd_606085 : Nat := 4983230072969 + 3 ^ 40 * 606085 * 2
def baseEnd_606085 : Nat := 69158427217859205188927

theorem tailTrace_606085 : CollatzResearch.WordTrace tailWord_606085 prefixEnd_606085 69158427217859205188927 := by
  unfold tailWord_606085
  simp only [CollatzResearch.WordTrace]
  refine ⟨22105736009265030922171709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14737157339510020614781139 22105736009265030922171709)
  ·
    refine ⟨8289651003474386595814391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22105736009265030922171709 8289651003474386595814391)
    ·
      refine ⟨12434476505211579893721587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8289651003474386595814391 12434476505211579893721587)
      ·
        refine ⟨18651714757817369840582381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12434476505211579893721587 18651714757817369840582381)
        ·
          refine ⟨6994393034181513690218393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18651714757817369840582381 6994393034181513690218393)
          ·
            refine ⟨5245794775636135267663795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6994393034181513690218393 5245794775636135267663795)
            ·
              refine ⟨7868692163454202901495693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5245794775636135267663795 7868692163454202901495693)
              ·
                refine ⟨2950759561295326088060885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7868692163454202901495693 2950759561295326088060885)
                ·
                  refine ⟨69158427217859205188927, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2950759561295326088060885 69158427217859205188927)
                  ·
                    rfl

theorem cell22_606085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 1, 3, 7].length) (baseStart_606085 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_606085 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_606085 prefixEnd_606085 := by exact prefixLift 606085
  have htrace : WordTrace (prefixWord ++ tailWord_606085) baseStart_606085 baseEnd_606085 := by
    simpa [prefixWord, tailWord_606085, baseEnd_606085] using wordTrace_append hprefix tailTrace_606085
  have hstable : (prefixWord ++ tailWord_606085).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_606085).length < 2 ^ (prefixWord ++ tailWord_606085).sum := by decide
  have hdescent : baseEnd_606085 < baseStart_606085 := by decide
  rcases family_descends (prefixWord ++ tailWord_606085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_606183 : List Nat := [1, 1, 5, 2, 3, 2, 2, 1, 1, 4]
def baseStart_606183 : Nat := 118140960795 + 606183 * 2 ^ 59
def prefixEnd_606183 : Nat := 4983230072969 + 3 ^ 40 * 606183 * 2
def baseEnd_606183 : Nat := 207508829056338026616481

theorem tailTrace_606183 : CollatzResearch.WordTrace tailWord_606183 prefixEnd_606183 207508829056338026616481 := by
  unfold tailWord_606183
  simp only [CollatzResearch.WordTrace]
  refine ⟨22109310362909993659239203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14739540241939995772826135 22109310362909993659239203)
  ·
    refine ⟨33163965544364990488858805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22109310362909993659239203 33163965544364990488858805)
    ·
      refine ⟨3109121769784217858330513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 33163965544364990488858805 3109121769784217858330513)
      ·
        refine ⟨2331841327338163393747885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3109121769784217858330513 2331841327338163393747885)
        ·
          refine ⟨874440497751811272655457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2331841327338163393747885 874440497751811272655457)
          ·
            refine ⟨655830373313858454491593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 874440497751811272655457 655830373313858454491593)
            ·
              refine ⟨491872779985393840868695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 655830373313858454491593 491872779985393840868695)
              ·
                refine ⟨737809169978090761303043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 491872779985393840868695 737809169978090761303043)
                ·
                  refine ⟨1106713754967136141954565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 737809169978090761303043 1106713754967136141954565)
                  ·
                    refine ⟨207508829056338026616481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1106713754967136141954565 207508829056338026616481)
                    ·
                      rfl

theorem cell22_606183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 2, 2, 1, 1, 4].length) (baseStart_606183 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_606183 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_606183 prefixEnd_606183 := by exact prefixLift 606183
  have htrace : WordTrace (prefixWord ++ tailWord_606183) baseStart_606183 baseEnd_606183 := by
    simpa [prefixWord, tailWord_606183, baseEnd_606183] using wordTrace_append hprefix tailTrace_606183
  have hstable : (prefixWord ++ tailWord_606183).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_606183).length < 2 ^ (prefixWord ++ tailWord_606183).sum := by decide
  have hdescent : baseEnd_606183 < baseStart_606183 := by decide
  rcases family_descends (prefixWord ++ tailWord_606183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_606252 : List Nat := [2, 2, 1, 1, 1, 2, 2, 4, 2, 5]
def baseStart_606252 : Nat := 118140960795 + 606252 * 2 ^ 59
def prefixEnd_606252 : Nat := 4983230072969 + 3 ^ 40 * 606252 * 2
def baseEnd_606252 : Nat := 207532449166444846641269

theorem tailTrace_606252 : CollatzResearch.WordTrace tailWord_606252 prefixEnd_606252 207532449166444846641269 := by
  unfold tailWord_606252
  simp only [CollatzResearch.WordTrace]
  refine ⟨11055913499830009221750505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14741217999773345629000673 11055913499830009221750505)
  ·
    refine ⟨8291935124872506916312879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11055913499830009221750505 8291935124872506916312879)
    ·
      refine ⟨12437902687308760374469319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8291935124872506916312879 12437902687308760374469319)
      ·
        refine ⟨18656854030963140561703979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12437902687308760374469319 18656854030963140561703979)
        ·
          refine ⟨27985281046444710842555969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18656854030963140561703979 27985281046444710842555969)
          ·
            refine ⟨20988960784833533131916977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27985281046444710842555969 20988960784833533131916977)
            ·
              refine ⟨15741720588625149848937733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20988960784833533131916977 15741720588625149848937733)
              ·
                refine ⟨2951572610367215596675825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15741720588625149848937733 2951572610367215596675825)
                ·
                  refine ⟨2213679457775411697506869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2951572610367215596675825 2213679457775411697506869)
                  ·
                    refine ⟨207532449166444846641269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2213679457775411697506869 207532449166444846641269)
                    ·
                      rfl

theorem cell22_606252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 5].length) (baseStart_606252 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_606252 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_606252 prefixEnd_606252 := by exact prefixLift 606252
  have htrace : WordTrace (prefixWord ++ tailWord_606252) baseStart_606252 baseEnd_606252 := by
    simpa [prefixWord, tailWord_606252, baseEnd_606252] using wordTrace_append hprefix tailTrace_606252
  have hstable : (prefixWord ++ tailWord_606252).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_606252).length < 2 ^ (prefixWord ++ tailWord_606252).sum := by decide
  have hdescent : baseEnd_606252 < baseStart_606252 := by decide
  rcases family_descends (prefixWord ++ tailWord_606252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_606254 : List Nat := [4, 1, 3, 1, 1, 2, 2, 1, 7]
def baseStart_606254 : Nat := 118140960795 + 606254 * 2 ^ 59
def prefixEnd_606254 : Nat := 4983230072969 + 3 ^ 40 * 606254 * 2
def baseEnd_606254 : Nat := 69177711269105836030421

theorem tailTrace_606254 : CollatzResearch.WordTrace tailWord_606254 prefixEnd_606254 69177711269105836030421 := by
  unfold tailWord_606254
  simp only [CollatzResearch.WordTrace]
  refine ⟨2763987493206596598134227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14741266630435181856715877 2763987493206596598134227)
  ·
    refine ⟨4145981239809894897201341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2763987493206596598134227 4145981239809894897201341)
    ·
      refine ⟨1554742964928710586450503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4145981239809894897201341 1554742964928710586450503)
      ·
        refine ⟨2332114447393065879675755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1554742964928710586450503 2332114447393065879675755)
        ·
          refine ⟨3498171671089598819513633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2332114447393065879675755 3498171671089598819513633)
          ·
            refine ⟨2623628753317199114635225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3498171671089598819513633 2623628753317199114635225)
            ·
              refine ⟨1967721564987899335976419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2623628753317199114635225 1967721564987899335976419)
              ·
                refine ⟨2951582347481849003964629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1967721564987899335976419 2951582347481849003964629)
                ·
                  refine ⟨69177711269105836030421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2951582347481849003964629 69177711269105836030421)
                  ·
                    rfl

theorem cell22_606254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 2, 1, 7].length) (baseStart_606254 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_606254 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_606254 prefixEnd_606254 := by exact prefixLift 606254
  have htrace : WordTrace (prefixWord ++ tailWord_606254) baseStart_606254 baseEnd_606254 := by
    simpa [prefixWord, tailWord_606254, baseEnd_606254] using wordTrace_append hprefix tailTrace_606254
  have hstable : (prefixWord ++ tailWord_606254).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_606254).length < 2 ^ (prefixWord ++ tailWord_606254).sum := by decide
  have hdescent : baseEnd_606254 < baseStart_606254 := by decide
  rcases family_descends (prefixWord ++ tailWord_606254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_606267 : List Nat := [1, 1, 1, 1, 1, 2, 1, 5, 5, 4]
def baseStart_606267 : Nat := 118140960795 + 606267 * 2 ^ 59
def prefixEnd_606267 : Nat := 4983230072969 + 3 ^ 40 * 606267 * 2
def baseEnd_606267 : Nat := 207537583972989807516223

theorem tailTrace_606267 : CollatzResearch.WordTrace tailWord_606267 prefixEnd_606267 207537583972989807516223 := by
  unfold tailWord_606267
  simp only [CollatzResearch.WordTrace]
  refine ⟨22112374094605676005297055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14741582729737117336864703 22112374094605676005297055)
  ·
    refine ⟨33168561141908514007945583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22112374094605676005297055 33168561141908514007945583)
    ·
      refine ⟨49752841712862771011918375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33168561141908514007945583 49752841712862771011918375)
      ·
        refine ⟨74629262569294156517877563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49752841712862771011918375 74629262569294156517877563)
        ·
          refine ⟨111943893853941234776816345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74629262569294156517877563 111943893853941234776816345)
          ·
            refine ⟨83957920390455926082612259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 111943893853941234776816345 83957920390455926082612259)
            ·
              refine ⟨125936880585683889123918389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 83957920390455926082612259 125936880585683889123918389)
              ·
                refine ⟨11806582554907864605367349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 125936880585683889123918389 11806582554907864605367349)
                ·
                  refine ⟨1106867114522612306753189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 11806582554907864605367349 1106867114522612306753189)
                  ·
                    refine ⟨207537583972989807516223, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1106867114522612306753189 207537583972989807516223)
                    ·
                      rfl

theorem cell22_606267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 5, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 5, 5, 4].length) (baseStart_606267 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_606267 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_606267 prefixEnd_606267 := by exact prefixLift 606267
  have htrace : WordTrace (prefixWord ++ tailWord_606267) baseStart_606267 baseEnd_606267 := by
    simpa [prefixWord, tailWord_606267, baseEnd_606267] using wordTrace_append hprefix tailTrace_606267
  have hstable : (prefixWord ++ tailWord_606267).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_606267).length < 2 ^ (prefixWord ++ tailWord_606267).sum := by decide
  have hdescent : baseEnd_606267 < baseStart_606267 := by decide
  rcases family_descends (prefixWord ++ tailWord_606267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_606282 : List Nat := [3, 1, 2, 1, 1, 2, 1, 3, 8]
def baseStart_606282 : Nat := 118140960795 + 606282 * 2 ^ 59
def prefixEnd_606282 : Nat := 4983230072969 + 3 ^ 40 * 606282 * 2
def baseEnd_606282 : Nat := 69180906259844922797059

theorem tailTrace_606282 : CollatzResearch.WordTrace tailWord_606282 prefixEnd_606282 69180906259844922797059 := by
  unfold tailWord_606282
  simp only [CollatzResearch.WordTrace]
  refine ⟨5528230297387833391773275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14741947459700889044728733 5528230297387833391773275)
  ·
    refine ⟨8292345446081750087659913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5528230297387833391773275 8292345446081750087659913)
    ·
      refine ⟨6219259084561312565744935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8292345446081750087659913 6219259084561312565744935)
      ·
        refine ⟨9328888626841968848617403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6219259084561312565744935 9328888626841968848617403)
        ·
          refine ⟨13993332940262953272926105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9328888626841968848617403 13993332940262953272926105)
          ·
            refine ⟨10494999705197214954694579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13993332940262953272926105 10494999705197214954694579)
            ·
              refine ⟨15742499557795822432041869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10494999705197214954694579 15742499557795822432041869)
              ·
                refine ⟨5903437334173433412015701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15742499557795822432041869 5903437334173433412015701)
                ·
                  refine ⟨69180906259844922797059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 5903437334173433412015701 69180906259844922797059)
                  ·
                    rfl

theorem cell22_606282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 3, 8].length) (baseStart_606282 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_606282 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_606282 prefixEnd_606282 := by exact prefixLift 606282
  have htrace : WordTrace (prefixWord ++ tailWord_606282) baseStart_606282 baseEnd_606282 := by
    simpa [prefixWord, tailWord_606282, baseEnd_606282] using wordTrace_append hprefix tailTrace_606282
  have hstable : (prefixWord ++ tailWord_606282).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_606282).length < 2 ^ (prefixWord ++ tailWord_606282).sum := by decide
  have hdescent : baseEnd_606282 < baseStart_606282 := by decide
  rcases family_descends (prefixWord ++ tailWord_606282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_606316 : List Nat := [2, 2, 1, 1, 3, 4, 1, 4, 4]
def baseStart_606316 : Nat := 118140960795 + 606316 * 2 ^ 59
def prefixEnd_606316 : Nat := 4983230072969 + 3 ^ 40 * 606316 * 2
def baseEnd_606316 : Nat := 69184785891456671013691

theorem tailTrace_606316 : CollatzResearch.WordTrace tailWord_606316 prefixEnd_606316 69184785891456671013691 := by
  unfold tailWord_606316
  simp only [CollatzResearch.WordTrace]
  refine ⟨11057080635714078686915401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14742774180952104915887201 11057080635714078686915401)
  ·
    refine ⟨8292810476785559015186551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11057080635714078686915401 8292810476785559015186551)
    ·
      refine ⟨12439215715178338522779827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8292810476785559015186551 12439215715178338522779827)
      ·
        refine ⟨18658823572767507784169741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12439215715178338522779827 18658823572767507784169741)
        ·
          refine ⟨6997058839787815419063653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18658823572767507784169741 6997058839787815419063653)
          ·
            refine ⟨1311948532460215391074435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6997058839787815419063653 1311948532460215391074435)
            ·
              refine ⟨1967922798690323086611653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1311948532460215391074435 1967922798690323086611653)
              ·
                refine ⟨368985524754435578739685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1967922798690323086611653 368985524754435578739685)
                ·
                  refine ⟨69184785891456671013691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 368985524754435578739685 69184785891456671013691)
                  ·
                    rfl

theorem cell22_606316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 4, 1, 4, 4].length) (baseStart_606316 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_606316 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_606316 prefixEnd_606316 := by exact prefixLift 606316
  have htrace : WordTrace (prefixWord ++ tailWord_606316) baseStart_606316 baseEnd_606316 := by
    simpa [prefixWord, tailWord_606316, baseEnd_606316] using wordTrace_append hprefix tailTrace_606316
  have hstable : (prefixWord ++ tailWord_606316).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_606316).length < 2 ^ (prefixWord ++ tailWord_606316).sum := by decide
  have hdescent : baseEnd_606316 < baseStart_606316 := by decide
  rcases family_descends (prefixWord ++ tailWord_606316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_606346 : List Nat := [3, 1, 2, 3, 1, 2, 3, 1, 2, 4]
def baseStart_606346 : Nat := 118140960795 + 606346 * 2 ^ 59
def prefixEnd_606346 : Nat := 4983230072969 + 3 ^ 40 * 606346 * 2
def baseEnd_606346 : Nat := 207564627287459934790981

theorem tailTrace_606346 : CollatzResearch.WordTrace tailWord_606346 prefixEnd_606346 207564627287459934790981 := by
  unfold tailWord_606346
  simp only [CollatzResearch.WordTrace]
  refine ⟨5528813865329868124355723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14743503640879648331615261 5528813865329868124355723)
  ·
    refine ⟨8293220797994802186533585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5528813865329868124355723 8293220797994802186533585)
    ·
      refine ⟨6219915598496101639900189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8293220797994802186533585 6219915598496101639900189)
      ·
        refine ⟨2332468349436038114962571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6219915598496101639900189 2332468349436038114962571)
        ·
          refine ⟨3498702524154057172443857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2332468349436038114962571 3498702524154057172443857)
          ·
            refine ⟨2624026893115542879332893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3498702524154057172443857 2624026893115542879332893)
            ·
              refine ⟨984010084918328579749835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2624026893115542879332893 984010084918328579749835)
              ·
                refine ⟨1476015127377492869624753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 984010084918328579749835 1476015127377492869624753)
                ·
                  refine ⟨1107011345533119652218565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1476015127377492869624753 1107011345533119652218565)
                  ·
                    refine ⟨207564627287459934790981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1107011345533119652218565 207564627287459934790981)
                    ·
                      rfl

theorem cell22_606346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 3, 1, 2, 4].length) (baseStart_606346 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_606346 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_606346 prefixEnd_606346 := by exact prefixLift 606346
  have htrace : WordTrace (prefixWord ++ tailWord_606346) baseStart_606346 baseEnd_606346 := by
    simpa [prefixWord, tailWord_606346, baseEnd_606346] using wordTrace_append hprefix tailTrace_606346
  have hstable : (prefixWord ++ tailWord_606346).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_606346).length < 2 ^ (prefixWord ++ tailWord_606346).sum := by decide
  have hdescent : baseEnd_606346 < baseStart_606346 := by decide
  rcases family_descends (prefixWord ++ tailWord_606346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_606382 : List Nat := [4, 1, 4, 2, 2, 1, 1, 1, 1, 5]
def baseStart_606382 : Nat := 118140960795 + 606382 * 2 ^ 59
def prefixEnd_606382 : Nat := 4983230072969 + 3 ^ 40 * 606382 * 2
def baseEnd_606382 : Nat := 207576950823167840890871

theorem tailTrace_606382 : CollatzResearch.WordTrace tailWord_606382 prefixEnd_606382 207576950823167840890871 := by
  unfold tailWord_606382
  simp only [CollatzResearch.WordTrace]
  refine ⟨2764571061148631330716675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14744378992792700430488933 2764571061148631330716675)
  ·
    refine ⟨4146856591722946996075013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2764571061148631330716675 4146856591722946996075013)
    ·
      refine ⟨777535610948052561764065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4146856591722946996075013 777535610948052561764065)
      ·
        refine ⟨583151708211039421323049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 777535610948052561764065 583151708211039421323049)
        ·
          refine ⟨437363781158279565992287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 583151708211039421323049 437363781158279565992287)
          ·
            refine ⟨656045671737419348988431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 437363781158279565992287 656045671737419348988431)
            ·
              refine ⟨984068507606129023482647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 656045671737419348988431 984068507606129023482647)
              ·
                refine ⟨1476102761409193535223971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 984068507606129023482647 1476102761409193535223971)
                ·
                  refine ⟨2214154142113790302835957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1476102761409193535223971 2214154142113790302835957)
                  ·
                    refine ⟨207576950823167840890871, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2214154142113790302835957 207576950823167840890871)
                    ·
                      rfl

theorem cell22_606382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 2, 1, 1, 1, 1, 5].length) (baseStart_606382 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_606382 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_606382 prefixEnd_606382 := by exact prefixLift 606382
  have htrace : WordTrace (prefixWord ++ tailWord_606382) baseStart_606382 baseEnd_606382 := by
    simpa [prefixWord, tailWord_606382, baseEnd_606382] using wordTrace_append hprefix tailTrace_606382
  have hstable : (prefixWord ++ tailWord_606382).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_606382).length < 2 ^ (prefixWord ++ tailWord_606382).sum := by decide
  have hdescent : baseEnd_606382 < baseStart_606382 := by decide
  rcases family_descends (prefixWord ++ tailWord_606382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_606464 : List Nat := [2, 1, 1, 2, 1, 1, 4, 3, 1, 6]
def baseStart_606464 : Nat := 118140960795 + 606464 * 2 ^ 59
def prefixEnd_606464 : Nat := 4983230072969 + 3 ^ 40 * 606464 * 2
def baseEnd_606464 : Nat := 207605021098946960340619

theorem tailTrace_606464 : CollatzResearch.WordTrace tailWord_606464 prefixEnd_606464 207605021098946960340619 := by
  unfold tailWord_606464
  simp only [CollatzResearch.WordTrace]
  refine ⟨11059779637445989325109223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14746372849927985766812297 11059779637445989325109223)
  ·
    refine ⟨16589669456168983987663835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11059779637445989325109223 16589669456168983987663835)
    ·
      refine ⟨24884504184253475981495753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16589669456168983987663835 24884504184253475981495753)
      ·
        refine ⟨18663378138190106986121815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24884504184253475981495753 18663378138190106986121815)
        ·
          refine ⟨27995067207285160479182723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18663378138190106986121815 27995067207285160479182723)
          ·
            refine ⟨41992600810927740718774085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27995067207285160479182723 41992600810927740718774085)
            ·
              refine ⟨7873612652048951384770141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 41992600810927740718774085 7873612652048951384770141)
              ·
                refine ⟨2952604744518356769288803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7873612652048951384770141 2952604744518356769288803)
                ·
                  refine ⟨4428907116777535153933205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2952604744518356769288803 4428907116777535153933205)
                  ·
                    refine ⟨207605021098946960340619, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4428907116777535153933205 207605021098946960340619)
                    ·
                      rfl

theorem cell22_606464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 3, 1, 6].length) (baseStart_606464 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_606464 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_606464 prefixEnd_606464 := by exact prefixLift 606464
  have htrace : WordTrace (prefixWord ++ tailWord_606464) baseStart_606464 baseEnd_606464 := by
    simpa [prefixWord, tailWord_606464, baseEnd_606464] using wordTrace_append hprefix tailTrace_606464
  have hstable : (prefixWord ++ tailWord_606464).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_606464).length < 2 ^ (prefixWord ++ tailWord_606464).sum := by decide
  have hdescent : baseEnd_606464 < baseStart_606464 := by decide
  rcases family_descends (prefixWord ++ tailWord_606464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_606481 : List Nat := [1, 2, 2, 1, 1, 5, 2, 2, 2, 4]
def baseStart_606481 : Nat := 118140960795 + 606481 * 2 ^ 59
def prefixEnd_606481 : Nat := 4983230072969 + 3 ^ 40 * 606481 * 2
def baseEnd_606481 : Nat := 207610840546364582665567

theorem tailTrace_606481 : CollatzResearch.WordTrace tailWord_606481 prefixEnd_606481 207610840546364582665567 := by
  unfold tailWord_606481
  simp only [CollatzResearch.WordTrace]
  refine ⟨22120179315830390553587297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14746786210553593702391531 22120179315830390553587297)
  ·
    refine ⟨16590134486872792915190473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22120179315830390553587297 16590134486872792915190473)
    ·
      refine ⟨12442600865154594686392855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16590134486872792915190473 12442600865154594686392855)
      ·
        refine ⟨18663901297731892029589283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12442600865154594686392855 18663901297731892029589283)
        ·
          refine ⟨27995851946597838044383925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18663901297731892029589283 27995851946597838044383925)
          ·
            refine ⟨2624611119993547316660993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 27995851946597838044383925 2624611119993547316660993)
            ·
              refine ⟨1968458339995160487495745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2624611119993547316660993 1968458339995160487495745)
              ·
                refine ⟨1476343754996370365621809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1968458339995160487495745 1476343754996370365621809)
                ·
                  refine ⟨1107257816247277774216357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1476343754996370365621809 1107257816247277774216357)
                  ·
                    refine ⟨207610840546364582665567, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1107257816247277774216357 207610840546364582665567)
                    ·
                      rfl

theorem cell22_606481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 4].length) (baseStart_606481 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_606481 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_606481 prefixEnd_606481 := by exact prefixLift 606481
  have htrace : WordTrace (prefixWord ++ tailWord_606481) baseStart_606481 baseEnd_606481 := by
    simpa [prefixWord, tailWord_606481, baseEnd_606481] using wordTrace_append hprefix tailTrace_606481
  have hstable : (prefixWord ++ tailWord_606481).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_606481).length < 2 ^ (prefixWord ++ tailWord_606481).sum := by decide
  have hdescent : baseEnd_606481 < baseStart_606481 := by decide
  rcases family_descends (prefixWord ++ tailWord_606481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_606496 : List Nat := [2, 1, 1, 5, 2, 1, 3, 7]
def baseStart_606496 : Nat := 118140960795 + 606496 * 2 ^ 59
def prefixEnd_606496 : Nat := 4983230072969 + 3 ^ 40 * 606496 * 2
def baseEnd_606496 : Nat := 23068441705878838171169

theorem tailTrace_606496 : CollatzResearch.WordTrace tailWord_606496 prefixEnd_606496 23068441705878838171169 := by
  unfold tailWord_606496
  simp only [CollatzResearch.WordTrace]
  refine ⟨11060363205388024057691671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14747150940517365410255561 11060363205388024057691671)
  ·
    refine ⟨16590544808082036086537507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11060363205388024057691671 16590544808082036086537507)
    ·
      refine ⟨24885817212123054129806261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16590544808082036086537507 24885817212123054129806261)
      ·
        refine ⟨2333045363636536324669337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 24885817212123054129806261 2333045363636536324669337)
        ·
          refine ⟨1749784022727402243502003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2333045363636536324669337 1749784022727402243502003)
          ·
            refine ⟨2624676034091103365253005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1749784022727402243502003 2624676034091103365253005)
            ·
              refine ⟨984253512784163761969877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2624676034091103365253005 984253512784163761969877)
              ·
                refine ⟨23068441705878838171169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 984253512784163761969877 23068441705878838171169)
                ·
                  rfl

theorem cell22_606496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 3, 7].length) (baseStart_606496 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_606496 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_606496 prefixEnd_606496 := by exact prefixLift 606496
  have htrace : WordTrace (prefixWord ++ tailWord_606496) baseStart_606496 baseEnd_606496 := by
    simpa [prefixWord, tailWord_606496, baseEnd_606496] using wordTrace_append hprefix tailTrace_606496
  have hstable : (prefixWord ++ tailWord_606496).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_606496).length < 2 ^ (prefixWord ++ tailWord_606496).sum := by decide
  have hdescent : baseEnd_606496 < baseStart_606496 := by decide
  rcases family_descends (prefixWord ++ tailWord_606496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_606511 : List Nat := [1, 1, 2, 1, 2, 1, 5, 1, 5, 3]
def baseStart_606511 : Nat := 118140960795 + 606511 * 2 ^ 59
def prefixEnd_606511 : Nat := 4983230072969 + 3 ^ 40 * 606511 * 2
def baseEnd_606511 : Nat := 207621110159454504415475

theorem tailTrace_606511 : CollatzResearch.WordTrace tailWord_606511 prefixEnd_606511 207621110159454504415475 := by
  unfold tailWord_606511
  simp only [CollatzResearch.WordTrace]
  refine ⟨22121273505721705677179387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14747515670481137118119591 22121273505721705677179387)
  ·
    refine ⟨33181910258582558515769081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22121273505721705677179387 33181910258582558515769081)
    ·
      refine ⟨24886432693936918886826811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33181910258582558515769081 24886432693936918886826811)
      ·
        refine ⟨37329649040905378330240217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24886432693936918886826811 37329649040905378330240217)
        ·
          refine ⟨27997236780679033747680163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37329649040905378330240217 27997236780679033747680163)
          ·
            refine ⟨41995855171018550621520245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27997236780679033747680163 41995855171018550621520245)
            ·
              refine ⟨3937111422282989120767523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 41995855171018550621520245 3937111422282989120767523)
              ·
                refine ⟨5905667133424483681151285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3937111422282989120767523 5905667133424483681151285)
                ·
                  refine ⟨553656293758545345107933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5905667133424483681151285 553656293758545345107933)
                  ·
                    refine ⟨207621110159454504415475, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 553656293758545345107933 207621110159454504415475)
                    ·
                      rfl

theorem cell22_606511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 5, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 5, 1, 5, 3].length) (baseStart_606511 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_606511 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_606511 prefixEnd_606511 := by exact prefixLift 606511
  have htrace : WordTrace (prefixWord ++ tailWord_606511) baseStart_606511 baseEnd_606511 := by
    simpa [prefixWord, tailWord_606511, baseEnd_606511] using wordTrace_append hprefix tailTrace_606511
  have hstable : (prefixWord ++ tailWord_606511).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_606511).length < 2 ^ (prefixWord ++ tailWord_606511).sum := by decide
  have hdescent : baseEnd_606511 < baseStart_606511 := by decide
  rcases family_descends (prefixWord ++ tailWord_606511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_606513 : List Nat := [1, 2, 2, 3, 4, 1, 3, 6]
def baseStart_606513 : Nat := 118140960795 + 606513 * 2 ^ 59
def prefixEnd_606513 : Nat := 4983230072969 + 3 ^ 40 * 606513 * 2
def baseEnd_606513 : Nat := 23069088311147462873941

theorem tailTrace_606513 : CollatzResearch.WordTrace tailWord_606513 prefixEnd_606513 23069088311147462873941 := by
  unfold tailWord_606513
  simp only [CollatzResearch.WordTrace]
  refine ⟨22121346451714460018752193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14747564301142973345834795 22121346451714460018752193)
  ·
    refine ⟨16591009838785845014064145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22121346451714460018752193 16591009838785845014064145)
    ·
      refine ⟨12443257379089383760548109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16591009838785845014064145 12443257379089383760548109)
      ·
        refine ⟨4666221517158518910205541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12443257379089383760548109 4666221517158518910205541)
        ·
          refine ⟨874916534467222295663539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4666221517158518910205541 874916534467222295663539)
          ·
            refine ⟨1312374801700833443495309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 874916534467222295663539 1312374801700833443495309)
            ·
              refine ⟨492140550637812541310741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1312374801700833443495309 492140550637812541310741)
              ·
                refine ⟨23069088311147462873941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 492140550637812541310741 23069088311147462873941)
                ·
                  rfl

theorem cell22_606513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 1, 3, 6].length) (baseStart_606513 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_606513 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_606513 prefixEnd_606513 := by exact prefixLift 606513
  have htrace : WordTrace (prefixWord ++ tailWord_606513) baseStart_606513 baseEnd_606513 := by
    simpa [prefixWord, tailWord_606513, baseEnd_606513] using wordTrace_append hprefix tailTrace_606513
  have hstable : (prefixWord ++ tailWord_606513).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_606513).length < 2 ^ (prefixWord ++ tailWord_606513).sum := by decide
  have hdescent : baseEnd_606513 < baseStart_606513 := by decide
  rcases family_descends (prefixWord ++ tailWord_606513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_606545 : List Nat := [1, 2, 2, 1, 4, 2, 2, 4, 1, 3]
def baseStart_606545 : Nat := 118140960795 + 606545 * 2 ^ 59
def prefixEnd_606545 : Nat := 4983230072969 + 3 ^ 40 * 606545 * 2
def baseEnd_606545 : Nat := 207632749054289749065371

theorem tailTrace_606545 : CollatzResearch.WordTrace tailWord_606545 prefixEnd_606545 207632749054289749065371 := by
  unfold tailWord_606545
  simp only [CollatzResearch.WordTrace]
  refine ⟨22122513587598529483917089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14748342391732352989278059 22122513587598529483917089)
  ·
    refine ⟨16591885190698897112937817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22122513587598529483917089 16591885190698897112937817)
    ·
      refine ⟨12443913893024172834703363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16591885190698897112937817 12443913893024172834703363)
      ·
        refine ⟨18665870839536259252055045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12443913893024172834703363 18665870839536259252055045)
        ·
          refine ⟨3499850782413048609760321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18665870839536259252055045 3499850782413048609760321)
          ·
            refine ⟨2624888086809786457320241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3499850782413048609760321 2624888086809786457320241)
            ·
              refine ⟨1968666065107339842990181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2624888086809786457320241 1968666065107339842990181)
              ·
                refine ⟨369124887207626220560659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1968666065107339842990181 369124887207626220560659)
                ·
                  refine ⟨553687330811439330840989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 369124887207626220560659 553687330811439330840989)
                  ·
                    refine ⟨207632749054289749065371, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 553687330811439330840989 207632749054289749065371)
                    ·
                      rfl

theorem cell22_606545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 2, 4, 1, 3].length) (baseStart_606545 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_606545 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_606545 prefixEnd_606545 := by exact prefixLift 606545
  have htrace : WordTrace (prefixWord ++ tailWord_606545) baseStart_606545 baseEnd_606545 := by
    simpa [prefixWord, tailWord_606545, baseEnd_606545] using wordTrace_append hprefix tailTrace_606545
  have hstable : (prefixWord ++ tailWord_606545).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_606545).length < 2 ^ (prefixWord ++ tailWord_606545).sum := by decide
  have hdescent : baseEnd_606545 < baseStart_606545 := by decide
  rcases family_descends (prefixWord ++ tailWord_606545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_606603 : List Nat := [1, 1, 1, 1, 4, 6, 1, 1, 6]
def baseStart_606603 : Nat := 118140960795 + 606603 * 2 ^ 59
def prefixEnd_606603 : Nat := 4983230072969 + 3 ^ 40 * 606603 * 2
def baseEnd_606603 : Nat := 69217534546532310371731

theorem tailTrace_606603 : CollatzResearch.WordTrace tailWord_606603 prefixEnd_606603 69217534546532310371731 := by
  unfold tailWord_606603
  simp only [CollatzResearch.WordTrace]
  refine ⟨22124629021388405389528463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14749752680925603593018975 22124629021388405389528463)
  ·
    refine ⟨33186943532082608084292695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22124629021388405389528463 33186943532082608084292695)
    ·
      refine ⟨49780415298123912126439043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33186943532082608084292695 49780415298123912126439043)
      ·
        refine ⟨74670622947185868189658565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49780415298123912126439043 74670622947185868189658565)
        ·
          refine ⟨14000741802597350285560981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 74670622947185868189658565 14000741802597350285560981)
          ·
            refine ⟨656284771996750794635671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 14000741802597350285560981 656284771996750794635671)
            ·
              refine ⟨984427157995126191953507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 656284771996750794635671 984427157995126191953507)
              ·
                refine ⟨1476640736992689287930261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 984427157995126191953507 1476640736992689287930261)
                ·
                  refine ⟨69217534546532310371731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1476640736992689287930261 69217534546532310371731)
                  ·
                    rfl

theorem cell22_606603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 6, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 6, 1, 1, 6].length) (baseStart_606603 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_606603 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_606603 prefixEnd_606603 := by exact prefixLift 606603
  have htrace : WordTrace (prefixWord ++ tailWord_606603) baseStart_606603 baseEnd_606603 := by
    simpa [prefixWord, tailWord_606603, baseEnd_606603] using wordTrace_append hprefix tailTrace_606603
  have hstable : (prefixWord ++ tailWord_606603).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_606603).length < 2 ^ (prefixWord ++ tailWord_606603).sum := by decide
  have hdescent : baseEnd_606603 < baseStart_606603 := by decide
  rcases family_descends (prefixWord ++ tailWord_606603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_606622 : List Nat := [4, 3, 1, 2, 1, 1, 3, 2, 1, 4]
def baseStart_606622 : Nat := 118140960795 + 606622 * 2 ^ 59
def prefixEnd_606622 : Nat := 4983230072969 + 3 ^ 40 * 606622 * 2
def baseEnd_606622 : Nat := 207659107727887214890135

theorem tailTrace_606622 : CollatzResearch.WordTrace tailWord_606622 prefixEnd_606622 207659107727887214890135 := by
  unfold tailWord_606622
  simp only [CollatzResearch.WordTrace]
  refine ⟨2765665251039946454308765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14750214672213047756313413 2765665251039946454308765)
  ·
    refine ⟨1037124469139979920365787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2765665251039946454308765 1037124469139979920365787)
    ·
      refine ⟨1555686703709969880548681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1037124469139979920365787 1555686703709969880548681)
      ·
        refine ⟨1166765027782477410411511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1555686703709969880548681 1166765027782477410411511)
        ·
          refine ⟨1750147541673716115617267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1166765027782477410411511 1750147541673716115617267)
          ·
            refine ⟨2625221312510574173425901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1750147541673716115617267 2625221312510574173425901)
            ·
              refine ⟨984457992191465315034713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2625221312510574173425901 984457992191465315034713)
              ·
                refine ⟨738343494143598986276035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 984457992191465315034713 738343494143598986276035)
                ·
                  refine ⟨1107515241215398479414053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 738343494143598986276035 1107515241215398479414053)
                  ·
                    refine ⟨207659107727887214890135, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1107515241215398479414053 207659107727887214890135)
                    ·
                      rfl

theorem cell22_606622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 3, 2, 1, 4].length) (baseStart_606622 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_606622 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_606622 prefixEnd_606622 := by exact prefixLift 606622
  have htrace : WordTrace (prefixWord ++ tailWord_606622) baseStart_606622 baseEnd_606622 := by
    simpa [prefixWord, tailWord_606622, baseEnd_606622] using wordTrace_append hprefix tailTrace_606622
  have hstable : (prefixWord ++ tailWord_606622).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_606622).length < 2 ^ (prefixWord ++ tailWord_606622).sum := by decide
  have hdescent : baseEnd_606622 < baseStart_606622 := by decide
  rcases family_descends (prefixWord ++ tailWord_606622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_606652 : List Nat := [2, 2, 2, 4, 1, 2, 2, 2, 2, 3]
def baseStart_606652 : Nat := 118140960795 + 606652 * 2 ^ 59
def prefixEnd_606652 : Nat := 4983230072969 + 3 ^ 40 * 606652 * 2
def baseEnd_606652 : Nat := 207669377340977136640043

theorem tailTrace_606652 : CollatzResearch.WordTrace tailWord_606652 prefixEnd_606652 207669377340977136640043 := by
  unfold tailWord_606652
  simp only [CollatzResearch.WordTrace]
  refine ⟨11063208099105443379031105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14750944132140591172041473 11063208099105443379031105)
  ·
    refine ⟨8297406074329082534273329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11063208099105443379031105 8297406074329082534273329)
    ·
      refine ⟨6223054555746811900704997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8297406074329082534273329 6223054555746811900704997)
      ·
        refine ⟨1166822729202527231382187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6223054555746811900704997 1166822729202527231382187)
        ·
          refine ⟨1750234093803790847073281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1166822729202527231382187 1750234093803790847073281)
          ·
            refine ⟨1312675570352843135304961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1750234093803790847073281 1312675570352843135304961)
            ·
              refine ⟨984506677764632351478721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1312675570352843135304961 984506677764632351478721)
              ·
                refine ⟨738380008323474263609041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 984506677764632351478721 738380008323474263609041)
                ·
                  refine ⟨553785006242605697706781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 738380008323474263609041 553785006242605697706781)
                  ·
                    refine ⟨207669377340977136640043, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 553785006242605697706781 207669377340977136640043)
                    ·
                      rfl

theorem cell22_606652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 2, 2, 2, 2, 3].length) (baseStart_606652 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_606652 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_606652 prefixEnd_606652 := by exact prefixLift 606652
  have htrace : WordTrace (prefixWord ++ tailWord_606652) baseStart_606652 baseEnd_606652 := by
    simpa [prefixWord, tailWord_606652, baseEnd_606652] using wordTrace_append hprefix tailTrace_606652
  have hstable : (prefixWord ++ tailWord_606652).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_606652).length < 2 ^ (prefixWord ++ tailWord_606652).sum := by decide
  have hdescent : baseEnd_606652 < baseStart_606652 := by decide
  rcases family_descends (prefixWord ++ tailWord_606652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_606727 : List Nat := [1, 1, 4, 3, 3, 1, 3, 1, 5]
def baseStart_606727 : Nat := 118140960795 + 606727 * 2 ^ 59
def prefixEnd_606727 : Nat := 4983230072969 + 3 ^ 40 * 606727 * 2
def baseEnd_606727 : Nat := 69231683791233980338271

theorem tailTrace_606727 : CollatzResearch.WordTrace tailWord_606727 prefixEnd_606727 69231683791233980338271 := by
  unfold tailWord_606727
  simp only [CollatzResearch.WordTrace]
  refine ⟨22129151672939174567042435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14752767781959449711361623 22129151672939174567042435)
  ·
    refine ⟨33193727509408761850563653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22129151672939174567042435 33193727509408761850563653)
    ·
      refine ⟨6223823908014142846980685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 33193727509408761850563653 6223823908014142846980685)
      ·
        refine ⟨2333933965505303567617757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6223823908014142846980685 2333933965505303567617757)
        ·
          refine ⟨875225237064488837856659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2333933965505303567617757 875225237064488837856659)
          ·
            refine ⟨1312837855596733256784989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 875225237064488837856659 1312837855596733256784989)
            ·
              refine ⟨492314195848774971294371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1312837855596733256784989 492314195848774971294371)
              ·
                refine ⟨738471293773162456941557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 492314195848774971294371 738471293773162456941557)
                ·
                  refine ⟨69231683791233980338271, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 738471293773162456941557 69231683791233980338271)
                  ·
                    rfl

theorem cell22_606727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 1, 3, 1, 5].length) (baseStart_606727 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_606727 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_606727 prefixEnd_606727 := by exact prefixLift 606727
  have htrace : WordTrace (prefixWord ++ tailWord_606727) baseStart_606727 baseEnd_606727 := by
    simpa [prefixWord, tailWord_606727, baseEnd_606727] using wordTrace_append hprefix tailTrace_606727
  have hstable : (prefixWord ++ tailWord_606727).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_606727).length < 2 ^ (prefixWord ++ tailWord_606727).sum := by decide
  have hdescent : baseEnd_606727 < baseStart_606727 := by decide
  rcases family_descends (prefixWord ++ tailWord_606727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_606753 : List Nat := [1, 2, 3, 2, 2, 1, 2, 1, 3, 5]
def baseStart_606753 : Nat := 118140960795 + 606753 * 2 ^ 59
def prefixEnd_606753 : Nat := 4983230072969 + 3 ^ 40 * 606753 * 2
def baseEnd_606753 : Nat := 207703951705046539864733

theorem tailTrace_606753 : CollatzResearch.WordTrace tailWord_606753 prefixEnd_606753 207703951705046539864733 := by
  unfold tailWord_606753
  simp only [CollatzResearch.WordTrace]
  refine ⟨22130099970844981007488913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14753399980563320671659275 22130099970844981007488913)
  ·
    refine ⟨16597574978133735755616685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22130099970844981007488913 16597574978133735755616685)
    ·
      refine ⟨6224090616800150908356257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16597574978133735755616685 6224090616800150908356257)
      ·
        refine ⟨4668067962600113181267193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6224090616800150908356257 4668067962600113181267193)
        ·
          refine ⟨3501050971950084885950395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4668067962600113181267193 3501050971950084885950395)
          ·
            refine ⟨5251576457925127328925593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3501050971950084885950395 5251576457925127328925593)
            ·
              refine ⟨3938682343443845496694195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5251576457925127328925593 3938682343443845496694195)
              ·
                refine ⟨5908023515165768245041293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3938682343443845496694195 5908023515165768245041293)
                ·
                  refine ⟨2215508818187163091890485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5908023515165768245041293 2215508818187163091890485)
                  ·
                    refine ⟨207703951705046539864733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2215508818187163091890485 207703951705046539864733)
                    ·
                      rfl

theorem cell22_606753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 2, 1, 3, 5].length) (baseStart_606753 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_606753 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_606753 prefixEnd_606753 := by exact prefixLift 606753
  have htrace : WordTrace (prefixWord ++ tailWord_606753) baseStart_606753 baseEnd_606753 := by
    simpa [prefixWord, tailWord_606753, baseEnd_606753] using wordTrace_append hprefix tailTrace_606753
  have hstable : (prefixWord ++ tailWord_606753).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_606753).length < 2 ^ (prefixWord ++ tailWord_606753).sum := by decide
  have hdescent : baseEnd_606753 < baseStart_606753 := by decide
  rcases family_descends (prefixWord ++ tailWord_606753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_606765 : List Nat := [1, 5, 4, 1, 1, 1, 3, 2, 1, 3]
def baseStart_606765 : Nat := 118140960795 + 606765 * 2 ^ 59
def prefixEnd_606765 : Nat := 4983230072969 + 3 ^ 40 * 606765 * 2
def baseEnd_606765 : Nat := 207708059550282508564697

theorem tailTrace_606765 : CollatzResearch.WordTrace tailWord_606765 prefixEnd_606765 207708059550282508564697 := by
  unfold tailWord_606765
  simp only [CollatzResearch.WordTrace]
  refine ⟨22130537646801507056925749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14753691764534338037950499 22130537646801507056925749)
  ·
    refine ⟨2074737904387641286586789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 22130537646801507056925749 2074737904387641286586789)
    ·
      refine ⟨389013357072682741235023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2074737904387641286586789 389013357072682741235023)
      ·
        refine ⟨583520035609024111852535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 389013357072682741235023 583520035609024111852535)
        ·
          refine ⟨875280053413536167778803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 583520035609024111852535 875280053413536167778803)
          ·
            refine ⟨1312920080120304251668205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 875280053413536167778803 1312920080120304251668205)
            ·
              refine ⟨492345030045114094375577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1312920080120304251668205 492345030045114094375577)
              ·
                refine ⟨369258772533835570781683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 492345030045114094375577 369258772533835570781683)
                ·
                  refine ⟨553888158800753356172525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 369258772533835570781683 553888158800753356172525)
                  ·
                    refine ⟨207708059550282508564697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 553888158800753356172525 207708059550282508564697)
                    ·
                      rfl

theorem cell22_606765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 1, 3, 2, 1, 3].length) (baseStart_606765 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_606765 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_606765 prefixEnd_606765 := by exact prefixLift 606765
  have htrace : WordTrace (prefixWord ++ tailWord_606765) baseStart_606765 baseEnd_606765 := by
    simpa [prefixWord, tailWord_606765, baseEnd_606765] using wordTrace_append hprefix tailTrace_606765
  have hstable : (prefixWord ++ tailWord_606765).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_606765).length < 2 ^ (prefixWord ++ tailWord_606765).sum := by decide
  have hdescent : baseEnd_606765 < baseStart_606765 := by decide
  rcases family_descends (prefixWord ++ tailWord_606765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_606768 : List Nat := [2, 1, 1, 1, 2, 3, 3, 1, 4, 4]
def baseStart_606768 : Nat := 118140960795 + 606768 * 2 ^ 59
def prefixEnd_606768 : Nat := 4983230072969 + 3 ^ 40 * 606768 * 2
def baseEnd_606768 : Nat := 207709086511591500739687

theorem tailTrace_606768 : CollatzResearch.WordTrace tailWord_606768 prefixEnd_606768 207709086511591500739687 := by
  unfold tailWord_606768
  simp only [CollatzResearch.WordTrace]
  refine ⟨11065323532895319284642479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14753764710527092379523305 11065323532895319284642479)
  ·
    refine ⟨16597985299342978926963719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11065323532895319284642479 16597985299342978926963719)
    ·
      refine ⟨24896977949014468390445579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16597985299342978926963719 24896977949014468390445579)
      ·
        refine ⟨37345466923521702585668369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24896977949014468390445579 37345466923521702585668369)
        ·
          refine ⟨28009100192641276939251277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37345466923521702585668369 28009100192641276939251277)
          ·
            refine ⟨10503412572240478852219229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28009100192641276939251277 10503412572240478852219229)
            ·
              refine ⟨3938779714590179569582211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10503412572240478852219229 3938779714590179569582211)
              ·
                refine ⟨5908169571885269354373317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3938779714590179569582211 5908169571885269354373317)
                ·
                  refine ⟨1107781794728488003944997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5908169571885269354373317 1107781794728488003944997)
                  ·
                    refine ⟨207709086511591500739687, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1107781794728488003944997 207709086511591500739687)
                    ·
                      rfl

theorem cell22_606768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 3, 1, 4, 4].length) (baseStart_606768 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_606768 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_606768 prefixEnd_606768 := by exact prefixLift 606768
  have htrace : WordTrace (prefixWord ++ tailWord_606768) baseStart_606768 baseEnd_606768 := by
    simpa [prefixWord, tailWord_606768, baseEnd_606768] using wordTrace_append hprefix tailTrace_606768
  have hstable : (prefixWord ++ tailWord_606768).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_606768).length < 2 ^ (prefixWord ++ tailWord_606768).sum := by decide
  have hdescent : baseEnd_606768 < baseStart_606768 := by decide
  rcases family_descends (prefixWord ++ tailWord_606768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_606770 : List Nat := [3, 2, 1, 1, 2, 1, 4, 1, 4, 3]
def baseStart_606770 : Nat := 118140960795 + 606770 * 2 ^ 59
def prefixEnd_606770 : Nat := 4983230072969 + 3 ^ 40 * 606770 * 2
def baseEnd_606770 : Nat := 207709771152464162189681

theorem tailTrace_606770 : CollatzResearch.WordTrace tailWord_606770 prefixEnd_606770 207709771152464162189681 := by
  unfold tailWord_606770
  simp only [CollatzResearch.WordTrace]
  refine ⟨5532680002945848227714441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14753813341188928607238509 5532680002945848227714441)
  ·
    refine ⟨4149510002209386170785831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5532680002945848227714441 4149510002209386170785831)
    ·
      refine ⟨6224265003314079256178747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4149510002209386170785831 6224265003314079256178747)
      ·
        refine ⟨9336397504971118884268121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6224265003314079256178747 9336397504971118884268121)
        ·
          refine ⟨7002298128728339163201091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9336397504971118884268121 7002298128728339163201091)
          ·
            refine ⟨10503447193092508744801637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7002298128728339163201091 10503447193092508744801637)
            ·
              refine ⟨1969396348704845389650307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10503447193092508744801637 1969396348704845389650307)
              ·
                refine ⟨2954094523057268084475461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1969396348704845389650307 2954094523057268084475461)
                ·
                  refine ⟨553892723073237765839149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2954094523057268084475461 553892723073237765839149)
                  ·
                    refine ⟨207709771152464162189681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 553892723073237765839149 207709771152464162189681)
                    ·
                      rfl

theorem cell22_606770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 4, 1, 4, 3].length) (baseStart_606770 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_606770 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_606770 prefixEnd_606770 := by exact prefixLift 606770
  have htrace : WordTrace (prefixWord ++ tailWord_606770) baseStart_606770 baseEnd_606770 := by
    simpa [prefixWord, tailWord_606770, baseEnd_606770] using wordTrace_append hprefix tailTrace_606770
  have hstable : (prefixWord ++ tailWord_606770).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_606770).length < 2 ^ (prefixWord ++ tailWord_606770).sum := by decide
  have hdescent : baseEnd_606770 < baseStart_606770 := by decide
  rcases family_descends (prefixWord ++ tailWord_606770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_606783 : List Nat := [1, 1, 2, 2, 3, 2, 4, 7]
def baseStart_606783 : Nat := 118140960795 + 606783 * 2 ^ 59
def prefixEnd_606783 : Nat := 4983230072969 + 3 ^ 40 * 606783 * 2
def baseEnd_606783 : Nat := 23079357924237384623849

theorem tailTrace_606783 : CollatzResearch.WordTrace tailWord_606783 prefixEnd_606783 23079357924237384623849 := by
  unfold tailWord_606783
  simp only [CollatzResearch.WordTrace]
  refine ⟨22131194160736296131081003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14754129440490864087387335 22131194160736296131081003)
  ·
    refine ⟨33196791241104444196621505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22131194160736296131081003 33196791241104444196621505)
    ·
      refine ⟨24897593430828333147466129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33196791241104444196621505 24897593430828333147466129)
      ·
        refine ⟨18673195073121249860599597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24897593430828333147466129 18673195073121249860599597)
        ·
          refine ⟨7002448152420468697724849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18673195073121249860599597 7002448152420468697724849)
          ·
            refine ⟨5251836114315351523293637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7002448152420468697724849 5251836114315351523293637)
            ·
              refine ⟨984719271434128410617557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5251836114315351523293637 984719271434128410617557)
              ·
                refine ⟨23079357924237384623849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 984719271434128410617557 23079357924237384623849)
                ·
                  rfl

theorem cell22_606783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 4, 7].length) (baseStart_606783 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_606783 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_606783 prefixEnd_606783 := by exact prefixLift 606783
  have htrace : WordTrace (prefixWord ++ tailWord_606783) baseStart_606783 baseEnd_606783 := by
    simpa [prefixWord, tailWord_606783, baseEnd_606783] using wordTrace_append hprefix tailTrace_606783
  have hstable : (prefixWord ++ tailWord_606783).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_606783).length < 2 ^ (prefixWord ++ tailWord_606783).sum := by decide
  have hdescent : baseEnd_606783 < baseStart_606783 := by decide
  rcases family_descends (prefixWord ++ tailWord_606783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_606798 : List Nat := [4, 1, 1, 1, 1, 2, 2, 1, 2, 7]
def baseStart_606798 : Nat := 118140960795 + 606798 * 2 ^ 59
def prefixEnd_606798 : Nat := 4983230072969 + 3 ^ 40 * 606798 * 2
def baseEnd_606798 : Nat := 207719356124681422489595

theorem tailTrace_606798 : CollatzResearch.WordTrace tailWord_606798 prefixEnd_606798 207719356124681422489595 := by
  unfold tailWord_606798
  simp only [CollatzResearch.WordTrace]
  refine ⟨2766467656960244211609631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14754494170454635795251365 2766467656960244211609631)
  ·
    refine ⟨4149701485440366317414447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2766467656960244211609631 4149701485440366317414447)
    ·
      refine ⟨6224552228160549476121671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4149701485440366317414447 6224552228160549476121671)
      ·
        refine ⟨9336828342240824214182507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6224552228160549476121671 9336828342240824214182507)
        ·
          refine ⟨14005242513361236321273761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9336828342240824214182507 14005242513361236321273761)
          ·
            refine ⟨10503931885020927240955321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14005242513361236321273761 10503931885020927240955321)
            ·
              refine ⟨7877948913765695430716491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10503931885020927240955321 7877948913765695430716491)
              ·
                refine ⟨11816923370648543146074737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7877948913765695430716491 11816923370648543146074737)
                ·
                  refine ⟨8862692527986407359556053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11816923370648543146074737 8862692527986407359556053)
                  ·
                    refine ⟨207719356124681422489595, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 8862692527986407359556053 207719356124681422489595)
                    ·
                      rfl

theorem cell22_606798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 2, 1, 2, 7].length) (baseStart_606798 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_606798 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_606798 prefixEnd_606798 := by exact prefixLift 606798
  have htrace : WordTrace (prefixWord ++ tailWord_606798) baseStart_606798 baseEnd_606798 := by
    simpa [prefixWord, tailWord_606798, baseEnd_606798] using wordTrace_append hprefix tailTrace_606798
  have hstable : (prefixWord ++ tailWord_606798).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_606798).length < 2 ^ (prefixWord ++ tailWord_606798).sum := by decide
  have hdescent : baseEnd_606798 < baseStart_606798 := by decide
  rcases family_descends (prefixWord ++ tailWord_606798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_606828 : List Nat := [2, 2, 1, 1, 3, 1, 2, 3, 7]
def baseStart_606828 : Nat := 118140960795 + 606828 * 2 ^ 59
def prefixEnd_606828 : Nat := 4983230072969 + 3 ^ 40 * 606828 * 2
def baseEnd_606828 : Nat := 69243208579257114746501

theorem tailTrace_606828 : CollatzResearch.WordTrace tailWord_606828 prefixEnd_606828 69243208579257114746501 := by
  unfold tailWord_606828
  simp only [CollatzResearch.WordTrace]
  refine ⟨11066417722786634408234569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14755223630382179210979425 11066417722786634408234569)
  ·
    refine ⟨8299813292089975806175927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11066417722786634408234569 8299813292089975806175927)
    ·
      refine ⟨12449719938134963709263891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8299813292089975806175927 12449719938134963709263891)
      ·
        refine ⟨18674579907202445563895837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12449719938134963709263891 18674579907202445563895837)
        ·
          refine ⟨7002967465200917086460939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18674579907202445563895837 7002967465200917086460939)
          ·
            refine ⟨10504451197801375629691409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7002967465200917086460939 10504451197801375629691409)
            ·
              refine ⟨7878338398351031722268557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10504451197801375629691409 7878338398351031722268557)
              ·
                refine ⟨2954376899381636895850709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7878338398351031722268557 2954376899381636895850709)
                ·
                  refine ⟨69243208579257114746501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2954376899381636895850709 69243208579257114746501)
                  ·
                    rfl

theorem cell22_606828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 7].length) (baseStart_606828 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_606828 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_606828 prefixEnd_606828 := by exact prefixLift 606828
  have htrace : WordTrace (prefixWord ++ tailWord_606828) baseStart_606828 baseEnd_606828 := by
    simpa [prefixWord, tailWord_606828, baseEnd_606828] using wordTrace_append hprefix tailTrace_606828
  have hstable : (prefixWord ++ tailWord_606828).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_606828).length < 2 ^ (prefixWord ++ tailWord_606828).sum := by decide
  have hdescent : baseEnd_606828 < baseStart_606828 := by decide
  rcases family_descends (prefixWord ++ tailWord_606828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_606830 : List Nat := [4, 1, 2, 2, 2, 1, 1, 1, 2, 6]
def baseStart_606830 : Nat := 118140960795 + 606830 * 2 ^ 59
def prefixEnd_606830 : Nat := 4983230072969 + 3 ^ 40 * 606830 * 2
def baseEnd_606830 : Nat := 207730310378644005689497

theorem tailTrace_606830 : CollatzResearch.WordTrace tailWord_606830 prefixEnd_606830 207730310378644005689497 := by
  unfold tailWord_606830
  simp only [CollatzResearch.WordTrace]
  refine ⟨2766613548945752894755243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14755272261044015438694629 2766613548945752894755243)
  ·
    refine ⟨4149920323418629342132865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2766613548945752894755243 4149920323418629342132865)
    ·
      refine ⟨3112440242563972006599649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4149920323418629342132865 3112440242563972006599649)
      ·
        refine ⟨2334330181922979004949737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3112440242563972006599649 2334330181922979004949737)
        ·
          refine ⟨1750747636442234253712303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2334330181922979004949737 1750747636442234253712303)
          ·
            refine ⟨2626121454663351380568455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1750747636442234253712303 2626121454663351380568455)
            ·
              refine ⟨3939182181995027070852683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2626121454663351380568455 3939182181995027070852683)
              ·
                refine ⟨5908773272992540606279025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3939182181995027070852683 5908773272992540606279025)
                ·
                  refine ⟨4431579954744405454709269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5908773272992540606279025 4431579954744405454709269)
                  ·
                    refine ⟨207730310378644005689497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4431579954744405454709269 207730310378644005689497)
                    ·
                      rfl

theorem cell22_606830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 1, 1, 2, 6].length) (baseStart_606830 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_606830 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_606830 prefixEnd_606830 := by exact prefixLift 606830
  have htrace : WordTrace (prefixWord ++ tailWord_606830) baseStart_606830 baseEnd_606830 := by
    simpa [prefixWord, tailWord_606830, baseEnd_606830] using wordTrace_append hprefix tailTrace_606830
  have hstable : (prefixWord ++ tailWord_606830).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_606830).length < 2 ^ (prefixWord ++ tailWord_606830).sum := by decide
  have hdescent : baseEnd_606830 < baseStart_606830 := by decide
  rcases family_descends (prefixWord ++ tailWord_606830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_606866 : List Nat := [3, 2, 3, 1, 2, 2, 2, 3, 1, 3]
def baseStart_606866 : Nat := 118140960795 + 606866 * 2 ^ 59
def prefixEnd_606866 : Nat := 4983230072969 + 3 ^ 40 * 606866 * 2
def baseEnd_606866 : Nat := 207742633914351911789387

theorem tailTrace_606866 : CollatzResearch.WordTrace tailWord_606866 prefixEnd_606866 207742633914351911789387 := by
  unfold tailWord_606866
  simp only [CollatzResearch.WordTrace]
  refine ⟨5533555354858900326588113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14756147612957067537568301 5533555354858900326588113)
  ·
    refine ⟨4150166516144175244941085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5533555354858900326588113 4150166516144175244941085)
    ·
      refine ⟨1556312443554065716852907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4150166516144175244941085 1556312443554065716852907)
      ·
        refine ⟨2334468665331098575279361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1556312443554065716852907 2334468665331098575279361)
        ·
          refine ⟨1750851498998323931459521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2334468665331098575279361 1750851498998323931459521)
          ·
            refine ⟨1313138624248742948594641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1750851498998323931459521 1313138624248742948594641)
            ·
              refine ⟨984853968186557211445981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1313138624248742948594641 984853968186557211445981)
              ·
                refine ⟨369320238069958954292243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 984853968186557211445981 369320238069958954292243)
                ·
                  refine ⟨553980357104938431438365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 369320238069958954292243 553980357104938431438365)
                  ·
                    refine ⟨207742633914351911789387, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 553980357104938431438365 207742633914351911789387)
                    ·
                      rfl

theorem cell22_606866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 2, 2, 3, 1, 3].length) (baseStart_606866 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_606866 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_606866 prefixEnd_606866 := by exact prefixLift 606866
  have htrace : WordTrace (prefixWord ++ tailWord_606866) baseStart_606866 baseEnd_606866 := by
    simpa [prefixWord, tailWord_606866, baseEnd_606866] using wordTrace_append hprefix tailTrace_606866
  have hstable : (prefixWord ++ tailWord_606866).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_606866).length < 2 ^ (prefixWord ++ tailWord_606866).sum := by decide
  have hdescent : baseEnd_606866 < baseStart_606866 := by decide
  rcases family_descends (prefixWord ++ tailWord_606866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_606873 : List Nat := [1, 2, 1, 2, 1, 2, 3, 2, 8]
def baseStart_606873 : Nat := 118140960795 + 606873 * 2 ^ 59
def prefixEnd_606873 : Nat := 4983230072969 + 3 ^ 40 * 606873 * 2
def baseEnd_606873 : Nat := 69248343385802075621455

theorem tailTrace_606873 : CollatzResearch.WordTrace tailWord_606873 prefixEnd_606873 69248343385802075621455 := by
  unfold tailWord_606873
  simp only [CollatzResearch.WordTrace]
  refine ⟨22134476730410241501857273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14756317820273494334571515 22134476730410241501857273)
  ·
    refine ⟨16600857547807681126392955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22134476730410241501857273 16600857547807681126392955)
    ·
      refine ⟨24901286321711521689589433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16600857547807681126392955 24901286321711521689589433)
      ·
        refine ⟨18675964741283641267192075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24901286321711521689589433 18675964741283641267192075)
        ·
          refine ⟨28013947111925461900788113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18675964741283641267192075 28013947111925461900788113)
          ·
            refine ⟨21010460333944096425591085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28013947111925461900788113 21010460333944096425591085)
            ·
              refine ⟨7878922625229036159596657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21010460333944096425591085 7878922625229036159596657)
              ·
                refine ⟨5909191968921777119697493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7878922625229036159596657 5909191968921777119697493)
                ·
                  refine ⟨69248343385802075621455, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 5909191968921777119697493 69248343385802075621455)
                  ·
                    rfl

theorem cell22_606873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 3, 2, 8].length) (baseStart_606873 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_606873 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_606873 prefixEnd_606873 := by exact prefixLift 606873
  have htrace : WordTrace (prefixWord ++ tailWord_606873) baseStart_606873 baseEnd_606873 := by
    simpa [prefixWord, tailWord_606873, baseEnd_606873] using wordTrace_append hprefix tailTrace_606873
  have hstable : (prefixWord ++ tailWord_606873).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_606873).length < 2 ^ (prefixWord ++ tailWord_606873).sum := by decide
  have hdescent : baseEnd_606873 < baseStart_606873 := by decide
  rcases family_descends (prefixWord ++ tailWord_606873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_606920 : List Nat := [2, 1, 3, 1, 2, 3, 2, 1, 1, 6]
def baseStart_606920 : Nat := 118140960795 + 606920 * 2 ^ 59
def prefixEnd_606920 : Nat := 4983230072969 + 3 ^ 40 * 606920 * 2
def baseEnd_606920 : Nat := 207761119217913770939221

theorem tailTrace_606920 : CollatzResearch.WordTrace tailWord_606920 prefixEnd_606920 207761119217913770939221 := by
  unfold tailWord_606920
  simp only [CollatzResearch.WordTrace]
  refine ⟨11068095480619984264409107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14757460640826645685878809 11068095480619984264409107)
  ·
    refine ⟨16602143220929976396613661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11068095480619984264409107 16602143220929976396613661)
    ·
      refine ⟨6225803707848741148730123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16602143220929976396613661 6225803707848741148730123)
      ·
        refine ⟨9338705561773111723095185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6225803707848741148730123 9338705561773111723095185)
        ·
          refine ⟨7004029171329833792321389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9338705561773111723095185 7004029171329833792321389)
          ·
            refine ⟨2626510939248687672120521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7004029171329833792321389 2626510939248687672120521)
            ·
              refine ⟨1969883204436515754090391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2626510939248687672120521 1969883204436515754090391)
              ·
                refine ⟨2954824806654773631135587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1969883204436515754090391 2954824806654773631135587)
                ·
                  refine ⟨4432237209982160446703381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2954824806654773631135587 4432237209982160446703381)
                  ·
                    refine ⟨207761119217913770939221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4432237209982160446703381 207761119217913770939221)
                    ·
                      rfl

theorem cell22_606920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 2, 1, 1, 6].length) (baseStart_606920 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_606920 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_606920 prefixEnd_606920 := by exact prefixLift 606920
  have htrace : WordTrace (prefixWord ++ tailWord_606920) baseStart_606920 baseEnd_606920 := by
    simpa [prefixWord, tailWord_606920, baseEnd_606920] using wordTrace_append hprefix tailTrace_606920
  have hstable : (prefixWord ++ tailWord_606920).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_606920).length < 2 ^ (prefixWord ++ tailWord_606920).sum := by decide
  have hdescent : baseEnd_606920 < baseStart_606920 := by decide
  rcases family_descends (prefixWord ++ tailWord_606920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_606922 : List Nat := [3, 1, 2, 1, 4, 1, 1, 2, 4, 3]
def baseStart_606922 : Nat := 118140960795 + 606922 * 2 ^ 59
def prefixEnd_606922 : Nat := 4983230072969 + 3 ^ 40 * 606922 * 2
def baseEnd_606922 : Nat := 207761803858786432389215

theorem tailTrace_606922 : CollatzResearch.WordTrace tailWord_606922 prefixEnd_606922 207761803858786432389215 := by
  unfold tailWord_606922
  simp only [CollatzResearch.WordTrace]
  refine ⟨5534065976808180717597755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14757509271488481913594013 5534065976808180717597755)
  ·
    refine ⟨8301098965212271076396633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5534065976808180717597755 8301098965212271076396633)
    ·
      refine ⟨6225824223909203307297475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8301098965212271076396633 6225824223909203307297475)
      ·
        refine ⟨9338736335863804960946213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6225824223909203307297475 9338736335863804960946213)
        ·
          refine ⟨1751013062974463430177415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9338736335863804960946213 1751013062974463430177415)
          ·
            refine ⟨2626519594461695145266123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1751013062974463430177415 2626519594461695145266123)
            ·
              refine ⟨3939779391692542717899185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2626519594461695145266123 3939779391692542717899185)
              ·
                refine ⟨2954834543769407038424389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3939779391692542717899185 2954834543769407038424389)
                ·
                  refine ⟨554031476956763819704573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2954834543769407038424389 554031476956763819704573)
                  ·
                    refine ⟨207761803858786432389215, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 554031476956763819704573 207761803858786432389215)
                    ·
                      rfl

theorem cell22_606922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 1, 2, 4, 3].length) (baseStart_606922 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_606922 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_606922 prefixEnd_606922 := by exact prefixLift 606922
  have htrace : WordTrace (prefixWord ++ tailWord_606922) baseStart_606922 baseEnd_606922 := by
    simpa [prefixWord, tailWord_606922, baseEnd_606922] using wordTrace_append hprefix tailTrace_606922
  have hstable : (prefixWord ++ tailWord_606922).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_606922).length < 2 ^ (prefixWord ++ tailWord_606922).sum := by decide
  have hdescent : baseEnd_606922 < baseStart_606922 := by decide
  rcases family_descends (prefixWord ++ tailWord_606922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_606924 : List Nat := [2, 2, 1, 5, 1, 1, 3, 3, 4]
def baseStart_606924 : Nat := 118140960795 + 606924 * 2 ^ 59
def prefixEnd_606924 : Nat := 4983230072969 + 3 ^ 40 * 606924 * 2
def baseEnd_606924 : Nat := 69254162833219697946403

theorem tailTrace_606924 : CollatzResearch.WordTrace tailWord_606924 prefixEnd_606924 69254162833219697946403 := by
  unfold tailWord_606924
  simp only [CollatzResearch.WordTrace]
  refine ⟨11068168426612738605981913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14757557902150318141309217 11068168426612738605981913)
  ·
    refine ⟨8301126319959553954486435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11068168426612738605981913 8301126319959553954486435)
    ·
      refine ⟨12451689479939330931729653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8301126319959553954486435 12451689479939330931729653)
      ·
        refine ⟨1167345888744312274849655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 12451689479939330931729653 1167345888744312274849655)
        ·
          refine ⟨1751018833116468412274483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1167345888744312274849655 1751018833116468412274483)
          ·
            refine ⟨2626528249674702618411725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1751018833116468412274483 2626528249674702618411725)
            ·
              refine ⟨984948093628013481904397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2626528249674702618411725 984948093628013481904397)
              ·
                refine ⟨369355535110505055714149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 984948093628013481904397 369355535110505055714149)
                ·
                  refine ⟨69254162833219697946403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 369355535110505055714149 69254162833219697946403)
                  ·
                    rfl

theorem cell22_606924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 3, 3, 4].length) (baseStart_606924 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_606924 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_606924 prefixEnd_606924 := by exact prefixLift 606924
  have htrace : WordTrace (prefixWord ++ tailWord_606924) baseStart_606924 baseEnd_606924 := by
    simpa [prefixWord, tailWord_606924, baseEnd_606924] using wordTrace_append hprefix tailTrace_606924
  have hstable : (prefixWord ++ tailWord_606924).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_606924).length < 2 ^ (prefixWord ++ tailWord_606924).sum := by decide
  have hdescent : baseEnd_606924 < baseStart_606924 := by decide
  rcases family_descends (prefixWord ++ tailWord_606924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_606935 : List Nat := [1, 1, 3, 2, 1, 6, 8]
def baseStart_606935 : Nat := 118140960795 + 606935 * 2 ^ 59
def prefixEnd_606935 : Nat := 4983230072969 + 3 ^ 40 * 606935 * 2
def baseEnd_606935 : Nat := 7695046445350323400525

theorem tailTrace_606935 : CollatzResearch.WordTrace tailWord_606935 prefixEnd_606935 7695046445350323400525 := by
  unfold tailWord_606935
  simp only [CollatzResearch.WordTrace]
  refine ⟨22136738056185626090614259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14757825370790417393742839 22136738056185626090614259)
  ·
    refine ⟨33205107084278439135921389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22136738056185626090614259 33205107084278439135921389)
    ·
      refine ⟨12451915156604414675970521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33205107084278439135921389 12451915156604414675970521)
      ·
        refine ⟨9338936367453311006977891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12451915156604414675970521 9338936367453311006977891)
        ·
          refine ⟨14008404551179966510466837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9338936367453311006977891 14008404551179966510466837)
          ·
            refine ⟨656643963336560930178133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 14008404551179966510466837 656643963336560930178133)
            ·
              refine ⟨7695046445350323400525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 656643963336560930178133 7695046445350323400525)
              ·
                rfl

theorem cell22_606935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 6, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 6, 8].length) (baseStart_606935 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_606935 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_606935 prefixEnd_606935 := by exact prefixLift 606935
  have htrace : WordTrace (prefixWord ++ tailWord_606935) baseStart_606935 baseEnd_606935 := by
    simpa [prefixWord, tailWord_606935, baseEnd_606935] using wordTrace_append hprefix tailTrace_606935
  have hstable : (prefixWord ++ tailWord_606935).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_606935).length < 2 ^ (prefixWord ++ tailWord_606935).sum := by decide
  have hdescent : baseEnd_606935 < baseStart_606935 := by decide
  rcases family_descends (prefixWord ++ tailWord_606935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_606952 : List Nat := [2, 1, 4, 1, 4, 1, 2, 7]
def baseStart_606952 : Nat := 118140960795 + 606952 * 2 ^ 59
def prefixEnd_606952 : Nat := 4983230072969 + 3 ^ 40 * 606952 * 2
def baseEnd_606952 : Nat := 23085785941319594904347

theorem tailTrace_606952 : CollatzResearch.WordTrace tailWord_606952 prefixEnd_606952 23085785941319594904347 := by
  unfold tailWord_606952
  simp only [CollatzResearch.WordTrace]
  refine ⟨11068679048562018996991555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14758238731416025329322073 11068679048562018996991555)
  ·
    refine ⟨16603018572843028495487333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11068679048562018996991555 16603018572843028495487333)
    ·
      refine ⟨3113065982408067842903875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 16603018572843028495487333 3113065982408067842903875)
      ·
        refine ⟨4669598973612101764355813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3113065982408067842903875 4669598973612101764355813)
        ·
          refine ⟨875549807552269080816715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4669598973612101764355813 875549807552269080816715)
          ·
            refine ⟨1313324711328403621225073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 875549807552269080816715 1313324711328403621225073)
            ·
              refine ⟨984993533496302715918805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1313324711328403621225073 984993533496302715918805)
              ·
                refine ⟨23085785941319594904347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 984993533496302715918805 23085785941319594904347)
                ·
                  rfl

theorem cell22_606952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 1, 2, 7].length) (baseStart_606952 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_606952 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_606952 prefixEnd_606952 := by exact prefixLift 606952
  have htrace : WordTrace (prefixWord ++ tailWord_606952) baseStart_606952 baseEnd_606952 := by
    simpa [prefixWord, tailWord_606952, baseEnd_606952] using wordTrace_append hprefix tailTrace_606952
  have hstable : (prefixWord ++ tailWord_606952).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_606952).length < 2 ^ (prefixWord ++ tailWord_606952).sum := by decide
  have hdescent : baseEnd_606952 < baseStart_606952 := by decide
  rcases family_descends (prefixWord ++ tailWord_606952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_606995 : List Nat := [1, 1, 1, 2, 1, 3, 4, 2, 2, 5]
def baseStart_606995 : Nat := 118140960795 + 606995 * 2 ^ 59
def prefixEnd_606995 : Nat := 4983230072969 + 3 ^ 40 * 606995 * 2
def baseEnd_606995 : Nat := 207786793250638575313991

theorem tailTrace_606995 : CollatzResearch.WordTrace tailWord_606995 prefixEnd_606995 207786793250638575313991 := by
  unfold tailWord_606995
  simp only [CollatzResearch.WordTrace]
  refine ⟨22138926435968256337798439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14759284290645504225198959 22138926435968256337798439)
  ·
    refine ⟨33208389653952384506697659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22138926435968256337798439 33208389653952384506697659)
    ·
      refine ⟨49812584480928576760046489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33208389653952384506697659 49812584480928576760046489)
      ·
        refine ⟨37359438360696432570034867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49812584480928576760046489 37359438360696432570034867)
        ·
          refine ⟨56039157541044648855052301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37359438360696432570034867 56039157541044648855052301)
          ·
            refine ⟨21014684077891743320644613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 56039157541044648855052301 21014684077891743320644613)
            ·
              refine ⟨3940253264604701872620865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21014684077891743320644613 3940253264604701872620865)
              ·
                refine ⟨2955189948453526404465649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3940253264604701872620865 2955189948453526404465649)
                ·
                  refine ⟨2216392461340144803349237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2955189948453526404465649 2216392461340144803349237)
                  ·
                    refine ⟨207786793250638575313991, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2216392461340144803349237 207786793250638575313991)
                    ·
                      rfl

theorem cell22_606995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 4, 2, 2, 5].length) (baseStart_606995 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_606995 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_606995 prefixEnd_606995 := by exact prefixLift 606995
  have htrace : WordTrace (prefixWord ++ tailWord_606995) baseStart_606995 baseEnd_606995 := by
    simpa [prefixWord, tailWord_606995, baseEnd_606995] using wordTrace_append hprefix tailTrace_606995
  have hstable : (prefixWord ++ tailWord_606995).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_606995).length < 2 ^ (prefixWord ++ tailWord_606995).sum := by decide
  have hdescent : baseEnd_606995 < baseStart_606995 := by decide
  rcases family_descends (prefixWord ++ tailWord_606995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_606997 : List Nat := [1, 3, 2, 1, 2, 2, 4, 2, 5]
def baseStart_606997 : Nat := 118140960795 + 606997 * 2 ^ 59
def prefixEnd_606997 : Nat := 4983230072969 + 3 ^ 40 * 606997 * 2
def baseEnd_606997 : Nat := 69262492630503745587995

theorem tailTrace_606997 : CollatzResearch.WordTrace tailWord_606997 prefixEnd_606997 69262492630503745587995 := by
  unfold tailWord_606997
  simp only [CollatzResearch.WordTrace]
  refine ⟨22138999381961010679371245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14759332921307340452914163 22138999381961010679371245)
  ·
    refine ⟨8302124768235379004764217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22138999381961010679371245 8302124768235379004764217)
    ·
      refine ⟨6226593576176534253573163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8302124768235379004764217 6226593576176534253573163)
      ·
        refine ⟨9339890364264801380359745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6226593576176534253573163 9339890364264801380359745)
        ·
          refine ⟨7004917773198601035269809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9339890364264801380359745 7004917773198601035269809)
          ·
            refine ⟨5253688329898950776452357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7004917773198601035269809 5253688329898950776452357)
            ·
              refine ⟨985066561856053270584817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5253688329898950776452357 985066561856053270584817)
              ·
                refine ⟨738799921392039952938613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 985066561856053270584817 738799921392039952938613)
                ·
                  refine ⟨69262492630503745587995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 738799921392039952938613 69262492630503745587995)
                  ·
                    rfl

theorem cell22_606997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 4, 2, 5].length) (baseStart_606997 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_606997 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_606997 prefixEnd_606997 := by exact prefixLift 606997
  have htrace : WordTrace (prefixWord ++ tailWord_606997) baseStart_606997 baseEnd_606997 := by
    simpa [prefixWord, tailWord_606997, baseEnd_606997] using wordTrace_append hprefix tailTrace_606997
  have hstable : (prefixWord ++ tailWord_606997).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_606997).length < 2 ^ (prefixWord ++ tailWord_606997).sum := by decide
  have hdescent : baseEnd_606997 < baseStart_606997 := by decide
  rcases family_descends (prefixWord ++ tailWord_606997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_607027 : List Nat := [1, 1, 1, 2, 6, 1, 2, 1, 3, 4]
def baseStart_607027 : Nat := 118140960795 + 607027 * 2 ^ 59
def prefixEnd_607027 : Nat := 4983230072969 + 3 ^ 40 * 607027 * 2
def baseEnd_607027 : Nat := 207797747504601158513893

theorem tailTrace_607027 : CollatzResearch.WordTrace tailWord_607027 prefixEnd_607027 207797747504601158513893 := by
  unfold tailWord_607027
  simp only [CollatzResearch.WordTrace]
  refine ⟨22140093571852325802963335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14760062381234883868642223 22140093571852325802963335)
  ·
    refine ⟨33210140357778488704445003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22140093571852325802963335 33210140357778488704445003)
    ·
      refine ⟨49815210536667733056667505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33210140357778488704445003 49815210536667733056667505)
      ·
        refine ⟨37361407902500799792500629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49815210536667733056667505 37361407902500799792500629)
        ·
          refine ⟨1751315995429724990273467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 37361407902500799792500629 1751315995429724990273467)
          ·
            refine ⟨2626973993144587485410201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1751315995429724990273467 2626973993144587485410201)
            ·
              refine ⟨1970230494858440614057651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2626973993144587485410201 1970230494858440614057651)
              ·
                refine ⟨2955345742287660921086477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1970230494858440614057651 2955345742287660921086477)
                ·
                  refine ⟨1108254653357872845407429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2955345742287660921086477 1108254653357872845407429)
                  ·
                    refine ⟨207797747504601158513893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1108254653357872845407429 207797747504601158513893)
                    ·
                      rfl

theorem cell22_607027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 2, 1, 3, 4].length) (baseStart_607027 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_607027 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_607027 prefixEnd_607027 := by exact prefixLift 607027
  have htrace : WordTrace (prefixWord ++ tailWord_607027) baseStart_607027 baseEnd_607027 := by
    simpa [prefixWord, tailWord_607027, baseEnd_607027] using wordTrace_append hprefix tailTrace_607027
  have hstable : (prefixWord ++ tailWord_607027).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_607027).length < 2 ^ (prefixWord ++ tailWord_607027).sum := by decide
  have hdescent : baseEnd_607027 < baseStart_607027 := by decide
  rcases family_descends (prefixWord ++ tailWord_607027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_607194 : List Nat := [3, 1, 1, 2, 4, 2, 1, 2, 6]
def baseStart_607194 : Nat := 118140960795 + 607194 * 2 ^ 59
def prefixEnd_607194 : Nat := 4983230072969 + 3 ^ 40 * 607194 * 2
def baseEnd_607194 : Nat := 69284971672489463196127

theorem tailTrace_607194 : CollatzResearch.WordTrace tailWord_607194 prefixEnd_607194 69284971672489463196127 := by
  unfold tailWord_607194
  simp only [CollatzResearch.WordTrace]
  refine ⟨5536546140561828331073159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14764123041498208882861757 5536546140561828331073159)
  ·
    refine ⟨8304819210842742496609739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5536546140561828331073159 8304819210842742496609739)
    ·
      refine ⟨12457228816264113744914609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8304819210842742496609739 12457228816264113744914609)
      ·
        refine ⟨9342921612198085308685957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12457228816264113744914609 9342921612198085308685957)
        ·
          refine ⟨1751797802287140995378617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9342921612198085308685957 1751797802287140995378617)
          ·
            refine ⟨1313848351715355746533963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1751797802287140995378617 1313848351715355746533963)
            ·
              refine ⟨1970772527573033619800945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1313848351715355746533963 1970772527573033619800945)
              ·
                refine ⟨1478079395679775214850709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1970772527573033619800945 1478079395679775214850709)
                ·
                  refine ⟨69284971672489463196127, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1478079395679775214850709 69284971672489463196127)
                  ·
                    rfl

theorem cell22_607194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 2, 1, 2, 6].length) (baseStart_607194 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_607194 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_607194 prefixEnd_607194 := by exact prefixLift 607194
  have htrace : WordTrace (prefixWord ++ tailWord_607194) baseStart_607194 baseEnd_607194 := by
    simpa [prefixWord, tailWord_607194, baseEnd_607194] using wordTrace_append hprefix tailTrace_607194
  have hstable : (prefixWord ++ tailWord_607194).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_607194).length < 2 ^ (prefixWord ++ tailWord_607194).sum := by decide
  have hdescent : baseEnd_607194 < baseStart_607194 := by decide
  rcases family_descends (prefixWord ++ tailWord_607194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_607243 : List Nat := [1, 1, 1, 1, 6, 3, 3, 1, 2, 3]
def baseStart_607243 : Nat := 118140960795 + 607243 * 2 ^ 59
def prefixEnd_607243 : Nat := 4983230072969 + 3 ^ 40 * 607243 * 2
def baseEnd_607243 : Nat := 207871688718848595113231

theorem tailTrace_607243 : CollatzResearch.WordTrace tailWord_607243 prefixEnd_607243 207871688718848595113231 := by
  unfold tailWord_607243
  simp only [CollatzResearch.WordTrace]
  refine ⟨22147971739069794692826383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14765314492713196461884255 22147971739069794692826383)
  ·
    refine ⟨33221957608604692039239575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22147971739069794692826383 33221957608604692039239575)
    ·
      refine ⟨49832936412907038058859363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33221957608604692039239575 49832936412907038058859363)
      ·
        refine ⟨74749404619360557088289045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49832936412907038058859363 74749404619360557088289045)
        ·
          refine ⟨3503878341532526113513549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 74749404619360557088289045 3503878341532526113513549)
          ·
            refine ⟨1313954378074697292567581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3503878341532526113513549 1313954378074697292567581)
            ·
              refine ⟨492732891778011484712843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1313954378074697292567581 492732891778011484712843)
              ·
                refine ⟨739099337667017227069265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 492732891778011484712843 739099337667017227069265)
                ·
                  refine ⟨554324503250262920301949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 739099337667017227069265 554324503250262920301949)
                  ·
                    refine ⟨207871688718848595113231, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 554324503250262920301949 207871688718848595113231)
                    ·
                      rfl

theorem cell22_607243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 3, 3, 1, 2, 3].length) (baseStart_607243 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_607243 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_607243 prefixEnd_607243 := by exact prefixLift 607243
  have htrace : WordTrace (prefixWord ++ tailWord_607243) baseStart_607243 baseEnd_607243 := by
    simpa [prefixWord, tailWord_607243, baseEnd_607243] using wordTrace_append hprefix tailTrace_607243
  have hstable : (prefixWord ++ tailWord_607243).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_607243).length < 2 ^ (prefixWord ++ tailWord_607243).sum := by decide
  have hdescent : baseEnd_607243 < baseStart_607243 := by decide
  rcases family_descends (prefixWord ++ tailWord_607243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_607256 : List Nat := [2, 1, 2, 3, 2, 4, 2, 6]
def baseStart_607256 : Nat := 118140960795 + 607256 * 2 ^ 59
def prefixEnd_607256 : Nat := 4983230072969 + 3 ^ 40 * 607256 * 2
def baseEnd_607256 : Nat := 23097348764946766059799

theorem tailTrace_607256 : CollatzResearch.WordTrace tailWord_607256 prefixEnd_607256 23097348764946766059799 := by
  unfold tailWord_607256
  simp only [CollatzResearch.WordTrace]
  refine ⟨11074222944011348956524811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14765630592015131942033081 11074222944011348956524811)
  ·
    refine ⟨16611334416017023434787217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11074222944011348956524811 16611334416017023434787217)
    ·
      refine ⟨12458500812012767576090413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16611334416017023434787217 12458500812012767576090413)
      ·
        refine ⟨4671937804504787841033905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12458500812012767576090413 4671937804504787841033905)
        ·
          refine ⟨3503953353378590880775429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4671937804504787841033905 3503953353378590880775429)
          ·
            refine ⟨656991253758485790145393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3503953353378590880775429 656991253758485790145393)
            ·
              refine ⟨492743440318864342609045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 656991253758485790145393 492743440318864342609045)
              ·
                refine ⟨23097348764946766059799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 492743440318864342609045 23097348764946766059799)
                ·
                  rfl

theorem cell22_607256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 4, 2, 6].length) (baseStart_607256 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_607256 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_607256 prefixEnd_607256 := by exact prefixLift 607256
  have htrace : WordTrace (prefixWord ++ tailWord_607256) baseStart_607256 baseEnd_607256 := by
    simpa [prefixWord, tailWord_607256, baseEnd_607256] using wordTrace_append hprefix tailTrace_607256
  have hstable : (prefixWord ++ tailWord_607256).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_607256).length < 2 ^ (prefixWord ++ tailWord_607256).sum := by decide
  have hdescent : baseEnd_607256 < baseStart_607256 := by decide
  rcases family_descends (prefixWord ++ tailWord_607256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_607288 : List Nat := [2, 1, 2, 1, 5, 3, 1, 1, 3, 3]
def baseStart_607288 : Nat := 118140960795 + 607288 * 2 ^ 59
def prefixEnd_607288 : Nat := 4983230072969 + 3 ^ 40 * 607288 * 2
def baseEnd_607288 : Nat := 207887093138483477738093

theorem tailTrace_607288 : CollatzResearch.WordTrace tailWord_607288 prefixEnd_607288 207887093138483477738093 := by
  unfold tailWord_607288
  simp only [CollatzResearch.WordTrace]
  refine ⟨11074806511953383689107259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14766408682604511585476345 11074806511953383689107259)
  ·
    refine ⟨16612209767930075533660889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11074806511953383689107259 16612209767930075533660889)
    ·
      refine ⟨12459157325947556650245667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16612209767930075533660889 12459157325947556650245667)
      ·
        refine ⟨18688735988921334975368501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12459157325947556650245667 18688735988921334975368501)
        ·
          refine ⟨1752068998961375153940797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 18688735988921334975368501 1752068998961375153940797)
          ·
            refine ⟨657025874610515682727799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1752068998961375153940797 657025874610515682727799)
            ·
              refine ⟨985538811915773524091699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 657025874610515682727799 985538811915773524091699)
              ·
                refine ⟨1478308217873660286137549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 985538811915773524091699 1478308217873660286137549)
                ·
                  refine ⟨554365581702622607301581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1478308217873660286137549 554365581702622607301581)
                  ·
                    refine ⟨207887093138483477738093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 554365581702622607301581 207887093138483477738093)
                    ·
                      rfl

theorem cell22_607288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 3, 1, 1, 3, 3].length) (baseStart_607288 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_607288 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_607288 prefixEnd_607288 := by exact prefixLift 607288
  have htrace : WordTrace (prefixWord ++ tailWord_607288) baseStart_607288 baseEnd_607288 := by
    simpa [prefixWord, tailWord_607288, baseEnd_607288] using wordTrace_append hprefix tailTrace_607288
  have hstable : (prefixWord ++ tailWord_607288).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_607288).length < 2 ^ (prefixWord ++ tailWord_607288).sum := by decide
  have hdescent : baseEnd_607288 < baseStart_607288 := by decide
  rcases family_descends (prefixWord ++ tailWord_607288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_607301 : List Nat := [1, 3, 1, 1, 1, 3, 6, 1, 5]
def baseStart_607301 : Nat := 118140960795 + 607301 * 2 ^ 59
def prefixEnd_607301 : Nat := 4983230072969 + 3 ^ 40 * 607301 * 2
def baseEnd_607301 : Nat := 69297181101385259054351

theorem tailTrace_607301 : CollatzResearch.WordTrace tailWord_607301 prefixEnd_607301 69297181101385259054351 := by
  unfold tailWord_607301
  simp only [CollatzResearch.WordTrace]
  refine ⟨22150087172859670598437757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14766724781906447065625171 22150087172859670598437757)
  ·
    refine ⟨8306282689822376474414159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22150087172859670598437757 8306282689822376474414159)
    ·
      refine ⟨12459424034733564711621239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8306282689822376474414159 12459424034733564711621239)
      ·
        refine ⟨18689136052100347067431859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12459424034733564711621239 18689136052100347067431859)
        ·
          refine ⟨28033704078150520601147789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18689136052100347067431859 28033704078150520601147789)
          ·
            refine ⟨10512639029306445225430421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28033704078150520601147789 10512639029306445225430421)
            ·
              refine ⟨492779954498739619942051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 10512639029306445225430421 492779954498739619942051)
              ·
                refine ⟨739169931748109429913077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 492779954498739619942051 739169931748109429913077)
                ·
                  refine ⟨69297181101385259054351, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 739169931748109429913077 69297181101385259054351)
                  ·
                    rfl

theorem cell22_607301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 6, 1, 5].length) (baseStart_607301 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_607301 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_607301 prefixEnd_607301 := by exact prefixLift 607301
  have htrace : WordTrace (prefixWord ++ tailWord_607301) baseStart_607301 baseEnd_607301 := by
    simpa [prefixWord, tailWord_607301, baseEnd_607301] using wordTrace_append hprefix tailTrace_607301
  have hstable : (prefixWord ++ tailWord_607301).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_607301).length < 2 ^ (prefixWord ++ tailWord_607301).sum := by decide
  have hdescent : baseEnd_607301 < baseStart_607301 := by decide
  rcases family_descends (prefixWord ++ tailWord_607301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_607344 : List Nat := [2, 1, 1, 1, 5, 1, 1, 2, 3, 5]
def baseStart_607344 : Nat := 118140960795 + 607344 * 2 ^ 59
def prefixEnd_607344 : Nat := 4983230072969 + 3 ^ 40 * 607344 * 2
def baseEnd_607344 : Nat := 207906263082917998337921

theorem tailTrace_607344 : CollatzResearch.WordTrace tailWord_607344 prefixEnd_607344 207906263082917998337921 := by
  unfold tailWord_607344
  simp only [CollatzResearch.WordTrace]
  refine ⟨11075827755851944471126543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14767770341135925961502057 11075827755851944471126543)
  ·
    refine ⟨16613741633777916706689815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11075827755851944471126543 16613741633777916706689815)
    ·
      refine ⟨24920612450666875060034723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16613741633777916706689815 24920612450666875060034723)
      ·
        refine ⟨37380918676000312590052085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24920612450666875060034723 37380918676000312590052085)
        ·
          refine ⟨3504461125875029305317383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 37380918676000312590052085 3504461125875029305317383)
          ·
            refine ⟨5256691688812543957976075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3504461125875029305317383 5256691688812543957976075)
            ·
              refine ⟨7885037533218815936964113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5256691688812543957976075 7885037533218815936964113)
              ·
                refine ⟨5913778149914111952723085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7885037533218815936964113 5913778149914111952723085)
                ·
                  refine ⟨2217666806217791982271157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5913778149914111952723085 2217666806217791982271157)
                  ·
                    refine ⟨207906263082917998337921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2217666806217791982271157 207906263082917998337921)
                    ·
                      rfl

theorem cell22_607344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 1, 2, 3, 5].length) (baseStart_607344 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_607344 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_607344 prefixEnd_607344 := by exact prefixLift 607344
  have htrace : WordTrace (prefixWord ++ tailWord_607344) baseStart_607344 baseEnd_607344 := by
    simpa [prefixWord, tailWord_607344, baseEnd_607344] using wordTrace_append hprefix tailTrace_607344
  have hstable : (prefixWord ++ tailWord_607344).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_607344).length < 2 ^ (prefixWord ++ tailWord_607344).sum := by decide
  have hdescent : baseEnd_607344 < baseStart_607344 := by decide
  rcases family_descends (prefixWord ++ tailWord_607344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_607361 : List Nat := [1, 2, 4, 2, 2, 1, 1, 3, 1, 5]
def baseStart_607361 : Nat := 118140960795 + 607361 * 2 ^ 59
def prefixEnd_607361 : Nat := 4983230072969 + 3 ^ 40 * 607361 * 2
def baseEnd_607361 : Nat := 207912082530335620662869

theorem tailTrace_607361 : CollatzResearch.WordTrace tailWord_607361 prefixEnd_607361 207912082530335620662869 := by
  unfold tailWord_607361
  simp only [CollatzResearch.WordTrace]
  refine ⟨22152275552642300845621937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14768183701761533897081291 22152275552642300845621937)
  ·
    refine ⟨16614206664481725634216453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22152275552642300845621937 16614206664481725634216453)
    ·
      refine ⟨3115163749590323556415585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 16614206664481725634216453 3115163749590323556415585)
      ·
        refine ⟨2336372812192742667311689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3115163749590323556415585 2336372812192742667311689)
        ·
          refine ⟨1752279609144557000483767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2336372812192742667311689 1752279609144557000483767)
          ·
            refine ⟨2628419413716835500725651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1752279609144557000483767 2628419413716835500725651)
            ·
              refine ⟨3942629120575253251088477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2628419413716835500725651 3942629120575253251088477)
              ·
                refine ⟨1478485920215719969158179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3942629120575253251088477 1478485920215719969158179)
                ·
                  refine ⟨2217728880323579953737269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1478485920215719969158179 2217728880323579953737269)
                  ·
                    refine ⟨207912082530335620662869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2217728880323579953737269 207912082530335620662869)
                    ·
                      rfl

theorem cell22_607361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 1, 3, 1, 5].length) (baseStart_607361 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_607361 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_607361 prefixEnd_607361 := by exact prefixLift 607361
  have htrace : WordTrace (prefixWord ++ tailWord_607361) baseStart_607361 baseEnd_607361 := by
    simpa [prefixWord, tailWord_607361, baseEnd_607361] using wordTrace_append hprefix tailTrace_607361
  have hstable : (prefixWord ++ tailWord_607361).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_607361).length < 2 ^ (prefixWord ++ tailWord_607361).sum := by decide
  have hdescent : baseEnd_607361 < baseStart_607361 := by decide
  rcases family_descends (prefixWord ++ tailWord_607361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_607391 : List Nat := [1, 1, 2, 6, 2, 1, 9]
def baseStart_607391 : Nat := 118140960795 + 607391 * 2 ^ 59
def prefixEnd_607391 : Nat := 4983230072969 + 3 ^ 40 * 607391 * 2
def baseEnd_607391 : Nat := 7700827857163908978251

theorem tailTrace_607391 : CollatzResearch.WordTrace tailWord_607391 prefixEnd_607391 7700827857163908978251 := by
  unfold tailWord_607391
  simp only [CollatzResearch.WordTrace]
  refine ⟨22153369742533615969214027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14768913161689077312809351 22153369742533615969214027)
  ·
    refine ⟨33230054613800423953821041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22153369742533615969214027 33230054613800423953821041)
    ·
      refine ⟨24922540960350317965365781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33230054613800423953821041 24922540960350317965365781)
      ·
        refine ⟨1168244107516421154626521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 24922540960350317965365781 1168244107516421154626521)
        ·
          refine ⟨876183080637315865969891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1168244107516421154626521 876183080637315865969891)
          ·
            refine ⟨1314274620955973798954837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 876183080637315865969891 1314274620955973798954837)
            ·
              refine ⟨7700827857163908978251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 1314274620955973798954837 7700827857163908978251)
              ·
                rfl

theorem cell22_607391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 1, 9].length) (baseStart_607391 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_607391 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_607391 prefixEnd_607391 := by exact prefixLift 607391
  have htrace : WordTrace (prefixWord ++ tailWord_607391) baseStart_607391 baseEnd_607391 := by
    simpa [prefixWord, tailWord_607391, baseEnd_607391] using wordTrace_append hprefix tailTrace_607391
  have hstable : (prefixWord ++ tailWord_607391).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_607391).length < 2 ^ (prefixWord ++ tailWord_607391).sum := by decide
  have hdescent : baseEnd_607391 < baseStart_607391 := by decide
  rcases family_descends (prefixWord ++ tailWord_607391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_607404 : List Nat := [2, 2, 1, 1, 1, 1, 1, 5, 2, 6]
def baseStart_607404 : Nat := 118140960795 + 607404 * 2 ^ 59
def prefixEnd_607404 : Nat := 4983230072969 + 3 ^ 40 * 607404 * 2
def baseEnd_607404 : Nat := 207926802309097841837737

theorem tailTrace_607404 : CollatzResearch.WordTrace tailWord_607404 prefixEnd_607404 207926802309097841837737 := by
  unfold tailWord_607404
  simp only [CollatzResearch.WordTrace]
  refine ⟨11076921945743259594718633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14769229260991012792958177 11076921945743259594718633)
  ·
    refine ⟨8307691459307444696038975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11076921945743259594718633 8307691459307444696038975)
    ·
      refine ⟨12461537188961167044058463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8307691459307444696038975 12461537188961167044058463)
      ·
        refine ⟨18692305783441750566087695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12461537188961167044058463 18692305783441750566087695)
        ·
          refine ⟨28038458675162625849131543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18692305783441750566087695 28038458675162625849131543)
          ·
            refine ⟨42057688012743938773697315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28038458675162625849131543 42057688012743938773697315)
            ·
              refine ⟨63086532019115908160545973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42057688012743938773697315 63086532019115908160545973)
              ·
                refine ⟨5914362376792116390051185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 63086532019115908160545973 5914362376792116390051185)
                ·
                  refine ⟨4435771782594087292538389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5914362376792116390051185 4435771782594087292538389)
                  ·
                    refine ⟨207926802309097841837737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4435771782594087292538389 207926802309097841837737)
                    ·
                      rfl

theorem cell22_607404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 6].length) (baseStart_607404 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_607404 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_607404 prefixEnd_607404 := by exact prefixLift 607404
  have htrace : WordTrace (prefixWord ++ tailWord_607404) baseStart_607404 baseEnd_607404 := by
    simpa [prefixWord, tailWord_607404, baseEnd_607404] using wordTrace_append hprefix tailTrace_607404
  have hstable : (prefixWord ++ tailWord_607404).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_607404).length < 2 ^ (prefixWord ++ tailWord_607404).sum := by decide
  have hdescent : baseEnd_607404 < baseStart_607404 := by decide
  rcases family_descends (prefixWord ++ tailWord_607404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_607425 : List Nat := [1, 2, 6, 1, 1, 3, 2, 6]
def baseStart_607425 : Nat := 118140960795 + 607425 * 2 ^ 59
def prefixEnd_607425 : Nat := 4983230072969 + 3 ^ 40 * 607425 * 2
def baseEnd_607425 : Nat := 23103776782028976340297

theorem tailTrace_607425 : CollatzResearch.WordTrace tailWord_607425 prefixEnd_607425 23103776782028976340297 := by
  unfold tailWord_607425
  simp only [CollatzResearch.WordTrace]
  refine ⟨22154609824410439775951729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14769739882940293183967819 22154609824410439775951729)
  ·
    refine ⟨16615957368307829831963797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22154609824410439775951729 16615957368307829831963797)
    ·
      refine ⟨778873001639429523373303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 16615957368307829831963797 778873001639429523373303)
      ·
        refine ⟨1168309502459144285059955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 778873001639429523373303 1168309502459144285059955)
        ·
          refine ⟨1752464253688716427589933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1168309502459144285059955 1752464253688716427589933)
          ·
            refine ⟨657174095133268660346225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1752464253688716427589933 657174095133268660346225)
            ·
              refine ⟨492880571349951495259669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 657174095133268660346225 492880571349951495259669)
              ·
                refine ⟨23103776782028976340297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 492880571349951495259669 23103776782028976340297)
                ·
                  rfl

theorem cell22_607425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 3, 2, 6].length) (baseStart_607425 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_607425 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_607425 prefixEnd_607425 := by exact prefixLift 607425
  have htrace : WordTrace (prefixWord ++ tailWord_607425) baseStart_607425 baseEnd_607425 := by
    simpa [prefixWord, tailWord_607425, baseEnd_607425] using wordTrace_append hprefix tailTrace_607425
  have hstable : (prefixWord ++ tailWord_607425).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_607425).length < 2 ^ (prefixWord ++ tailWord_607425).sum := by decide
  have hdescent : baseEnd_607425 < baseStart_607425 := by decide
  rcases family_descends (prefixWord ++ tailWord_607425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_607457 : List Nat := [1, 2, 3, 1, 3, 3, 3, 2, 1, 3]
def baseStart_607457 : Nat := 118140960795 + 607457 * 2 ^ 59
def prefixEnd_607457 : Nat := 4983230072969 + 3 ^ 40 * 607457 * 2
def baseEnd_607457 : Nat := 207944945292223370262575

theorem tailTrace_607457 : CollatzResearch.WordTrace tailWord_607457 prefixEnd_607457 207944945292223370262575 := by
  unfold tailWord_607457
  simp only [CollatzResearch.WordTrace]
  refine ⟨22155776960294509241116625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14770517973529672827411083 22155776960294509241116625)
  ·
    refine ⟨16616832720220881930837469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22155776960294509241116625 16616832720220881930837469)
    ·
      refine ⟨6231312270082830724064051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16616832720220881930837469 6231312270082830724064051)
      ·
        refine ⟨9346968405124246086096077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6231312270082830724064051 9346968405124246086096077)
        ·
          refine ⟨3505113151921592282286029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9346968405124246086096077 3505113151921592282286029)
          ·
            refine ⟨1314417431970597105857261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3505113151921592282286029 1314417431970597105857261)
            ·
              refine ⟨492906536988973914696473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1314417431970597105857261 492906536988973914696473)
              ·
                refine ⟨369679902741730436022355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 492906536988973914696473 369679902741730436022355)
                ·
                  refine ⟨554519854112595654033533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 369679902741730436022355 554519854112595654033533)
                  ·
                    refine ⟨207944945292223370262575, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 554519854112595654033533 207944945292223370262575)
                    ·
                      rfl

theorem cell22_607457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 3, 3, 2, 1, 3].length) (baseStart_607457 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_607457 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_607457 prefixEnd_607457 := by exact prefixLift 607457
  have htrace : WordTrace (prefixWord ++ tailWord_607457) baseStart_607457 baseEnd_607457 := by
    simpa [prefixWord, tailWord_607457, baseEnd_607457] using wordTrace_append hprefix tailTrace_607457
  have hstable : (prefixWord ++ tailWord_607457).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_607457).length < 2 ^ (prefixWord ++ tailWord_607457).sum := by decide
  have hdescent : baseEnd_607457 < baseStart_607457 := by decide
  rcases family_descends (prefixWord ++ tailWord_607457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_607498 : List Nat := [3, 1, 2, 2, 1, 1, 1, 7, 4]
def baseStart_607498 : Nat := 118140960795 + 607498 * 2 ^ 59
def prefixEnd_607498 : Nat := 4983230072969 + 3 ^ 40 * 607498 * 2
def baseEnd_607498 : Nat := 69319660143370976662483

theorem tailTrace_607498 : CollatzResearch.WordTrace tailWord_607498 prefixEnd_607498 69319660143370976662483 := by
  unfold tailWord_607498
  simp only [CollatzResearch.WordTrace]
  refine ⟨5539318088286493310839787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14771514902097315495572765 5539318088286493310839787)
  ·
    refine ⟨8308977132429739966259681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5539318088286493310839787 8308977132429739966259681)
    ·
      refine ⟨6231732849322304974694761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8308977132429739966259681 6231732849322304974694761)
      ·
        refine ⟨4673799636991728731021071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6231732849322304974694761 4673799636991728731021071)
        ·
          refine ⟨7010699455487593096531607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4673799636991728731021071 7010699455487593096531607)
          ·
            refine ⟨10516049183231389644797411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7010699455487593096531607 10516049183231389644797411)
            ·
              refine ⟨15774073774847084467196117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10516049183231389644797411 15774073774847084467196117)
              ·
                refine ⟨369704854097978542199909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 15774073774847084467196117 369704854097978542199909)
                ·
                  refine ⟨69319660143370976662483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 369704854097978542199909 69319660143370976662483)
                  ·
                    rfl

theorem cell22_607498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 7, 4].length) (baseStart_607498 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_607498 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_607498 prefixEnd_607498 := by exact prefixLift 607498
  have htrace : WordTrace (prefixWord ++ tailWord_607498) baseStart_607498 baseEnd_607498 := by
    simpa [prefixWord, tailWord_607498, baseEnd_607498] using wordTrace_append hprefix tailTrace_607498
  have hstable : (prefixWord ++ tailWord_607498).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_607498).length < 2 ^ (prefixWord ++ tailWord_607498).sum := by decide
  have hdescent : baseEnd_607498 < baseStart_607498 := by decide
  rcases family_descends (prefixWord ++ tailWord_607498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_607500 : List Nat := [2, 2, 1, 2, 2, 4, 3, 1, 1, 4]
def baseStart_607500 : Nat := 118140960795 + 607500 * 2 ^ 59
def prefixEnd_607500 : Nat := 4983230072969 + 3 ^ 40 * 607500 * 2
def baseEnd_607500 : Nat := 207959665070985591437443

theorem tailTrace_607500 : CollatzResearch.WordTrace tailWord_607500 prefixEnd_607500 207959665070985591437443 := by
  unfold tailWord_607500
  simp only [CollatzResearch.WordTrace]
  refine ⟨11078672649569363792465977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14771563532759151723287969 11078672649569363792465977)
  ·
    refine ⟨8309004487177022844349483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11078672649569363792465977 8309004487177022844349483)
    ·
      refine ⟨12463506730765534266524225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8309004487177022844349483 12463506730765534266524225)
      ·
        refine ⟨9347630048074150699893169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12463506730765534266524225 9347630048074150699893169)
        ·
          refine ⟨7010722536055613024919877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9347630048074150699893169 7010722536055613024919877)
          ·
            refine ⟨1314510475510427442172477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7010722536055613024919877 1314510475510427442172477)
            ·
              refine ⟨492941428316410290814679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1314510475510427442172477 492941428316410290814679)
              ·
                refine ⟨739412142474615436222019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 492941428316410290814679 739412142474615436222019)
                ·
                  refine ⟨1109118213711923154333029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 739412142474615436222019 1109118213711923154333029)
                  ·
                    refine ⟨207959665070985591437443, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1109118213711923154333029 207959665070985591437443)
                    ·
                      rfl

theorem cell22_607500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 4, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 4, 3, 1, 1, 4].length) (baseStart_607500 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_607500 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_607500 prefixEnd_607500 := by exact prefixLift 607500
  have htrace : WordTrace (prefixWord ++ tailWord_607500) baseStart_607500 baseEnd_607500 := by
    simpa [prefixWord, tailWord_607500, baseEnd_607500] using wordTrace_append hprefix tailTrace_607500
  have hstable : (prefixWord ++ tailWord_607500).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_607500).length < 2 ^ (prefixWord ++ tailWord_607500).sum := by decide
  have hdescent : baseEnd_607500 < baseStart_607500 := by decide
  rcases family_descends (prefixWord ++ tailWord_607500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_607530 : List Nat := [3, 1, 4, 2, 1, 2, 2, 1, 1, 5]
def baseStart_607530 : Nat := 118140960795 + 607530 * 2 ^ 59
def prefixEnd_607530 : Nat := 4983230072969 + 3 ^ 40 * 607530 * 2
def baseEnd_607530 : Nat := 207969934684075513187351

theorem tailTrace_607530 : CollatzResearch.WordTrace tailWord_607530 prefixEnd_607530 207969934684075513187351 := by
  unfold tailWord_607530
  simp only [CollatzResearch.WordTrace]
  refine ⟨5539609872257510677131011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14772292992686695139016029 5539609872257510677131011)
  ·
    refine ⟨8309414808386266015696517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5539609872257510677131011 8309414808386266015696517)
    ·
      refine ⟨1558015276572424877943097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8309414808386266015696517 1558015276572424877943097)
      ·
        refine ⟨1168511457429318658457323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1558015276572424877943097 1168511457429318658457323)
        ·
          refine ⟨1752767186143977987685985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1168511457429318658457323 1752767186143977987685985)
          ·
            refine ⟨1314575389607983490764489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1752767186143977987685985 1314575389607983490764489)
            ·
              refine ⟨985931542205987618073367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1314575389607983490764489 985931542205987618073367)
              ·
                refine ⟨1478897313308981427110051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 985931542205987618073367 1478897313308981427110051)
                ·
                  refine ⟨2218345969963472140665077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1478897313308981427110051 2218345969963472140665077)
                  ·
                    refine ⟨207969934684075513187351, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2218345969963472140665077 207969934684075513187351)
                    ·
                      rfl

theorem cell22_607530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 2, 2, 1, 1, 5].length) (baseStart_607530 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_607530 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_607530 prefixEnd_607530 := by exact prefixLift 607530
  have htrace : WordTrace (prefixWord ++ tailWord_607530) baseStart_607530 baseEnd_607530 := by
    simpa [prefixWord, tailWord_607530, baseEnd_607530] using wordTrace_append hprefix tailTrace_607530
  have hstable : (prefixWord ++ tailWord_607530).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_607530).length < 2 ^ (prefixWord ++ tailWord_607530).sum := by decide
  have hdescent : baseEnd_607530 < baseStart_607530 := by decide
  rcases family_descends (prefixWord ++ tailWord_607530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_607571 : List Nat := [1, 1, 1, 2, 1, 1, 7, 1, 7]
def baseStart_607571 : Nat := 118140960795 + 607571 * 2 ^ 59
def prefixEnd_607571 : Nat := 4983230072969 + 3 ^ 40 * 607571 * 2
def baseEnd_607571 : Nat := 69327989940655024304075

theorem tailTrace_607571 : CollatzResearch.WordTrace tailWord_607571 prefixEnd_607571 69327989940655024304075 := by
  unfold tailWord_607571
  simp only [CollatzResearch.WordTrace]
  refine ⟨22159934881881506710766567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14773289921254337807177711 22159934881881506710766567)
  ·
    refine ⟨33239902322822260066149851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22159934881881506710766567 33239902322822260066149851)
    ·
      refine ⟨49859853484233390099224777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33239902322822260066149851 49859853484233390099224777)
      ·
        refine ⟨37394890113175042574418583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49859853484233390099224777 37394890113175042574418583)
        ·
          refine ⟨56092335169762563861627875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37394890113175042574418583 56092335169762563861627875)
          ·
            refine ⟨84138502754643845792441813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56092335169762563861627875 84138502754643845792441813)
            ·
              refine ⟨1971996158311965135760355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 84138502754643845792441813 1971996158311965135760355)
              ·
                refine ⟨2957994237467947703640533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1971996158311965135760355 2957994237467947703640533)
                ·
                  refine ⟨69327989940655024304075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2957994237467947703640533 69327989940655024304075)
                  ·
                    rfl

theorem cell22_607571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 7, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 7, 1, 7].length) (baseStart_607571 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_607571 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_607571 prefixEnd_607571 := by exact prefixLift 607571
  have htrace : WordTrace (prefixWord ++ tailWord_607571) baseStart_607571 baseEnd_607571 := by
    simpa [prefixWord, tailWord_607571, baseEnd_607571] using wordTrace_append hprefix tailTrace_607571
  have hstable : (prefixWord ++ tailWord_607571).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_607571).length < 2 ^ (prefixWord ++ tailWord_607571).sum := by decide
  have hdescent : baseEnd_607571 < baseStart_607571 := by decide
  rcases family_descends (prefixWord ++ tailWord_607571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_607575 : List Nat := [1, 1, 3, 2, 3, 3, 2, 1, 3, 3]
def baseStart_607575 : Nat := 118140960795 + 607575 * 2 ^ 59
def prefixEnd_607575 : Nat := 4983230072969 + 3 ^ 40 * 607575 * 2
def baseEnd_607575 : Nat := 207985339103710395812213

theorem tailTrace_607575 : CollatzResearch.WordTrace tailWord_607575 prefixEnd_607575 207985339103710395812213 := by
  unfold tailWord_607575
  simp only [CollatzResearch.WordTrace]
  refine ⟨22160080773867015393912179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14773387182578010262608119 22160080773867015393912179)
  ·
    refine ⟨33240121160800523090868269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22160080773867015393912179 33240121160800523090868269)
    ·
      refine ⟨12465045435300196159075601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33240121160800523090868269 12465045435300196159075601)
      ·
        refine ⟨9348784076475147119306701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12465045435300196159075601 9348784076475147119306701)
        ·
          refine ⟨3505794028678180169740013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9348784076475147119306701 3505794028678180169740013)
          ·
            refine ⟨1314672760754317563652505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3505794028678180169740013 1314672760754317563652505)
            ·
              refine ⟨986004570565738172739379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1314672760754317563652505 986004570565738172739379)
              ·
                refine ⟨1479006855848607259109069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 986004570565738172739379 1479006855848607259109069)
                ·
                  refine ⟨554627570943227722165901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1479006855848607259109069 554627570943227722165901)
                  ·
                    refine ⟨207985339103710395812213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 554627570943227722165901 207985339103710395812213)
                    ·
                      rfl

theorem cell22_607575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 3, 2, 1, 3, 3].length) (baseStart_607575 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_607575 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_607575 prefixEnd_607575 := by exact prefixLift 607575
  have htrace : WordTrace (prefixWord ++ tailWord_607575) baseStart_607575 baseEnd_607575 := by
    simpa [prefixWord, tailWord_607575, baseEnd_607575] using wordTrace_append hprefix tailTrace_607575
  have hstable : (prefixWord ++ tailWord_607575).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_607575).length < 2 ^ (prefixWord ++ tailWord_607575).sum := by decide
  have hdescent : baseEnd_607575 < baseStart_607575 := by decide
  rcases family_descends (prefixWord ++ tailWord_607575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_607581 : List Nat := [1, 4, 5, 1, 2, 1, 1, 1, 1, 5]
def baseStart_607581 : Nat := 118140960795 + 607581 * 2 ^ 59
def prefixEnd_607581 : Nat := 4983230072969 + 3 ^ 40 * 607581 * 2
def baseEnd_607581 : Nat := 207987393026328380162195

theorem tailTrace_607581 : CollatzResearch.WordTrace tailWord_607581 prefixEnd_607581 207987393026328380162195 := by
  unfold tailWord_607581
  simp only [CollatzResearch.WordTrace]
  refine ⟨22160299611845278418630597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14773533074563518945753731 22160299611845278418630597)
  ·
    refine ⟨4155056177220989703493237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 22160299611845278418630597 4155056177220989703493237)
    ·
      refine ⟨389536516614467784702491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 4155056177220989703493237 389536516614467784702491)
      ·
        refine ⟨584304774921701677053737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 389536516614467784702491 584304774921701677053737)
        ·
          refine ⟨438228581191276257790303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 584304774921701677053737 438228581191276257790303)
          ·
            refine ⟨657342871786914386685455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 438228581191276257790303 657342871786914386685455)
            ·
              refine ⟨986014307680371580028183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 657342871786914386685455 986014307680371580028183)
              ·
                refine ⟨1479021461520557370042275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 986014307680371580028183 1479021461520557370042275)
                ·
                  refine ⟨2218532192280836055063413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1479021461520557370042275 2218532192280836055063413)
                  ·
                    refine ⟨207987393026328380162195, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2218532192280836055063413 207987393026328380162195)
                    ·
                      rfl

theorem cell22_607581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 2, 1, 1, 1, 1, 5].length) (baseStart_607581 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_607581 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_607581 prefixEnd_607581 := by exact prefixLift 607581
  have htrace : WordTrace (prefixWord ++ tailWord_607581) baseStart_607581 baseEnd_607581 := by
    simpa [prefixWord, tailWord_607581, baseEnd_607581] using wordTrace_append hprefix tailTrace_607581
  have hstable : (prefixWord ++ tailWord_607581).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_607581).length < 2 ^ (prefixWord ++ tailWord_607581).sum := by decide
  have hdescent : baseEnd_607581 < baseStart_607581 := by decide
  rcases family_descends (prefixWord ++ tailWord_607581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_607616 : List Nat := [2, 1, 1, 2, 1, 2, 1, 4, 8]
def baseStart_607616 : Nat := 118140960795 + 607616 * 2 ^ 59
def prefixEnd_607616 : Nat := 4983230072969 + 3 ^ 40 * 607616 * 2
def baseEnd_607616 : Nat := 69333124747199985179029

theorem tailTrace_607616 : CollatzResearch.WordTrace tailWord_607616 prefixEnd_607616 69333124747199985179029 := by
  unfold tailWord_607616
  simp only [CollatzResearch.WordTrace]
  refine ⟨11080788083359239698077351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14774384111145652930769801 11080788083359239698077351)
  ·
    refine ⟨16621182125038859547116027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11080788083359239698077351 16621182125038859547116027)
    ·
      refine ⟨24931773187558289320674041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16621182125038859547116027 24931773187558289320674041)
      ·
        refine ⟨18698829890668716990505531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24931773187558289320674041 18698829890668716990505531)
        ·
          refine ⟨28048244836003075485758297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18698829890668716990505531 28048244836003075485758297)
          ·
            refine ⟨21036183627002306614318723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28048244836003075485758297 21036183627002306614318723)
            ·
              refine ⟨31554275440503459921478085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21036183627002306614318723 31554275440503459921478085)
              ·
                refine ⟨5916426645094398735277141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 31554275440503459921478085 5916426645094398735277141)
                ·
                  refine ⟨69333124747199985179029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 5916426645094398735277141 69333124747199985179029)
                  ·
                    rfl

theorem cell22_607616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 4, 8].length) (baseStart_607616 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_607616 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_607616 prefixEnd_607616 := by exact prefixLift 607616
  have htrace : WordTrace (prefixWord ++ tailWord_607616) baseStart_607616 baseEnd_607616 := by
    simpa [prefixWord, tailWord_607616, baseEnd_607616] using wordTrace_append hprefix tailTrace_607616
  have hstable : (prefixWord ++ tailWord_607616).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_607616).length < 2 ^ (prefixWord ++ tailWord_607616).sum := by decide
  have hdescent : baseEnd_607616 < baseStart_607616 := by decide
  rcases family_descends (prefixWord ++ tailWord_607616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_607648 : List Nat := [2, 1, 1, 4, 1, 2, 2, 3, 1, 5]
def baseStart_607648 : Nat := 118140960795 + 607648 * 2 ^ 59
def prefixEnd_607648 : Nat := 4983230072969 + 3 ^ 40 * 607648 * 2
def baseEnd_607648 : Nat := 208010328495562538736989

theorem tailTrace_607648 : CollatzResearch.WordTrace tailWord_607648 prefixEnd_607648 208010328495562538736989 := by
  unfold tailWord_607648
  simp only [CollatzResearch.WordTrace]
  refine ⟨11081371651301274430659799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14775162201735032574213065 11081371651301274430659799)
  ·
    refine ⟨16622057476951911645989699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11081371651301274430659799 16622057476951911645989699)
    ·
      refine ⟨24933086215427867468984549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16622057476951911645989699 24933086215427867468984549)
      ·
        refine ⟨4674953665392725150434603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 24933086215427867468984549 4674953665392725150434603)
        ·
          refine ⟨7012430498089087725651905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4674953665392725150434603 7012430498089087725651905)
          ·
            refine ⟨5259322873566815794238929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7012430498089087725651905 5259322873566815794238929)
            ·
              refine ⟨3944492155175111845679197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5259322873566815794238929 3944492155175111845679197)
              ·
                refine ⟨1479184558190666942129699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3944492155175111845679197 1479184558190666942129699)
                ·
                  refine ⟨2218776837286000413194549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1479184558190666942129699 2218776837286000413194549)
                  ·
                    refine ⟨208010328495562538736989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2218776837286000413194549 208010328495562538736989)
                    ·
                      rfl

theorem cell22_607648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 2, 3, 1, 5].length) (baseStart_607648 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_607648 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_607648 prefixEnd_607648 := by exact prefixLift 607648
  have htrace : WordTrace (prefixWord ++ tailWord_607648) baseStart_607648 baseEnd_607648 := by
    simpa [prefixWord, tailWord_607648, baseEnd_607648] using wordTrace_append hprefix tailTrace_607648
  have hstable : (prefixWord ++ tailWord_607648).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_607648).length < 2 ^ (prefixWord ++ tailWord_607648).sum := by decide
  have hdescent : baseEnd_607648 < baseStart_607648 := by decide
  rcases family_descends (prefixWord ++ tailWord_607648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_607684 : List Nat := [2, 3, 3, 2, 1, 1, 4, 2, 4]
def baseStart_607684 : Nat := 118140960795 + 607684 * 2 ^ 59
def prefixEnd_607684 : Nat := 4983230072969 + 3 ^ 40 * 607684 * 2
def baseEnd_607684 : Nat := 69340884010423481612293

theorem tailTrace_607684 : CollatzResearch.WordTrace tailWord_607684 prefixEnd_607684 69340884010423481612293 := by
  unfold tailWord_607684
  simp only [CollatzResearch.WordTrace]
  refine ⟨11082028165236063504815053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14776037553648084673086737 11082028165236063504815053)
  ·
    refine ⟨4155760561963523814305645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11082028165236063504815053 4155760561963523814305645)
    ·
      refine ⟨1558410210736321430364617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4155760561963523814305645 1558410210736321430364617)
      ·
        refine ⟨1168807658052241072773463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1558410210736321430364617 1168807658052241072773463)
        ·
          refine ⟨1753211487078361609160195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1168807658052241072773463 1753211487078361609160195)
          ·
            refine ⟨2629817230617542413740293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1753211487078361609160195 2629817230617542413740293)
            ·
              refine ⟨493090730740789202576305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2629817230617542413740293 493090730740789202576305)
              ·
                refine ⟨369818048055591901932229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 493090730740789202576305 369818048055591901932229)
                ·
                  refine ⟨69340884010423481612293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 369818048055591901932229 69340884010423481612293)
                  ·
                    rfl

theorem cell22_607684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 4, 2, 4].length) (baseStart_607684 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_607684 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_607684 prefixEnd_607684 := by exact prefixLift 607684
  have htrace : WordTrace (prefixWord ++ tailWord_607684) baseStart_607684 baseEnd_607684 := by
    simpa [prefixWord, tailWord_607684, baseEnd_607684] using wordTrace_append hprefix tailTrace_607684
  have hstable : (prefixWord ++ tailWord_607684).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_607684).length < 2 ^ (prefixWord ++ tailWord_607684).sum := by decide
  have hdescent : baseEnd_607684 < baseStart_607684 := by decide
  rcases family_descends (prefixWord ++ tailWord_607684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_607727 : List Nat := [1, 1, 2, 1, 4, 1, 3, 5, 1, 3]
def baseStart_607727 : Nat := 118140960795 + 607727 * 2 ^ 59
def prefixEnd_607727 : Nat := 4983230072969 + 3 ^ 40 * 607727 * 2
def baseEnd_607727 : Nat := 208037371810032666011747

theorem tailTrace_607727 : CollatzResearch.WordTrace tailWord_607727 prefixEnd_607727 208037371810032666011747 := by
  unfold tailWord_607727
  simp only [CollatzResearch.WordTrace]
  refine ⟨22165624669316345353445435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14777083112877563568963623 22165624669316345353445435)
  ·
    refine ⟨33248437003974518030168153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22165624669316345353445435 33248437003974518030168153)
    ·
      refine ⟨24936327752980888522626115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33248437003974518030168153 24936327752980888522626115)
      ·
        refine ⟨37404491629471332783939173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24936327752980888522626115 37404491629471332783939173)
        ·
          refine ⟨7013342180525874896988595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 37404491629471332783939173 7013342180525874896988595)
          ·
            refine ⟨10520013270788812345482893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7013342180525874896988595 10520013270788812345482893)
            ·
              refine ⟨3945004976545804629556085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10520013270788812345482893 3945004976545804629556085)
              ·
                refine ⟨369844216551169184020883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3945004976545804629556085 369844216551169184020883)
                ·
                  refine ⟨554766324826753776031325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 369844216551169184020883 554766324826753776031325)
                  ·
                    refine ⟨208037371810032666011747, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 554766324826753776031325 208037371810032666011747)
                    ·
                      rfl

theorem cell22_607727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 3, 5, 1, 3].length) (baseStart_607727 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_607727 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_607727 prefixEnd_607727 := by exact prefixLift 607727
  have htrace : WordTrace (prefixWord ++ tailWord_607727) baseStart_607727 baseEnd_607727 := by
    simpa [prefixWord, tailWord_607727, baseEnd_607727] using wordTrace_append hprefix tailTrace_607727
  have hstable : (prefixWord ++ tailWord_607727).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_607727).length < 2 ^ (prefixWord ++ tailWord_607727).sum := by decide
  have hdescent : baseEnd_607727 < baseStart_607727 := by decide
  rcases family_descends (prefixWord ++ tailWord_607727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_607738 : List Nat := [3, 1, 1, 1, 1, 2, 3, 1, 4, 5]
def baseStart_607738 : Nat := 118140960795 + 607738 * 2 ^ 59
def prefixEnd_607738 : Nat := 4983230072969 + 3 ^ 40 * 607738 * 2
def baseEnd_607738 : Nat := 208041137334832303986713

theorem tailTrace_607738 : CollatzResearch.WordTrace tailWord_607738 prefixEnd_607738 208041137334832303986713 := by
  unfold tailWord_607738
  simp only [CollatzResearch.WordTrace]
  refine ⟨5541506468069123558023967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14777350581517662821397245 5541506468069123558023967)
  ·
    refine ⟨8312259702103685337035951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5541506468069123558023967 8312259702103685337035951)
    ·
      refine ⟨12468389553155528005553927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8312259702103685337035951 12468389553155528005553927)
      ·
        refine ⟨18702584329733292008330891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12468389553155528005553927 18702584329733292008330891)
        ·
          refine ⟨28053876494599938012496337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18702584329733292008330891 28053876494599938012496337)
          ·
            refine ⟨21040407370949953509372253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28053876494599938012496337 21040407370949953509372253)
            ·
              refine ⟨7890152764106232566014595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21040407370949953509372253 7890152764106232566014595)
              ·
                refine ⟨11835229146159348849021893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7890152764106232566014595 11835229146159348849021893)
                ·
                  refine ⟨2219105464904877909191605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11835229146159348849021893 2219105464904877909191605)
                  ·
                    refine ⟨208041137334832303986713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2219105464904877909191605 208041137334832303986713)
                    ·
                      rfl

theorem cell22_607738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 3, 1, 4, 5].length) (baseStart_607738 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_607738 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_607738 prefixEnd_607738 := by exact prefixLift 607738
  have htrace : WordTrace (prefixWord ++ tailWord_607738) baseStart_607738 baseEnd_607738 := by
    simpa [prefixWord, tailWord_607738, baseEnd_607738] using wordTrace_append hprefix tailTrace_607738
  have hstable : (prefixWord ++ tailWord_607738).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_607738).length < 2 ^ (prefixWord ++ tailWord_607738).sum := by decide
  have hdescent : baseEnd_607738 < baseStart_607738 := by decide
  rcases family_descends (prefixWord ++ tailWord_607738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_607740 : List Nat := [2, 2, 2, 1, 2, 1, 5, 2, 5]
def baseStart_607740 : Nat := 118140960795 + 607740 * 2 ^ 59
def prefixEnd_607740 : Nat := 4983230072969 + 3 ^ 40 * 607740 * 2
def baseEnd_607740 : Nat := 69347273991901655145569

theorem tailTrace_607740 : CollatzResearch.WordTrace tailWord_607740 prefixEnd_607740 69347273991901655145569 := by
  unfold tailWord_607740
  simp only [CollatzResearch.WordTrace]
  refine ⟨11083049409134624286834337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14777399212179499049112449 11083049409134624286834337)
  ·
    refine ⟨8312287056850968215125753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11083049409134624286834337 8312287056850968215125753)
    ·
      refine ⟨6234215292638226161344315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8312287056850968215125753 6234215292638226161344315)
      ·
        refine ⟨9351322938957339242016473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6234215292638226161344315 9351322938957339242016473)
        ·
          refine ⟨7013492204218004431512355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9351322938957339242016473 7013492204218004431512355)
          ·
            refine ⟨10520238306327006647268533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7013492204218004431512355 10520238306327006647268533)
            ·
              refine ⟨986272341218156873181425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 10520238306327006647268533 986272341218156873181425)
              ·
                refine ⟨739704255913617654886069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 986272341218156873181425 739704255913617654886069)
                ·
                  refine ⟨69347273991901655145569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 739704255913617654886069 69347273991901655145569)
                  ·
                    rfl

theorem cell22_607740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 5, 2, 5].length) (baseStart_607740 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_607740 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_607740 prefixEnd_607740 := by exact prefixLift 607740
  have htrace : WordTrace (prefixWord ++ tailWord_607740) baseStart_607740 baseEnd_607740 := by
    simpa [prefixWord, tailWord_607740, baseEnd_607740] using wordTrace_append hprefix tailTrace_607740
  have hstable : (prefixWord ++ tailWord_607740).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_607740).length < 2 ^ (prefixWord ++ tailWord_607740).sum := by decide
  have hdescent : baseEnd_607740 < baseStart_607740 := by decide
  rcases family_descends (prefixWord ++ tailWord_607740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_607750 : List Nat := [6, 2, 1, 1, 2, 1, 3, 1, 2, 3]
def baseStart_607750 : Nat := 118140960795 + 607750 * 2 ^ 59
def prefixEnd_607750 : Nat := 4983230072969 + 3 ^ 40 * 607750 * 2
def baseEnd_607750 : Nat := 208045245180068272686677

theorem tailTrace_607750 : CollatzResearch.WordTrace tailWord_607750 prefixEnd_607750 208045245180068272686677 := by
  unfold tailWord_607750
  simp only [CollatzResearch.WordTrace]
  refine ⟨692701985882281883797897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 14777642365488680187688469 692701985882281883797897)
  ·
    refine ⟨519526489411711412848423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 692701985882281883797897 519526489411711412848423)
    ·
      refine ⟨779289734117567119272635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 519526489411711412848423 779289734117567119272635)
      ·
        refine ⟨1168934601176350678908953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 779289734117567119272635 1168934601176350678908953)
        ·
          refine ⟨876700950882263009181715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1168934601176350678908953 876700950882263009181715)
          ·
            refine ⟨1315051426323394513772573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 876700950882263009181715 1315051426323394513772573)
            ·
              refine ⟨493144284871272942664715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1315051426323394513772573 493144284871272942664715)
              ·
                refine ⟨739716427306909413997073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 493144284871272942664715 739716427306909413997073)
                ·
                  refine ⟨554787320480182060497805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 739716427306909413997073 554787320480182060497805)
                  ·
                    refine ⟨208045245180068272686677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 554787320480182060497805 208045245180068272686677)
                    ·
                      rfl

theorem cell22_607750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 1, 3, 1, 2, 3].length) (baseStart_607750 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_607750 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_607750 prefixEnd_607750 := by exact prefixLift 607750
  have htrace : WordTrace (prefixWord ++ tailWord_607750) baseStart_607750 baseEnd_607750 := by
    simpa [prefixWord, tailWord_607750, baseEnd_607750] using wordTrace_append hprefix tailTrace_607750
  have hstable : (prefixWord ++ tailWord_607750).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_607750).length < 2 ^ (prefixWord ++ tailWord_607750).sum := by decide
  have hdescent : baseEnd_607750 < baseStart_607750 := by decide
  rcases family_descends (prefixWord ++ tailWord_607750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_607821 : List Nat := [1, 6, 1, 1, 3, 2, 1, 2, 1, 4]
def baseStart_607821 : Nat := 118140960795 + 607821 * 2 ^ 59
def prefixEnd_607821 : Nat := 4983230072969 + 3 ^ 40 * 607821 * 2
def baseEnd_607821 : Nat := 208069549931047754161459

theorem tailTrace_607821 : CollatzResearch.WordTrace tailWord_607821 prefixEnd_607821 208069549931047754161459 := by
  unfold tailWord_607821
  simp only [CollatzResearch.WordTrace]
  refine ⟨22169053130975799407367317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14779368753983866271578211 22169053130975799407367317)
  ·
    refine ⟨1039174365514490597220343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 22169053130975799407367317 1039174365514490597220343)
    ·
      refine ⟨1558761548271735895830515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1039174365514490597220343 1558761548271735895830515)
      ·
        refine ⟨2338142322407603843745773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1558761548271735895830515 2338142322407603843745773)
        ·
          refine ⟨876803370902851441404665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2338142322407603843745773 876803370902851441404665)
          ·
            refine ⟨657602528177138581053499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 876803370902851441404665 657602528177138581053499)
            ·
              refine ⟨986403792265707871580249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 657602528177138581053499 986403792265707871580249)
              ·
                refine ⟨739802844199280903685187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 986403792265707871580249 739802844199280903685187)
                ·
                  refine ⟨1109704266298921355527781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 739802844199280903685187 1109704266298921355527781)
                  ·
                    refine ⟨208069549931047754161459, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1109704266298921355527781 208069549931047754161459)
                    ·
                      rfl

theorem cell22_607821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 2, 1, 2, 1, 4].length) (baseStart_607821 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_607821 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_607821 prefixEnd_607821 := by exact prefixLift 607821
  have htrace : WordTrace (prefixWord ++ tailWord_607821) baseStart_607821 baseEnd_607821 := by
    simpa [prefixWord, tailWord_607821, baseEnd_607821] using wordTrace_append hprefix tailTrace_607821
  have hstable : (prefixWord ++ tailWord_607821).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_607821).length < 2 ^ (prefixWord ++ tailWord_607821).sum := by decide
  have hdescent : baseEnd_607821 < baseStart_607821 := by decide
  rcases family_descends (prefixWord ++ tailWord_607821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_607853 : List Nat := [1, 5, 1, 1, 5, 1, 2, 2, 4]
def baseStart_607853 : Nat := 118140960795 + 607853 * 2 ^ 59
def prefixEnd_607853 : Nat := 4983230072969 + 3 ^ 40 * 607853 * 2
def baseEnd_607853 : Nat := 69360168061670112453787

theorem tailTrace_607853 : CollatzResearch.WordTrace tailWord_607853 prefixEnd_607853 69360168061670112453787 := by
  unfold tailWord_607853
  simp only [CollatzResearch.WordTrace]
  refine ⟨22170220266859868872532213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14780146844573245915021475 22170220266859868872532213)
  ·
    refine ⟨2078458150018112706799895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 22170220266859868872532213 2078458150018112706799895)
    ·
      refine ⟨3117687225027169060199843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2078458150018112706799895 3117687225027169060199843)
      ·
        refine ⟨4676530837540753590299765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3117687225027169060199843 4676530837540753590299765)
        ·
          refine ⟨438424766019445649090603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 4676530837540753590299765 438424766019445649090603)
          ·
            refine ⟨657637149029168473635905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 438424766019445649090603 657637149029168473635905)
            ·
              refine ⟨493227861771876355226929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 657637149029168473635905 493227861771876355226929)
              ·
                refine ⟨369920896328907266420197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 493227861771876355226929 369920896328907266420197)
                ·
                  refine ⟨69360168061670112453787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 369920896328907266420197 69360168061670112453787)
                  ·
                    rfl

theorem cell22_607853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 5, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 5, 1, 2, 2, 4].length) (baseStart_607853 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_607853 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_607853 prefixEnd_607853 := by exact prefixLift 607853
  have htrace : WordTrace (prefixWord ++ tailWord_607853) baseStart_607853 baseEnd_607853 := by
    simpa [prefixWord, tailWord_607853, baseEnd_607853] using wordTrace_append hprefix tailTrace_607853
  have hstable : (prefixWord ++ tailWord_607853).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_607853).length < 2 ^ (prefixWord ++ tailWord_607853).sum := by decide
  have hdescent : baseEnd_607853 < baseStart_607853 := by decide
  rcases family_descends (prefixWord ++ tailWord_607853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_607896 : List Nat := [2, 1, 2, 4, 1, 3, 2, 3, 1, 3]
def baseStart_607896 : Nat := 118140960795 + 607896 * 2 ^ 59
def prefixEnd_607896 : Nat := 4983230072969 + 3 ^ 40 * 607896 * 2
def baseEnd_607896 : Nat := 208095223963772558536229

theorem tailTrace_607896 : CollatzResearch.WordTrace tailWord_607896 prefixEnd_607896 208095223963772558536229 := by
  unfold tailWord_607896
  simp only [CollatzResearch.WordTrace]
  refine ⟨11085894302852043608173771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14781192403802724810898361 11085894302852043608173771)
  ·
    refine ⟨16628841454278065412260657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11085894302852043608173771 16628841454278065412260657)
    ·
      refine ⟨12471631090708549059195493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16628841454278065412260657 12471631090708549059195493)
      ·
        refine ⟨2338430829507852948599155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12471631090708549059195493 2338430829507852948599155)
        ·
          refine ⟨3507646244261779422898733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2338430829507852948599155 3507646244261779422898733)
          ·
            refine ⟨1315367341598167283587025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3507646244261779422898733 1315367341598167283587025)
            ·
              refine ⟨986525506198625462690269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1315367341598167283587025 986525506198625462690269)
              ·
                refine ⟨369947064824484548508851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 986525506198625462690269 369947064824484548508851)
                ·
                  refine ⟨554920597236726822763277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 369947064824484548508851 554920597236726822763277)
                  ·
                    refine ⟨208095223963772558536229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 554920597236726822763277 208095223963772558536229)
                    ·
                      rfl

theorem cell22_607896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 3, 2, 3, 1, 3].length) (baseStart_607896 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_607896 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_607896 prefixEnd_607896 := by exact prefixLift 607896
  have htrace : WordTrace (prefixWord ++ tailWord_607896) baseStart_607896 baseEnd_607896 := by
    simpa [prefixWord, tailWord_607896, baseEnd_607896] using wordTrace_append hprefix tailTrace_607896
  have hstable : (prefixWord ++ tailWord_607896).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_607896).length < 2 ^ (prefixWord ++ tailWord_607896).sum := by decide
  have hdescent : baseEnd_607896 < baseStart_607896 := by decide
  rcases family_descends (prefixWord ++ tailWord_607896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_607920 : List Nat := [2, 1, 1, 1, 2, 1, 5, 3, 6]
def baseStart_607920 : Nat := 118140960795 + 607920 * 2 ^ 59
def prefixEnd_607920 : Nat := 4983230072969 + 3 ^ 40 * 607920 * 2
def baseEnd_607920 : Nat := 69367813218081498645385

theorem tailTrace_607920 : CollatzResearch.WordTrace tailWord_607920 prefixEnd_607920 69367813218081498645385 := by
  unfold tailWord_607920
  simp only [CollatzResearch.WordTrace]
  refine ⟨11086331978808569657610607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14781775971744759543480809 11086331978808569657610607)
  ·
    refine ⟨16629497968212854486415911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11086331978808569657610607 16629497968212854486415911)
    ·
      refine ⟨24944246952319281729623867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16629497968212854486415911 24944246952319281729623867)
      ·
        refine ⟨37416370428478922594435801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24944246952319281729623867 37416370428478922594435801)
        ·
          refine ⟨28062277821359191945826851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37416370428478922594435801 28062277821359191945826851)
          ·
            refine ⟨42093416732038787918740277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28062277821359191945826851 42093416732038787918740277)
            ·
              refine ⟨3946257818628636367381901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 42093416732038787918740277 3946257818628636367381901)
              ·
                refine ⟨1479846681985738637768213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3946257818628636367381901 1479846681985738637768213)
                ·
                  refine ⟨69367813218081498645385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1479846681985738637768213 69367813218081498645385)
                  ·
                    rfl

theorem cell22_607920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 5, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 5, 3, 6].length) (baseStart_607920 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_607920 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_607920 prefixEnd_607920 := by exact prefixLift 607920
  have htrace : WordTrace (prefixWord ++ tailWord_607920) baseStart_607920 baseEnd_607920 := by
    simpa [prefixWord, tailWord_607920, baseEnd_607920] using wordTrace_append hprefix tailTrace_607920
  have hstable : (prefixWord ++ tailWord_607920).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_607920).length < 2 ^ (prefixWord ++ tailWord_607920).sum := by decide
  have hdescent : baseEnd_607920 < baseStart_607920 := by decide
  rcases family_descends (prefixWord ++ tailWord_607920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_607967 : List Nat := [1, 1, 2, 3, 2, 2, 3, 2, 2, 4]
def baseStart_607967 : Nat := 118140960795 + 607967 * 2 ^ 59
def prefixEnd_607967 : Nat := 4983230072969 + 3 ^ 40 * 607967 * 2
def baseEnd_607967 : Nat := 208119528714752040011011

theorem tailTrace_607967 : CollatzResearch.WordTrace tailWord_607967 prefixEnd_607967 208119528714752040011011 := by
  unfold tailWord_607967
  simp only [CollatzResearch.WordTrace]
  refine ⟨22174378188446866342182155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14782918792297910894788103 22174378188446866342182155)
  ·
    refine ⟨33261567282670299513273233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22174378188446866342182155 33261567282670299513273233)
    ·
      refine ⟨24946175462002724634954925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33261567282670299513273233 24946175462002724634954925)
      ·
        refine ⟨9354815798251021738108097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24946175462002724634954925 9354815798251021738108097)
        ·
          refine ⟨7016111848688266303581073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9354815798251021738108097 7016111848688266303581073)
          ·
            refine ⟨5262083886516199727685805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7016111848688266303581073 5262083886516199727685805)
            ·
              refine ⟨1973281457443574897882177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5262083886516199727685805 1973281457443574897882177)
              ·
                refine ⟨1479961093082681173411633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1973281457443574897882177 1479961093082681173411633)
                ·
                  refine ⟨1109970819812010880058725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1479961093082681173411633 1109970819812010880058725)
                  ·
                    refine ⟨208119528714752040011011, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1109970819812010880058725 208119528714752040011011)
                    ·
                      rfl

theorem cell22_607967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 3, 2, 2, 4].length) (baseStart_607967 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_607967 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_607967 prefixEnd_607967 := by exact prefixLift 607967
  have htrace : WordTrace (prefixWord ++ tailWord_607967) baseStart_607967 baseEnd_607967 := by
    simpa [prefixWord, tailWord_607967, baseEnd_607967] using wordTrace_append hprefix tailTrace_607967
  have hstable : (prefixWord ++ tailWord_607967).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_607967).length < 2 ^ (prefixWord ++ tailWord_607967).sum := by decide
  have hdescent : baseEnd_607967 < baseStart_607967 := by decide
  rcases family_descends (prefixWord ++ tailWord_607967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_607971 : List Nat := [1, 1, 1, 7, 3, 1, 1, 1, 6]
def baseStart_607971 : Nat := 118140960795 + 607971 * 2 ^ 59
def prefixEnd_607971 : Nat := 4983230072969 + 3 ^ 40 * 607971 * 2
def baseEnd_607971 : Nat := 69373632665499120970333

theorem tailTrace_607971 : CollatzResearch.WordTrace tailWord_607971 prefixEnd_607971 69373632665499120970333 := by
  unfold tailWord_607971
  simp only [CollatzResearch.WordTrace]
  refine ⟨22174524080432375025327767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14783016053621583350218511 22174524080432375025327767)
  ·
    refine ⟨33261786120648562537991651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22174524080432375025327767 33261786120648562537991651)
    ·
      refine ⟨49892679180972843806987477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33261786120648562537991651 49892679180972843806987477)
      ·
        refine ⟨1169359668304051026726269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 49892679180972843806987477 1169359668304051026726269)
        ·
          refine ⟨438509875614019135022351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1169359668304051026726269 438509875614019135022351)
          ·
            refine ⟨657764813421028702533527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 438509875614019135022351 657764813421028702533527)
            ·
              refine ⟨986647220131543053800291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 657764813421028702533527 986647220131543053800291)
              ·
                refine ⟨1479970830197314580700437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 986647220131543053800291 1479970830197314580700437)
                ·
                  refine ⟨69373632665499120970333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1479970830197314580700437 69373632665499120970333)
                  ·
                    rfl

theorem cell22_607971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 3, 1, 1, 1, 6].length) (baseStart_607971 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_607971 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_607971 prefixEnd_607971 := by exact prefixLift 607971
  have htrace : WordTrace (prefixWord ++ tailWord_607971) baseStart_607971 baseEnd_607971 := by
    simpa [prefixWord, tailWord_607971, baseEnd_607971] using wordTrace_append hprefix tailTrace_607971
  have hstable : (prefixWord ++ tailWord_607971).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_607971).length < 2 ^ (prefixWord ++ tailWord_607971).sum := by decide
  have hdescent : baseEnd_607971 < baseStart_607971 := by decide
  rcases family_descends (prefixWord ++ tailWord_607971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_607982 : List Nat := [4, 1, 2, 1, 1, 2, 4, 7]
def baseStart_607982 : Nat := 118140960795 + 607982 * 2 ^ 59
def prefixEnd_607982 : Nat := 4983230072969 + 3 ^ 40 * 607982 * 2
def baseEnd_607982 : Nat := 23124962613477444542885

theorem tailTrace_607982 : CollatzResearch.WordTrace tailWord_607982 prefixEnd_607982 23124962613477444542885 := by
  unfold tailWord_607982
  simp only [CollatzResearch.WordTrace]
  refine ⟨2771865660424065487997275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14783283522261682602652133 2771865660424065487997275)
  ·
    refine ⟨4157798490636098231995913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2771865660424065487997275 4157798490636098231995913)
    ·
      refine ⟨3118348867977073673996935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4157798490636098231995913 3118348867977073673996935)
      ·
        refine ⟨4677523301965610510995403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3118348867977073673996935 4677523301965610510995403)
        ·
          refine ⟨7016284952948415766493105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4677523301965610510995403 7016284952948415766493105)
          ·
            refine ⟨5262213714711311824869829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7016284952948415766493105 5262213714711311824869829)
            ·
              refine ⟨986665071508370967163093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5262213714711311824869829 986665071508370967163093)
              ·
                refine ⟨23124962613477444542885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 986665071508370967163093 23124962613477444542885)
                ·
                  rfl

theorem cell22_607982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 4, 7].length) (baseStart_607982 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_607982 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_607982 prefixEnd_607982 := by exact prefixLift 607982
  have htrace : WordTrace (prefixWord ++ tailWord_607982) baseStart_607982 baseEnd_607982 := by
    simpa [prefixWord, tailWord_607982, baseEnd_607982] using wordTrace_append hprefix tailTrace_607982
  have hstable : (prefixWord ++ tailWord_607982).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_607982).length < 2 ^ (prefixWord ++ tailWord_607982).sum := by decide
  have hdescent : baseEnd_607982 < baseStart_607982 := by decide
  rcases family_descends (prefixWord ++ tailWord_607982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_607995 : List Nat := [1, 1, 1, 1, 1, 3, 1, 3, 4, 6]
def baseStart_607995 : Nat := 118140960795 + 607995 * 2 ^ 59
def prefixEnd_607995 : Nat := 4983230072969 + 3 ^ 40 * 607995 * 2
def baseEnd_607995 : Nat := 208129113686969300310925

theorem tailTrace_607995 : CollatzResearch.WordTrace tailWord_607995 prefixEnd_607995 208129113686969300310925 := by
  unfold tailWord_607995
  simp only [CollatzResearch.WordTrace]
  refine ⟨22175399432345427124201439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14783599621563618082800959 22175399432345427124201439)
  ·
    refine ⟨33263099148518140686302159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22175399432345427124201439 33263099148518140686302159)
    ·
      refine ⟨49894648722777211029453239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33263099148518140686302159 49894648722777211029453239)
      ·
        refine ⟨74841973084165816544179859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49894648722777211029453239 74841973084165816544179859)
        ·
          refine ⟨112262959626248724816269789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74841973084165816544179859 112262959626248724816269789)
          ·
            refine ⟨42098609859843271806101171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 112262959626248724816269789 42098609859843271806101171)
            ·
              refine ⟨63147914789764907709151757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42098609859843271806101171 63147914789764907709151757)
              ·
                refine ⟨23680468046161840390931909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 63147914789764907709151757 23680468046161840390931909)
                ·
                  refine ⟨4440087758655345073299733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23680468046161840390931909 4440087758655345073299733)
                  ·
                    refine ⟨208129113686969300310925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4440087758655345073299733 208129113686969300310925)
                    ·
                      rfl

theorem cell22_607995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 4, 6].length) (baseStart_607995 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_607995 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_607995 prefixEnd_607995 := by exact prefixLift 607995
  have htrace : WordTrace (prefixWord ++ tailWord_607995) baseStart_607995 baseEnd_607995 := by
    simpa [prefixWord, tailWord_607995, baseEnd_607995] using wordTrace_append hprefix tailTrace_607995
  have hstable : (prefixWord ++ tailWord_607995).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_607995).length < 2 ^ (prefixWord ++ tailWord_607995).sum := by decide
  have hdescent : baseEnd_607995 < baseStart_607995 := by decide
  rcases family_descends (prefixWord ++ tailWord_607995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_608031 : List Nat := [1, 1, 2, 4, 2, 1, 3, 4, 1, 3]
def baseStart_608031 : Nat := 118140960795 + 608031 * 2 ^ 59
def prefixEnd_608031 : Nat := 4983230072969 + 3 ^ 40 * 608031 * 2
def baseEnd_608031 : Nat := 208141437222677206410815

theorem tailTrace_608031 : CollatzResearch.WordTrace tailWord_608031 prefixEnd_608031 208141437222677206410815 := by
  unfold tailWord_608031
  simp only [CollatzResearch.WordTrace]
  refine ⟨22176712460215005272511947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14784474973476670181674631 22176712460215005272511947)
  ·
    refine ⟨33265068690322507908767921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22176712460215005272511947 33265068690322507908767921)
    ·
      refine ⟨24948801517741880931575941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33265068690322507908767921 24948801517741880931575941)
      ·
        refine ⟨4677900284576602674670489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 24948801517741880931575941 4677900284576602674670489)
        ·
          refine ⟨3508425213432452006002867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4677900284576602674670489 3508425213432452006002867)
          ·
            refine ⟨5262637820148678009004301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3508425213432452006002867 5262637820148678009004301)
            ·
              refine ⟨1973489182555754253376613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5262637820148678009004301 1973489182555754253376613)
              ·
                refine ⟨370029221729203922508115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1973489182555754253376613 370029221729203922508115)
                ·
                  refine ⟨555043832593805883762173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 370029221729203922508115 555043832593805883762173)
                  ·
                    refine ⟨208141437222677206410815, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 555043832593805883762173 208141437222677206410815)
                    ·
                      rfl

theorem cell22_608031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 3, 4, 1, 3].length) (baseStart_608031 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_608031 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_608031 prefixEnd_608031 := by exact prefixLift 608031
  have htrace : WordTrace (prefixWord ++ tailWord_608031) baseStart_608031 baseEnd_608031 := by
    simpa [prefixWord, tailWord_608031, baseEnd_608031] using wordTrace_append hprefix tailTrace_608031
  have hstable : (prefixWord ++ tailWord_608031).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_608031).length < 2 ^ (prefixWord ++ tailWord_608031).sum := by decide
  have hdescent : baseEnd_608031 < baseStart_608031 := by decide
  rcases family_descends (prefixWord ++ tailWord_608031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_608074 : List Nat := [3, 1, 2, 1, 1, 1, 5, 3, 1, 4]
def baseStart_608074 : Nat := 118140960795 + 608074 * 2 ^ 59
def prefixEnd_608074 : Nat := 4983230072969 + 3 ^ 40 * 608074 * 2
def baseEnd_608074 : Nat := 208156157001439427585683

theorem tailTrace_608074 : CollatzResearch.WordTrace tailWord_608074 prefixEnd_608074 208156157001439427585683 := by
  unfold tailWord_608074
  simp only [CollatzResearch.WordTrace]
  refine ⟨5544570199764805904081819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14785520532706149077551517 5544570199764805904081819)
  ·
    refine ⟨8316855299647208856122729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5544570199764805904081819 8316855299647208856122729)
    ·
      refine ⟨6237641474735406642092047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8316855299647208856122729 6237641474735406642092047)
      ·
        refine ⟨9356462212103109963138071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6237641474735406642092047 9356462212103109963138071)
        ·
          refine ⟨14034693318154664944707107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9356462212103109963138071 14034693318154664944707107)
          ·
            refine ⟨21052039977231997417060661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14034693318154664944707107 21052039977231997417060661)
            ·
              refine ⟨1973628747865499757849437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 21052039977231997417060661 1973628747865499757849437)
              ·
                refine ⟨740110780449562409193539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1973628747865499757849437 740110780449562409193539)
                ·
                  refine ⟨1110166170674343613790309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 740110780449562409193539 1110166170674343613790309)
                  ·
                    refine ⟨208156157001439427585683, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1110166170674343613790309 208156157001439427585683)
                    ·
                      rfl

theorem cell22_608074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 5, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 5, 3, 1, 4].length) (baseStart_608074 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_608074 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_608074 prefixEnd_608074 := by exact prefixLift 608074
  have htrace : WordTrace (prefixWord ++ tailWord_608074) baseStart_608074 baseEnd_608074 := by
    simpa [prefixWord, tailWord_608074, baseEnd_608074] using wordTrace_append hprefix tailTrace_608074
  have hstable : (prefixWord ++ tailWord_608074).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_608074).length < 2 ^ (prefixWord ++ tailWord_608074).sum := by decide
  have hdescent : baseEnd_608074 < baseStart_608074 := by decide
  rcases family_descends (prefixWord ++ tailWord_608074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_608089 : List Nat := [1, 2, 1, 2, 2, 3, 1, 6, 4]
def baseStart_608089 : Nat := 118140960795 + 608089 * 2 ^ 59
def prefixEnd_608089 : Nat := 4983230072969 + 3 ^ 40 * 608089 * 2
def baseEnd_608089 : Nat := 69387097269328129486879

theorem tailTrace_608089 : CollatzResearch.WordTrace tailWord_608089 prefixEnd_608089 69387097269328129486879 := by
  unfold tailWord_608089
  simp only [CollatzResearch.WordTrace]
  refine ⟨22178827894004881178123321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14785885262669920785415547 22178827894004881178123321)
  ·
    refine ⟨16634120920503660883592491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22178827894004881178123321 16634120920503660883592491)
    ·
      refine ⟨24951181380755491325388737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16634120920503660883592491 24951181380755491325388737)
      ·
        refine ⟨18713386035566618494041553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24951181380755491325388737 18713386035566618494041553)
        ·
          refine ⟨14035039526674963870531165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18713386035566618494041553 14035039526674963870531165)
          ·
            refine ⟨5263139822503111451449187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14035039526674963870531165 5263139822503111451449187)
            ·
              refine ⟨7894709733754667177173781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5263139822503111451449187 7894709733754667177173781)
              ·
                refine ⟨370064518769750023930021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 7894709733754667177173781 370064518769750023930021)
                ·
                  refine ⟨69387097269328129486879, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 370064518769750023930021 69387097269328129486879)
                  ·
                    rfl

theorem cell22_608089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 1, 6, 4].length) (baseStart_608089 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_608089 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_608089 prefixEnd_608089 := by exact prefixLift 608089
  have htrace : WordTrace (prefixWord ++ tailWord_608089) baseStart_608089 baseEnd_608089 := by
    simpa [prefixWord, tailWord_608089, baseEnd_608089] using wordTrace_append hprefix tailTrace_608089
  have hstable : (prefixWord ++ tailWord_608089).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_608089).length < 2 ^ (prefixWord ++ tailWord_608089).sum := by decide
  have hdescent : baseEnd_608089 < baseStart_608089 := by decide
  rcases family_descends (prefixWord ++ tailWord_608089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_608136 : List Nat := [2, 1, 3, 3, 3, 1, 1, 2, 2, 4]
def baseStart_608136 : Nat := 118140960795 + 608136 * 2 ^ 59
def prefixEnd_608136 : Nat := 4983230072969 + 3 ^ 40 * 608136 * 2
def baseEnd_608136 : Nat := 208177380868491932535493

theorem tailTrace_608136 : CollatzResearch.WordTrace tailWord_608136 prefixEnd_608136 208177380868491932535493 := by
  unfold tailWord_608136
  simp only [CollatzResearch.WordTrace]
  refine ⟨11090271062417304102542131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14787028083223072136722841 11090271062417304102542131)
  ·
    refine ⟨16635406593625956153813197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11090271062417304102542131 16635406593625956153813197)
    ·
      refine ⟨6238277472609733557679949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16635406593625956153813197 6238277472609733557679949)
      ·
        refine ⟨2339354052228650084129981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6238277472609733557679949 2339354052228650084129981)
        ·
          refine ⟨877257769585743781548743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2339354052228650084129981 877257769585743781548743)
          ·
            refine ⟨1315886654378615672323115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 877257769585743781548743 1315886654378615672323115)
            ·
              refine ⟨1973829981567923508484673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1315886654378615672323115 1973829981567923508484673)
              ·
                refine ⟨1480372486175942631363505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1973829981567923508484673 1480372486175942631363505)
                ·
                  refine ⟨1110279364631956973522629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1480372486175942631363505 1110279364631956973522629)
                  ·
                    refine ⟨208177380868491932535493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1110279364631956973522629 208177380868491932535493)
                    ·
                      rfl

theorem cell22_608136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 1, 1, 2, 2, 4].length) (baseStart_608136 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_608136 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_608136 prefixEnd_608136 := by exact prefixLift 608136
  have htrace : WordTrace (prefixWord ++ tailWord_608136) baseStart_608136 baseEnd_608136 := by
    simpa [prefixWord, tailWord_608136, baseEnd_608136] using wordTrace_append hprefix tailTrace_608136
  have hstable : (prefixWord ++ tailWord_608136).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_608136).length < 2 ^ (prefixWord ++ tailWord_608136).sum := by decide
  have hdescent : baseEnd_608136 < baseStart_608136 := by decide
  rcases family_descends (prefixWord ++ tailWord_608136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_608200 : List Nat := [2, 1, 3, 1, 4, 1, 4, 2, 1, 3]
def baseStart_608200 : Nat := 118140960795 + 608200 * 2 ^ 59
def prefixEnd_608200 : Nat := 4983230072969 + 3 ^ 40 * 608200 * 2
def baseEnd_608200 : Nat := 208199289376417098935297

theorem tailTrace_608200 : CollatzResearch.WordTrace tailWord_608200 prefixEnd_608200 208199289376417098935297 := by
  unfold tailWord_608200
  simp only [CollatzResearch.WordTrace]
  refine ⟨11091438198301373567707027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14788584264401831423609369 11091438198301373567707027)
  ·
    refine ⟨16637157297452060351560541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11091438198301373567707027 16637157297452060351560541)
    ·
      refine ⟨6238933986544522631835203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16637157297452060351560541 6238933986544522631835203)
      ·
        refine ⟨9358400979816783947752805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6238933986544522631835203 9358400979816783947752805)
        ·
          refine ⟨1754700183715646990203651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9358400979816783947752805 1754700183715646990203651)
          ·
            refine ⟨2632050275573470485305477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1754700183715646990203651 2632050275573470485305477)
            ·
              refine ⟨493509426670025715994777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2632050275573470485305477 493509426670025715994777)
              ·
                refine ⟨370132070002519286996083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 493509426670025715994777 370132070002519286996083)
                ·
                  refine ⟨555198105003778930494125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 370132070002519286996083 555198105003778930494125)
                  ·
                    refine ⟨208199289376417098935297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 555198105003778930494125 208199289376417098935297)
                    ·
                      rfl

theorem cell22_608200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 4, 2, 1, 3].length) (baseStart_608200 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_608200 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_608200 prefixEnd_608200 := by exact prefixLift 608200
  have htrace : WordTrace (prefixWord ++ tailWord_608200) baseStart_608200 baseEnd_608200 := by
    simpa [prefixWord, tailWord_608200, baseEnd_608200] using wordTrace_append hprefix tailTrace_608200
  have hstable : (prefixWord ++ tailWord_608200).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_608200).length < 2 ^ (prefixWord ++ tailWord_608200).sum := by decide
  have hdescent : baseEnd_608200 < baseStart_608200 := by decide
  rcases family_descends (prefixWord ++ tailWord_608200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_608239 : List Nat := [1, 1, 2, 1, 4, 2, 1, 4, 1, 5]
def baseStart_608239 : Nat := 118140960795 + 608239 * 2 ^ 59
def prefixEnd_608239 : Nat := 4983230072969 + 3 ^ 40 * 608239 * 2
def baseEnd_608239 : Nat := 208212639873433997210177

theorem tailTrace_608239 : CollatzResearch.WordTrace tailWord_608239 prefixEnd_608239 208212639873433997210177 := by
  unfold tailWord_608239
  simp only [CollatzResearch.WordTrace]
  refine ⟨22184298843461456796083771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14789532562307637864055847 22184298843461456796083771)
  ·
    refine ⟨33276448265192185194125657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22184298843461456796083771 33276448265192185194125657)
    ·
      refine ⟨24957336198894138895594243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33276448265192185194125657 24957336198894138895594243)
      ·
        refine ⟨37436004298341208343391365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24957336198894138895594243 37436004298341208343391365)
        ·
          refine ⟨7019250805938976564385881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 37436004298341208343391365 7019250805938976564385881)
          ·
            refine ⟨5264438104454232423289411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7019250805938976564385881 5264438104454232423289411)
            ·
              refine ⟨7896657156681348634934117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5264438104454232423289411 7896657156681348634934117)
              ·
                refine ⟨1480623216877752869050147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7896657156681348634934117 1480623216877752869050147)
                ·
                  refine ⟨2220934825316629303575221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1480623216877752869050147 2220934825316629303575221)
                  ·
                    refine ⟨208212639873433997210177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2220934825316629303575221 208212639873433997210177)
                    ·
                      rfl

theorem cell22_608239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 1, 4, 1, 5].length) (baseStart_608239 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_608239 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_608239 prefixEnd_608239 := by exact prefixLift 608239
  have htrace : WordTrace (prefixWord ++ tailWord_608239) baseStart_608239 baseEnd_608239 := by
    simpa [prefixWord, tailWord_608239, baseEnd_608239] using wordTrace_append hprefix tailTrace_608239
  have hstable : (prefixWord ++ tailWord_608239).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_608239).length < 2 ^ (prefixWord ++ tailWord_608239).sum := by decide
  have hdescent : baseEnd_608239 < baseStart_608239 := by decide
  rcases family_descends (prefixWord ++ tailWord_608239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_608256 : List Nat := [2, 1, 1, 2, 1, 1, 1, 8, 2, 3]
def baseStart_608256 : Nat := 118140960795 + 608256 * 2 ^ 59
def prefixEnd_608256 : Nat := 4983230072969 + 3 ^ 40 * 608256 * 2
def baseEnd_608256 : Nat := 208218459320851619535125

theorem tailTrace_608256 : CollatzResearch.WordTrace tailWord_608256 prefixEnd_608256 208218459320851619535125 := by
  unfold tailWord_608256
  simp only [CollatzResearch.WordTrace]
  refine ⟨11092459442199934349726311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14789945922933245799635081 11092459442199934349726311)
  ·
    refine ⟨16638689163299901524589467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11092459442199934349726311 16638689163299901524589467)
    ·
      refine ⟨24958033744949852286884201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16638689163299901524589467 24958033744949852286884201)
      ·
        refine ⟨18718525308712389215163151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24958033744949852286884201 18718525308712389215163151)
        ·
          refine ⟨28077787963068583822744727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18718525308712389215163151 28077787963068583822744727)
          ·
            refine ⟨42116681944602875734117091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28077787963068583822744727 42116681944602875734117091)
            ·
              refine ⟨63175022916904313601175637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42116681944602875734117091 63175022916904313601175637)
              ·
                refine ⟨740332299807472425013777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 63175022916904313601175637 740332299807472425013777)
                ·
                  refine ⟨555249224855604318760333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 740332299807472425013777 555249224855604318760333)
                  ·
                    refine ⟨208218459320851619535125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 555249224855604318760333 208218459320851619535125)
                    ·
                      rfl

theorem cell22_608256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 8, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 8, 2, 3].length) (baseStart_608256 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_608256 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_608256 prefixEnd_608256 := by exact prefixLift 608256
  have htrace : WordTrace (prefixWord ++ tailWord_608256) baseStart_608256 baseEnd_608256 := by
    simpa [prefixWord, tailWord_608256, baseEnd_608256] using wordTrace_append hprefix tailTrace_608256
  have hstable : (prefixWord ++ tailWord_608256).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_608256).length < 2 ^ (prefixWord ++ tailWord_608256).sum := by decide
  have hdescent : baseEnd_608256 < baseStart_608256 := by decide
  rcases family_descends (prefixWord ++ tailWord_608256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_608292 : List Nat := [2, 3, 1, 4, 3, 1, 1, 3, 4]
def baseStart_608292 : Nat := 118140960795 + 608292 * 2 ^ 59
def prefixEnd_608292 : Nat := 4983230072969 + 3 ^ 40 * 608292 * 2
def baseEnd_608292 : Nat := 69410260952186508545005

theorem tailTrace_608292 : CollatzResearch.WordTrace tailWord_608292 prefixEnd_608292 69410260952186508545005 := by
  unfold tailWord_608292
  simp only [CollatzResearch.WordTrace]
  refine ⟨11093115956134723423881565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14790821274846297898508753 11093115956134723423881565)
  ·
    refine ⟨4159918483550521283955587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11093115956134723423881565 4159918483550521283955587)
    ·
      refine ⟨6239877725325781925933381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4159918483550521283955587 6239877725325781925933381)
      ·
        refine ⟨1169977073498584111112509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6239877725325781925933381 1169977073498584111112509)
        ·
          refine ⟨438741402561969041667191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1169977073498584111112509 438741402561969041667191)
          ·
            refine ⟨658112103842953562500787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 438741402561969041667191 658112103842953562500787)
            ·
              refine ⟨987168155764430343751181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 658112103842953562500787 987168155764430343751181)
              ·
                refine ⟨370188058411661378906693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 987168155764430343751181 370188058411661378906693)
                ·
                  refine ⟨69410260952186508545005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 370188058411661378906693 69410260952186508545005)
                  ·
                    rfl

theorem cell22_608292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 3, 1, 1, 3, 4].length) (baseStart_608292 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_608292 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_608292 prefixEnd_608292 := by exact prefixLift 608292
  have htrace : WordTrace (prefixWord ++ tailWord_608292) baseStart_608292 baseEnd_608292 := by
    simpa [prefixWord, tailWord_608292, baseEnd_608292] using wordTrace_append hprefix tailTrace_608292
  have hstable : (prefixWord ++ tailWord_608292).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_608292).length < 2 ^ (prefixWord ++ tailWord_608292).sum := by decide
  have hdescent : baseEnd_608292 < baseStart_608292 := by decide
  rcases family_descends (prefixWord ++ tailWord_608292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_608329 : List Nat := [1, 2, 1, 1, 2, 2, 4, 1, 1, 7]
def baseStart_608329 : Nat := 118140960795 + 608329 * 2 ^ 59
def prefixEnd_608329 : Nat := 4983230072969 + 3 ^ 40 * 608329 * 2
def baseEnd_608329 : Nat := 208243448712703762459901

theorem tailTrace_608329 : CollatzResearch.WordTrace tailWord_608329 prefixEnd_608329 208243448712703762459901 := by
  unfold tailWord_608329
  simp only [CollatzResearch.WordTrace]
  refine ⟨22187581413135402166860041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14791720942090268111240027 22187581413135402166860041)
  ·
    refine ⟨16640686059851551625145031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22187581413135402166860041 16640686059851551625145031)
    ·
      refine ⟨24961029089777327437717547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16640686059851551625145031 24961029089777327437717547)
      ·
        refine ⟨37441543634665991156576321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24961029089777327437717547 37441543634665991156576321)
        ·
          refine ⟨28081157725999493367432241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37441543634665991156576321 28081157725999493367432241)
          ·
            refine ⟨21060868294499620025574181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28081157725999493367432241 21060868294499620025574181)
            ·
              refine ⟨3948912805218678754795159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21060868294499620025574181 3948912805218678754795159)
              ·
                refine ⟨5923369207828018132192739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3948912805218678754795159 5923369207828018132192739)
                ·
                  refine ⟨8885053811742027198289109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5923369207828018132192739 8885053811742027198289109)
                  ·
                    refine ⟨208243448712703762459901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 8885053811742027198289109 208243448712703762459901)
                    ·
                      rfl

theorem cell22_608329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 4, 1, 1, 7].length) (baseStart_608329 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_608329 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_608329 prefixEnd_608329 := by exact prefixLift 608329
  have htrace : WordTrace (prefixWord ++ tailWord_608329) baseStart_608329 baseEnd_608329 := by
    simpa [prefixWord, tailWord_608329, baseEnd_608329] using wordTrace_append hprefix tailTrace_608329
  have hstable : (prefixWord ++ tailWord_608329).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_608329).length < 2 ^ (prefixWord ++ tailWord_608329).sum := by decide
  have hdescent : baseEnd_608329 < baseStart_608329 := by decide
  rcases family_descends (prefixWord ++ tailWord_608329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_608391 : List Nat := [1, 1, 4, 2, 1, 1, 3, 3, 1, 5]
def baseStart_608391 : Nat := 118140960795 + 608391 * 2 ^ 59
def prefixEnd_608391 : Nat := 4983230072969 + 3 ^ 40 * 608391 * 2
def baseEnd_608391 : Nat := 208264672579756267409711

theorem tailTrace_608391 : CollatzResearch.WordTrace tailWord_608391 prefixEnd_608391 208264672579756267409711 := by
  unfold tailWord_608391
  simp only [CollatzResearch.WordTrace]
  refine ⟨22189842738910786755617027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14793228492607191170411351 22189842738910786755617027)
  ·
    refine ⟨33284764108366180133425541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22189842738910786755617027 33284764108366180133425541)
    ·
      refine ⟨6240893270318658775017289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 33284764108366180133425541 6240893270318658775017289)
      ·
        refine ⟨4680669952738994081262967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6240893270318658775017289 4680669952738994081262967)
        ·
          refine ⟨7021004929108491121894451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4680669952738994081262967 7021004929108491121894451)
          ·
            refine ⟨10531507393662736682841677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7021004929108491121894451 10531507393662736682841677)
            ·
              refine ⟨3949315272623526256065629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10531507393662736682841677 3949315272623526256065629)
              ·
                refine ⟨1480993227233822346024611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3949315272623526256065629 1480993227233822346024611)
                ·
                  refine ⟨2221489840850733519036917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1480993227233822346024611 2221489840850733519036917)
                  ·
                    refine ⟨208264672579756267409711, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2221489840850733519036917 208264672579756267409711)
                    ·
                      rfl

theorem cell22_608391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 3, 3, 1, 5].length) (baseStart_608391 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_608391 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_608391 prefixEnd_608391 := by exact prefixLift 608391
  have htrace : WordTrace (prefixWord ++ tailWord_608391) baseStart_608391 baseEnd_608391 := by
    simpa [prefixWord, tailWord_608391, baseEnd_608391] using wordTrace_append hprefix tailTrace_608391
  have hstable : (prefixWord ++ tailWord_608391).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_608391).length < 2 ^ (prefixWord ++ tailWord_608391).sum := by decide
  have hdescent : baseEnd_608391 < baseStart_608391 := by decide
  rcases family_descends (prefixWord ++ tailWord_608391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_608453 : List Nat := [1, 3, 1, 1, 1, 1, 6, 2, 3, 3]
def baseStart_608453 : Nat := 118140960795 + 608453 * 2 ^ 59
def prefixEnd_608453 : Nat := 4983230072969 + 3 ^ 40 * 608453 * 2
def baseEnd_608453 : Nat := 208285896446808772359521

theorem tailTrace_608453 : CollatzResearch.WordTrace tailWord_608453 prefixEnd_608453 208285896446808772359521 := by
  unfold tailWord_608453
  simp only [CollatzResearch.WordTrace]
  refine ⟨22192104064686171344374013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14794736043124114229582675 22192104064686171344374013)
  ·
    refine ⟨8322039024257314254140255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22192104064686171344374013 8322039024257314254140255)
    ·
      refine ⟨12483058536385971381210383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8322039024257314254140255 12483058536385971381210383)
      ·
        refine ⟨18724587804578957071815575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12483058536385971381210383 18724587804578957071815575)
        ·
          refine ⟨28086881706868435607723363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18724587804578957071815575 28086881706868435607723363)
          ·
            refine ⟨42130322560302653411585045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28086881706868435607723363 42130322560302653411585045)
            ·
              refine ⟨1974858870014186878668049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 42130322560302653411585045 1974858870014186878668049)
              ·
                refine ⟨1481144152510640159001037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1974858870014186878668049 1481144152510640159001037)
                ·
                  refine ⟨555429057191490059625389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1481144152510640159001037 555429057191490059625389)
                  ·
                    refine ⟨208285896446808772359521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 555429057191490059625389 208285896446808772359521)
                    ·
                      rfl

theorem cell22_608453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 6, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 6, 2, 3, 3].length) (baseStart_608453 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_608453 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_608453 prefixEnd_608453 := by exact prefixLift 608453
  have htrace : WordTrace (prefixWord ++ tailWord_608453) baseStart_608453 baseEnd_608453 := by
    simpa [prefixWord, tailWord_608453, baseEnd_608453] using wordTrace_append hprefix tailTrace_608453
  have hstable : (prefixWord ++ tailWord_608453).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_608453).length < 2 ^ (prefixWord ++ tailWord_608453).sum := by decide
  have hdescent : baseEnd_608453 < baseStart_608453 := by decide
  rcases family_descends (prefixWord ++ tailWord_608453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_608487 : List Nat := [1, 1, 5, 3, 1, 3, 1, 1, 3, 3]
def baseStart_608487 : Nat := 118140960795 + 608487 * 2 ^ 59
def prefixEnd_608487 : Nat := 4983230072969 + 3 ^ 40 * 608487 * 2
def baseEnd_608487 : Nat := 208297535341644017009417

theorem tailTrace_608487 : CollatzResearch.WordTrace tailWord_608487 prefixEnd_608487 208297535341644017009417 := by
  unfold tailWord_608487
  simp only [CollatzResearch.WordTrace]
  refine ⟨22193344146562995151111715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14795562764375330100741143 22193344146562995151111715)
  ·
    refine ⟨33290016219844492726667573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22193344146562995151111715 33290016219844492726667573)
    ·
      refine ⟨3120939020610421193125085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 33290016219844492726667573 3120939020610421193125085)
      ·
        refine ⟨1170352132728907947421907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3120939020610421193125085 1170352132728907947421907)
        ·
          refine ⟨1755528199093361921132861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1170352132728907947421907 1755528199093361921132861)
          ·
            refine ⟨658323074660010720424823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1755528199093361921132861 658323074660010720424823)
            ·
              refine ⟨987484611990016080637235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 658323074660010720424823 987484611990016080637235)
              ·
                refine ⟨1481226917985024120955853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 987484611990016080637235 1481226917985024120955853)
                ·
                  refine ⟨555460094244384045358445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1481226917985024120955853 555460094244384045358445)
                  ·
                    refine ⟨208297535341644017009417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 555460094244384045358445 208297535341644017009417)
                    ·
                      rfl

theorem cell22_608487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 3, 1, 1, 3, 3].length) (baseStart_608487 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_608487 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_608487 prefixEnd_608487 := by exact prefixLift 608487
  have htrace : WordTrace (prefixWord ++ tailWord_608487) baseStart_608487 baseEnd_608487 := by
    simpa [prefixWord, tailWord_608487, baseEnd_608487] using wordTrace_append hprefix tailTrace_608487
  have hstable : (prefixWord ++ tailWord_608487).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_608487).length < 2 ^ (prefixWord ++ tailWord_608487).sum := by decide
  have hdescent : baseEnd_608487 < baseStart_608487 := by decide
  rcases family_descends (prefixWord ++ tailWord_608487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_608511 : List Nat := [1, 1, 2, 2, 1, 4, 2, 1, 8]
def baseStart_608511 : Nat := 118140960795 + 608511 * 2 ^ 59
def prefixEnd_608511 : Nat := 4983230072969 + 3 ^ 40 * 608511 * 2
def baseEnd_608511 : Nat := 69435250344038651469781

theorem tailTrace_608511 : CollatzResearch.WordTrace tailWord_608511 prefixEnd_608511 69435250344038651469781 := by
  unfold tailWord_608511
  simp only [CollatzResearch.WordTrace]
  refine ⟨22194219498476047249985387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14796146332317364833323591 22194219498476047249985387)
  ·
    refine ⟨33291329247714070874978081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22194219498476047249985387 33291329247714070874978081)
    ·
      refine ⟨24968496935785553156233561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33291329247714070874978081 24968496935785553156233561)
      ·
        refine ⟨18726372701839164867175171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24968496935785553156233561 18726372701839164867175171)
        ·
          refine ⟨28089559052758747300762757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18726372701839164867175171 28089559052758747300762757)
          ·
            refine ⟨5266792322392265118893017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 28089559052758747300762757 5266792322392265118893017)
            ·
              refine ⟨3950094241794198839169763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5266792322392265118893017 3950094241794198839169763)
              ·
                refine ⟨5925141362691298258754645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3950094241794198839169763 5925141362691298258754645)
                ·
                  refine ⟨69435250344038651469781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 5925141362691298258754645 69435250344038651469781)
                  ·
                    rfl

theorem cell22_608511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 2, 1, 8].length) (baseStart_608511 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_608511 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_608511 prefixEnd_608511 := by exact prefixLift 608511
  have htrace : WordTrace (prefixWord ++ tailWord_608511) baseStart_608511 baseEnd_608511 := by
    simpa [prefixWord, tailWord_608511, baseEnd_608511] using wordTrace_append hprefix tailTrace_608511
  have hstable : (prefixWord ++ tailWord_608511).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_608511).length < 2 ^ (prefixWord ++ tailWord_608511).sum := by decide
  have hdescent : baseEnd_608511 < baseStart_608511 := by decide
  rcases family_descends (prefixWord ++ tailWord_608511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_608513 : List Nat := [1, 2, 4, 1, 1, 2, 3, 1, 3, 4]
def baseStart_608513 : Nat := 118140960795 + 608513 * 2 ^ 59
def prefixEnd_608513 : Nat := 4983230072969 + 3 ^ 40 * 608513 * 2
def baseEnd_608513 : Nat := 208306435672988615859337

theorem tailTrace_608513 : CollatzResearch.WordTrace tailWord_608513 prefixEnd_608513 208306435672988615859337 := by
  unfold tailWord_608513
  simp only [CollatzResearch.WordTrace]
  refine ⟨22194292444468801591558193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14796194962979201061038795 22194292444468801591558193)
  ·
    refine ⟨16645719333351601193668645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22194292444468801591558193 16645719333351601193668645)
    ·
      refine ⟨3121072375003425223812871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 16645719333351601193668645 3121072375003425223812871)
      ·
        refine ⟨4681608562505137835719307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3121072375003425223812871 4681608562505137835719307)
        ·
          refine ⟨7022412843757706753578961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4681608562505137835719307 7022412843757706753578961)
          ·
            refine ⟨5266809632818280065184221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7022412843757706753578961 5266809632818280065184221)
            ·
              refine ⟨1975053612306855024444083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5266809632818280065184221 1975053612306855024444083)
              ·
                refine ⟨2962580418460282536666125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1975053612306855024444083 2962580418460282536666125)
                ·
                  refine ⟨1110967656922605951249797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2962580418460282536666125 1110967656922605951249797)
                  ·
                    refine ⟨208306435672988615859337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1110967656922605951249797 208306435672988615859337)
                    ·
                      rfl

theorem cell22_608513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 3, 1, 3, 4].length) (baseStart_608513 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_608513 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_608513 prefixEnd_608513 := by exact prefixLift 608513
  have htrace : WordTrace (prefixWord ++ tailWord_608513) baseStart_608513 baseEnd_608513 := by
    simpa [prefixWord, tailWord_608513, baseEnd_608513] using wordTrace_append hprefix tailTrace_608513
  have hstable : (prefixWord ++ tailWord_608513).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_608513).length < 2 ^ (prefixWord ++ tailWord_608513).sum := by decide
  have hdescent : baseEnd_608513 < baseStart_608513 := by decide
  rcases family_descends (prefixWord ++ tailWord_608513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_608662 : List Nat := [5, 3, 1, 2, 2, 1, 2, 1, 2, 3]
def baseStart_608662 : Nat := 118140960795 + 608662 * 2 ^ 59
def prefixEnd_608662 : Nat := 4983230072969 + 3 ^ 40 * 608662 * 2
def baseEnd_608662 : Nat := 208357441418001893883881

theorem tailTrace_608662 : CollatzResearch.WordTrace tailWord_608662 prefixEnd_608662 208357441418001893883881 := by
  unfold tailWord_608662
  simp only [CollatzResearch.WordTrace]
  refine ⟨1387482932558062502420765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 14799817947286000025821493 1387482932558062502420765)
  ·
    refine ⟨520306099709273438407787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1387482932558062502420765 520306099709273438407787)
    ·
      refine ⟨780459149563910157611681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 520306099709273438407787 780459149563910157611681)
      ·
        refine ⟨585344362172932618208761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 780459149563910157611681 585344362172932618208761)
        ·
          refine ⟨439008271629699463656571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 585344362172932618208761 439008271629699463656571)
          ·
            refine ⟨658512407444549195484857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 439008271629699463656571 658512407444549195484857)
            ·
              refine ⟨493884305583411896613643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 658512407444549195484857 493884305583411896613643)
              ·
                refine ⟨740826458375117844920465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 493884305583411896613643 740826458375117844920465)
                ·
                  refine ⟨555619843781338383690349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 740826458375117844920465 555619843781338383690349)
                  ·
                    refine ⟨208357441418001893883881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 555619843781338383690349 208357441418001893883881)
                    ·
                      rfl

theorem cell22_608662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 2, 1, 2, 1, 2, 3].length) (baseStart_608662 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_608662 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_608662 prefixEnd_608662 := by exact prefixLift 608662
  have htrace : WordTrace (prefixWord ++ tailWord_608662) baseStart_608662 baseEnd_608662 := by
    simpa [prefixWord, tailWord_608662, baseEnd_608662] using wordTrace_append hprefix tailTrace_608662
  have hstable : (prefixWord ++ tailWord_608662).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_608662).length < 2 ^ (prefixWord ++ tailWord_608662).sum := by decide
  have hdescent : baseEnd_608662 < baseStart_608662 := by decide
  rcases family_descends (prefixWord ++ tailWord_608662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_608669 : List Nat := [1, 4, 2, 1, 4, 2, 2, 1, 5]
def baseStart_608669 : Nat := 118140960795 + 608669 * 2 ^ 59
def prefixEnd_608669 : Nat := 4983230072969 + 3 ^ 40 * 608669 * 2
def baseEnd_608669 : Nat := 69453279220352069652953

theorem tailTrace_608669 : CollatzResearch.WordTrace tailWord_608669 prefixEnd_608669 69453279220352069652953 := by
  unfold tailWord_608669
  simp only [CollatzResearch.WordTrace]
  refine ⟨22199982231903640234237061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14799988154602426822824707 22199982231903640234237061)
  ·
    refine ⟨4162496668481932543919449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 22199982231903640234237061 4162496668481932543919449)
    ·
      refine ⟨3121872501361449407939587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4162496668481932543919449 3121872501361449407939587)
      ·
        refine ⟨4682808752042174111909381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3121872501361449407939587 4682808752042174111909381)
        ·
          refine ⟨878026641007907645983009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4682808752042174111909381 878026641007907645983009)
          ·
            refine ⟨658519980755930734487257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 878026641007907645983009 658519980755930734487257)
            ·
              refine ⟨493889985566948050865443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 658519980755930734487257 493889985566948050865443)
              ·
                refine ⟨740834978350422076298165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 493889985566948050865443 740834978350422076298165)
                ·
                  refine ⟨69453279220352069652953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 740834978350422076298165 69453279220352069652953)
                  ·
                    rfl

theorem cell22_608669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 2, 2, 1, 5].length) (baseStart_608669 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_608669 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_608669 prefixEnd_608669 := by exact prefixLift 608669
  have htrace : WordTrace (prefixWord ++ tailWord_608669) baseStart_608669 baseEnd_608669 := by
    simpa [prefixWord, tailWord_608669, baseEnd_608669] using wordTrace_append hprefix tailTrace_608669
  have hstable : (prefixWord ++ tailWord_608669).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_608669).length < 2 ^ (prefixWord ++ tailWord_608669).sum := by decide
  have hdescent : baseEnd_608669 < baseStart_608669 := by decide
  rcases family_descends (prefixWord ++ tailWord_608669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_608695 : List Nat := [1, 1, 3, 1, 3, 4, 1, 2, 1, 5]
def baseStart_608695 : Nat := 118140960795 + 608695 * 2 ^ 59
def prefixEnd_608695 : Nat := 4983230072969 + 3 ^ 40 * 608695 * 2
def baseEnd_608695 : Nat := 208368737992400807808779

theorem tailTrace_608695 : CollatzResearch.WordTrace tailWord_608695 prefixEnd_608695 208368737992400807808779 := by
  unfold tailWord_608695
  simp only [CollatzResearch.WordTrace]
  refine ⟨22200930529809446674683539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14800620353206297783122359 22200930529809446674683539)
  ·
    refine ⟨33301395794714170012025309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22200930529809446674683539 33301395794714170012025309)
    ·
      refine ⟨12488023423017813754509491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33301395794714170012025309 12488023423017813754509491)
      ·
        refine ⟨18732035134526720631764237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12488023423017813754509491 18732035134526720631764237)
        ·
          refine ⟨7024513175447520236911589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18732035134526720631764237 7024513175447520236911589)
          ·
            refine ⟨1317096220396410044420923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7024513175447520236911589 1317096220396410044420923)
            ·
              refine ⟨1975644330594615066631385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1317096220396410044420923 1975644330594615066631385)
              ·
                refine ⟨1481733247945961299973539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1975644330594615066631385 1481733247945961299973539)
                ·
                  refine ⟨2222599871918941949960309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1481733247945961299973539 2222599871918941949960309)
                  ·
                    refine ⟨208368737992400807808779, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2222599871918941949960309 208368737992400807808779)
                    ·
                      rfl

theorem cell22_608695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 4, 1, 2, 1, 5].length) (baseStart_608695 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_608695 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_608695 prefixEnd_608695 := by exact prefixLift 608695
  have htrace : WordTrace (prefixWord ++ tailWord_608695) baseStart_608695 baseEnd_608695 := by
    simpa [prefixWord, tailWord_608695, baseEnd_608695] using wordTrace_append hprefix tailTrace_608695
  have hstable : (prefixWord ++ tailWord_608695).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_608695).length < 2 ^ (prefixWord ++ tailWord_608695).sum := by decide
  have hdescent : baseEnd_608695 < baseStart_608695 := by decide
  rcases family_descends (prefixWord ++ tailWord_608695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_608712 : List Nat := [2, 1, 3, 1, 3, 2, 1, 4, 2, 3]
def baseStart_608712 : Nat := 118140960795 + 608712 * 2 ^ 59
def prefixEnd_608712 : Nat := 4983230072969 + 3 ^ 40 * 608712 * 2
def baseEnd_608712 : Nat := 208374557439818430133727

theorem tailTrace_608712 : CollatzResearch.WordTrace tailWord_608712 prefixEnd_608712 208374557439818430133727 := by
  unfold tailWord_608712
  simp only [CollatzResearch.WordTrace]
  refine ⟨11100775285373929289026195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14801033713831905718701593 11100775285373929289026195)
  ·
    refine ⟨16651162928060893933539293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11100775285373929289026195 16651162928060893933539293)
    ·
      refine ⟨6244186098022835225077235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16651162928060893933539293 6244186098022835225077235)
      ·
        refine ⟨9366279147034252837615853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6244186098022835225077235 9366279147034252837615853)
        ·
          refine ⟨3512354680137844814105945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9366279147034252837615853 3512354680137844814105945)
          ·
            refine ⟨2634266010103383610579459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3512354680137844814105945 2634266010103383610579459)
            ·
              refine ⟨3951399015155075415869189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2634266010103383610579459 3951399015155075415869189)
              ·
                refine ⟨740887315341576640475473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3951399015155075415869189 740887315341576640475473)
                ·
                  refine ⟨555665486506182480356605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 740887315341576640475473 555665486506182480356605)
                  ·
                    refine ⟨208374557439818430133727, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 555665486506182480356605 208374557439818430133727)
                    ·
                      rfl

theorem cell22_608712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 1, 4, 2, 3].length) (baseStart_608712 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_608712 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_608712 prefixEnd_608712 := by exact prefixLift 608712
  have htrace : WordTrace (prefixWord ++ tailWord_608712) baseStart_608712 baseEnd_608712 := by
    simpa [prefixWord, tailWord_608712, baseEnd_608712] using wordTrace_append hprefix tailTrace_608712
  have hstable : (prefixWord ++ tailWord_608712).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_608712).length < 2 ^ (prefixWord ++ tailWord_608712).sum := by decide
  have hdescent : baseEnd_608712 < baseStart_608712 := by decide
  rcases family_descends (prefixWord ++ tailWord_608712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_608725 : List Nat := [1, 3, 2, 3, 1, 2, 3, 7]
def baseStart_608725 : Nat := 118140960795 + 608725 * 2 ^ 59
def prefixEnd_608725 : Nat := 4983230072969 + 3 ^ 40 * 608725 * 2
def baseEnd_608725 : Nat := 23153223067276747728743

theorem tailTrace_608725 : CollatzResearch.WordTrace tailWord_608725 prefixEnd_608725 23153223067276747728743 := by
  unfold tailWord_608725
  simp only [CollatzResearch.WordTrace]
  refine ⟨22202024719700761798275629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14801349813133841198850419 22202024719700761798275629)
  ·
    refine ⟨8325759269887785674353361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22202024719700761798275629 8325759269887785674353361)
    ·
      refine ⟨6244319452415839255765021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8325759269887785674353361 6244319452415839255765021)
      ·
        refine ⟨2341619794655939720911883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6244319452415839255765021 2341619794655939720911883)
        ·
          refine ⟨3512429691983909581367825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2341619794655939720911883 3512429691983909581367825)
          ·
            refine ⟨2634322268987932186025869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3512429691983909581367825 2634322268987932186025869)
            ·
              refine ⟨987870850870474569759701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2634322268987932186025869 987870850870474569759701)
              ·
                refine ⟨23153223067276747728743, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 987870850870474569759701 23153223067276747728743)
                ·
                  rfl

theorem cell22_608725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 3, 7].length) (baseStart_608725 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_608725 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_608725 prefixEnd_608725 := by exact prefixLift 608725
  have htrace : WordTrace (prefixWord ++ tailWord_608725) baseStart_608725 baseEnd_608725 := by
    simpa [prefixWord, tailWord_608725, baseEnd_608725] using wordTrace_append hprefix tailTrace_608725
  have hstable : (prefixWord ++ tailWord_608725).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_608725).length < 2 ^ (prefixWord ++ tailWord_608725).sum := by decide
  have hdescent : baseEnd_608725 < baseStart_608725 := by decide
  rcases family_descends (prefixWord ++ tailWord_608725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_608787 : List Nat := [1, 1, 1, 2, 1, 5, 5, 1, 5]
def baseStart_608787 : Nat := 118140960795 + 608787 * 2 ^ 59
def prefixEnd_608787 : Nat := 4983230072969 + 3 ^ 40 * 608787 * 2
def baseEnd_608787 : Nat := 69466743824181078169499

theorem tailTrace_608787 : CollatzResearch.WordTrace tailWord_608787 prefixEnd_608787 69466743824181078169499 := by
  unfold tailWord_608787
  simp only [CollatzResearch.WordTrace]
  refine ⟨22204286045476146387032615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14802857363650764258021743 22204286045476146387032615)
  ·
    refine ⟨33306429068214219580548923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22204286045476146387032615 33306429068214219580548923)
    ·
      refine ⟨49959643602321329370823385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33306429068214219580548923 49959643602321329370823385)
      ·
        refine ⟨37469732701740997028117539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49959643602321329370823385 37469732701740997028117539)
        ·
          refine ⟨56204599052611495542176309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37469732701740997028117539 56204599052611495542176309)
          ·
            refine ⟨5269181161182327707079029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 56204599052611495542176309 5269181161182327707079029)
            ·
              refine ⟨493985733860843222538659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 5269181161182327707079029 493985733860843222538659)
              ·
                refine ⟨740978600791264833807989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 493985733860843222538659 740978600791264833807989)
                ·
                  refine ⟨69466743824181078169499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 740978600791264833807989 69466743824181078169499)
                  ·
                    rfl

theorem cell22_608787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 5, 1, 5].length) (baseStart_608787 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_608787 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_608787 prefixEnd_608787 := by exact prefixLift 608787
  have htrace : WordTrace (prefixWord ++ tailWord_608787) baseStart_608787 baseEnd_608787 := by
    simpa [prefixWord, tailWord_608787, baseEnd_608787] using wordTrace_append hprefix tailTrace_608787
  have hstable : (prefixWord ++ tailWord_608787).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_608787).length < 2 ^ (prefixWord ++ tailWord_608787).sum := by decide
  have hdescent : baseEnd_608787 < baseStart_608787 := by decide
  rcases family_descends (prefixWord ++ tailWord_608787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_608808 : List Nat := [2, 1, 5, 2, 1, 3, 1, 3, 1, 3]
def baseStart_608808 : Nat := 118140960795 + 608808 * 2 ^ 59
def prefixEnd_608808 : Nat := 4983230072969 + 3 ^ 40 * 608808 * 2
def baseEnd_608808 : Nat := 208407420201706179733433

theorem tailTrace_608808 : CollatzResearch.WordTrace tailWord_608808 prefixEnd_608808 208407420201706179733433 := by
  unfold tailWord_608808
  simp only [CollatzResearch.WordTrace]
  refine ⟨11102525989200033486773539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14803367985600044649031385 11102525989200033486773539)
  ·
    refine ⟨16653788983800050230160309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11102525989200033486773539 16653788983800050230160309)
    ·
      refine ⟨1561292717231254709077529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 16653788983800050230160309 1561292717231254709077529)
      ·
        refine ⟨1170969537923441031808147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1561292717231254709077529 1170969537923441031808147)
        ·
          refine ⟨1756454306885161547712221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1170969537923441031808147 1756454306885161547712221)
          ·
            refine ⟨658670365081935580392083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1756454306885161547712221 658670365081935580392083)
            ·
              refine ⟨988005547622903370588125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 658670365081935580392083 988005547622903370588125)
              ·
                refine ⟨370502080358588763970547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 988005547622903370588125 370502080358588763970547)
                ·
                  refine ⟨555753120537883145955821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 370502080358588763970547 555753120537883145955821)
                  ·
                    refine ⟨208407420201706179733433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 555753120537883145955821 208407420201706179733433)
                    ·
                      rfl

theorem cell22_608808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 3, 1, 3, 1, 3].length) (baseStart_608808 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_608808 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_608808 prefixEnd_608808 := by exact prefixLift 608808
  have htrace : WordTrace (prefixWord ++ tailWord_608808) baseStart_608808 baseEnd_608808 := by
    simpa [prefixWord, tailWord_608808, baseEnd_608808] using wordTrace_append hprefix tailTrace_608808
  have hstable : (prefixWord ++ tailWord_608808).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_608808).length < 2 ^ (prefixWord ++ tailWord_608808).sum := by decide
  have hdescent : baseEnd_608808 < baseStart_608808 := by decide
  rcases family_descends (prefixWord ++ tailWord_608808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_608817 : List Nat := [1, 2, 2, 3, 1, 1, 4, 3, 1, 4]
def baseStart_608817 : Nat := 118140960795 + 608817 * 2 ^ 59
def prefixEnd_608817 : Nat := 4983230072969 + 3 ^ 40 * 608817 * 2
def baseEnd_608817 : Nat := 208410501085633156258405

theorem tailTrace_608817 : CollatzResearch.WordTrace tailWord_608817 prefixEnd_608817 208410501085633156258405 := by
  unfold tailWord_608817
  simp only [CollatzResearch.WordTrace]
  refine ⟨22205380235367461510624705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14803586823578307673749803 22205380235367461510624705)
  ·
    refine ⟨16654035176525596132968529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22205380235367461510624705 16654035176525596132968529)
    ·
      refine ⟨12490526382394197099726397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16654035176525596132968529 12490526382394197099726397)
      ·
        refine ⟨4683947393397823912397399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12490526382394197099726397 4683947393397823912397399)
        ·
          refine ⟨7025921090096735868596099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4683947393397823912397399 7025921090096735868596099)
          ·
            refine ⟨10538881635145103802894149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7025921090096735868596099 10538881635145103802894149)
            ·
              refine ⟨1976040306589706963042653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10538881635145103802894149 1976040306589706963042653)
              ·
                refine ⟨741015114971140111140995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1976040306589706963042653 741015114971140111140995)
                ·
                  refine ⟨1111522672456710166711493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 741015114971140111140995 1111522672456710166711493)
                  ·
                    refine ⟨208410501085633156258405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1111522672456710166711493 208410501085633156258405)
                    ·
                      rfl

theorem cell22_608817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 4, 3, 1, 4].length) (baseStart_608817 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_608817 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_608817 prefixEnd_608817 := by exact prefixLift 608817
  have htrace : WordTrace (prefixWord ++ tailWord_608817) baseStart_608817 baseEnd_608817 := by
    simpa [prefixWord, tailWord_608817, baseEnd_608817] using wordTrace_append hprefix tailTrace_608817
  have hstable : (prefixWord ++ tailWord_608817).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_608817).length < 2 ^ (prefixWord ++ tailWord_608817).sum := by decide
  have hdescent : baseEnd_608817 < baseStart_608817 := by decide
  rcases family_descends (prefixWord ++ tailWord_608817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_608832 : List Nat := [2, 1, 1, 2, 2, 2, 2, 6, 4]
def baseStart_608832 : Nat := 118140960795 + 608832 * 2 ^ 59
def prefixEnd_608832 : Nat := 4983230072969 + 3 ^ 40 * 608832 * 2
def baseEnd_608832 : Nat := 69471878630726039044453

theorem tailTrace_608832 : CollatzResearch.WordTrace tailWord_608832 prefixEnd_608832 69471878630726039044453 := by
  unfold tailWord_608832
  simp only [CollatzResearch.WordTrace]
  refine ⟨11102963665156559536210375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14803951553542079381613833 11102963665156559536210375)
  ·
    refine ⟨16654445497734839304315563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11102963665156559536210375 16654445497734839304315563)
    ·
      refine ⟨24981668246602258956473345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16654445497734839304315563 24981668246602258956473345)
      ·
        refine ⟨18736251184951694217355009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24981668246602258956473345 18736251184951694217355009)
        ·
          refine ⟨14052188388713770663016257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18736251184951694217355009 14052188388713770663016257)
          ·
            refine ⟨10539141291535327997262193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14052188388713770663016257 10539141291535327997262193)
            ·
              refine ⟨7904355968651495997946645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10539141291535327997262193 7904355968651495997946645)
              ·
                refine ⟨370516686030538874903749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 7904355968651495997946645 370516686030538874903749)
                ·
                  refine ⟨69471878630726039044453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 370516686030538874903749 69471878630726039044453)
                  ·
                    rfl

theorem cell22_608832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 2, 6, 4].length) (baseStart_608832 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_608832 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_608832 prefixEnd_608832 := by exact prefixLift 608832
  have htrace : WordTrace (prefixWord ++ tailWord_608832) baseStart_608832 baseEnd_608832 := by
    simpa [prefixWord, tailWord_608832, baseEnd_608832] using wordTrace_append hprefix tailTrace_608832
  have hstable : (prefixWord ++ tailWord_608832).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_608832).length < 2 ^ (prefixWord ++ tailWord_608832).sum := by decide
  have hdescent : baseEnd_608832 < baseStart_608832 := by decide
  rcases family_descends (prefixWord ++ tailWord_608832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_608838 : List Nat := [6, 1, 1, 1, 2, 3, 2, 1, 5]
def baseStart_608838 : Nat := 118140960795 + 608838 * 2 ^ 59
def prefixEnd_608838 : Nat := 4983230072969 + 3 ^ 40 * 608838 * 2
def baseEnd_608838 : Nat := 69472563271598700494447

theorem tailTrace_608838 : CollatzResearch.WordTrace tailWord_608838 prefixEnd_608838 69472563271598700494447 := by
  unfold tailWord_608838
  simp only [CollatzResearch.WordTrace]
  refine ⟨693942067759105690535599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 14804097445527588064759445 693942067759105690535599)
  ·
    refine ⟨1040913101638658535803399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 693942067759105690535599 1040913101638658535803399)
    ·
      refine ⟨1561369652457987803705099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1040913101638658535803399 1561369652457987803705099)
      ·
        refine ⟨2342054478686981705557649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1561369652457987803705099 2342054478686981705557649)
        ·
          refine ⟨1756540859015236279168237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2342054478686981705557649 1756540859015236279168237)
          ·
            refine ⟨658702822130713604688089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1756540859015236279168237 658702822130713604688089)
            ·
              refine ⟨494027116598035203516067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 658702822130713604688089 494027116598035203516067)
              ·
                refine ⟨741040674897052805274101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 494027116598035203516067 741040674897052805274101)
                ·
                  refine ⟨69472563271598700494447, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 741040674897052805274101 69472563271598700494447)
                  ·
                    rfl

theorem cell22_608838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 3, 2, 1, 5].length) (baseStart_608838 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_608838 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_608838 prefixEnd_608838 := by exact prefixLift 608838
  have htrace : WordTrace (prefixWord ++ tailWord_608838) baseStart_608838 baseEnd_608838 := by
    simpa [prefixWord, tailWord_608838, baseEnd_608838] using wordTrace_append hprefix tailTrace_608838
  have hstable : (prefixWord ++ tailWord_608838).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_608838).length < 2 ^ (prefixWord ++ tailWord_608838).sum := by decide
  have hdescent : baseEnd_608838 < baseStart_608838 := by decide
  rcases family_descends (prefixWord ++ tailWord_608838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_608905 : List Nat := [1, 2, 1, 1, 4, 1, 1, 2, 9]
def baseStart_608905 : Nat := 118140960795 + 608905 * 2 ^ 59
def prefixEnd_608905 : Nat := 4983230072969 + 3 ^ 40 * 608905 * 2
def baseEnd_608905 : Nat := 69480208428010086686045

theorem tailTrace_608905 : CollatzResearch.WordTrace tailWord_608905 prefixEnd_608905 69480208428010086686045 := by
  unfold tailWord_608905
  simp only [CollatzResearch.WordTrace]
  refine ⟨22208589859048652539828169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14805726572699101693218779 22208589859048652539828169)
  ·
    refine ⟨16656442394286489404871127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22208589859048652539828169 16656442394286489404871127)
    ·
      refine ⟨24984663591429734107306691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16656442394286489404871127 24984663591429734107306691)
      ·
        refine ⟨37476995387144601160960037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24984663591429734107306691 37476995387144601160960037)
        ·
          refine ⟨7026936635089612717680007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 37476995387144601160960037 7026936635089612717680007)
          ·
            refine ⟨10540404952634419076520011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7026936635089612717680007 10540404952634419076520011)
            ·
              refine ⟨15810607428951628614780017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10540404952634419076520011 15810607428951628614780017)
              ·
                refine ⟨11857955571713721461085013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15810607428951628614780017 11857955571713721461085013)
                ·
                  refine ⟨69480208428010086686045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 11857955571713721461085013 69480208428010086686045)
                  ·
                    rfl

theorem cell22_608905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 2, 9].length) (baseStart_608905 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_608905 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_608905 prefixEnd_608905 := by exact prefixLift 608905
  have htrace : WordTrace (prefixWord ++ tailWord_608905) baseStart_608905 baseEnd_608905 := by
    simpa [prefixWord, tailWord_608905, baseEnd_608905] using wordTrace_append hprefix tailTrace_608905
  have hstable : (prefixWord ++ tailWord_608905).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_608905).length < 2 ^ (prefixWord ++ tailWord_608905).sum := by decide
  have hdescent : baseEnd_608905 < baseStart_608905 := by decide
  rcases family_descends (prefixWord ++ tailWord_608905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_609014 : List Nat := [5, 1, 1, 1, 1, 2, 1, 2, 4, 4]
def baseStart_609014 : Nat := 118140960795 + 609014 * 2 ^ 59
def prefixEnd_609014 : Nat := 4983230072969 + 3 ^ 40 * 609014 * 2
def baseEnd_609014 : Nat := 208477938211590309082801

theorem tailTrace_609014 : CollatzResearch.WordTrace tailWord_609014 prefixEnd_609014 208477938211590309082801 := by
  unfold tailWord_609014
  simp only [CollatzResearch.WordTrace]
  refine ⟨1388285338478360259721631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 14808376943769176103697397 1388285338478360259721631)
  ·
    refine ⟨2082428007717540389582447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1388285338478360259721631 2082428007717540389582447)
    ·
      refine ⟨3123642011576310584373671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2082428007717540389582447 3123642011576310584373671)
      ·
        refine ⟨4685463017364465876560507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3123642011576310584373671 4685463017364465876560507)
        ·
          refine ⟨7028194526046698814840761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4685463017364465876560507 7028194526046698814840761)
          ·
            refine ⟨5271145894535024111130571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7028194526046698814840761 5271145894535024111130571)
            ·
              refine ⟨7906718841802536166695857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5271145894535024111130571 7906718841802536166695857)
              ·
                refine ⟨5930039131351902125021893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7906718841802536166695857 5930039131351902125021893)
                ·
                  refine ⟨1111882337128481648441605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5930039131351902125021893 1111882337128481648441605)
                  ·
                    refine ⟨208477938211590309082801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1111882337128481648441605 208477938211590309082801)
                    ·
                      rfl

theorem cell22_609014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 1, 2, 4, 4].length) (baseStart_609014 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_609014 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_609014 prefixEnd_609014 := by exact prefixLift 609014
  have htrace : WordTrace (prefixWord ++ tailWord_609014) baseStart_609014 baseEnd_609014 := by
    simpa [prefixWord, tailWord_609014, baseEnd_609014] using wordTrace_append hprefix tailTrace_609014
  have hstable : (prefixWord ++ tailWord_609014).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_609014).length < 2 ^ (prefixWord ++ tailWord_609014).sum := by decide
  have hdescent : baseEnd_609014 < baseStart_609014 := by decide
  rcases family_descends (prefixWord ++ tailWord_609014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_609031 : List Nat := [1, 1, 4, 4, 1, 2, 2, 1, 2, 4]
def baseStart_609031 : Nat := 118140960795 + 609031 * 2 ^ 59
def prefixEnd_609031 : Nat := 4983230072969 + 3 ^ 40 * 609031 * 2
def baseEnd_609031 : Nat := 208483757659007931407749

theorem tailTrace_609031 : CollatzResearch.WordTrace tailWord_609031 prefixEnd_609031 208483757659007931407749 := by
  unfold tailWord_609031
  simp only [CollatzResearch.WordTrace]
  refine ⟨22213185456592176058914947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14808790304394784039276631 22213185456592176058914947)
  ·
    refine ⟨33319778184888264088372421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22213185456592176058914947 33319778184888264088372421)
    ·
      refine ⟨6247458409666549516569829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 33319778184888264088372421 6247458409666549516569829)
      ·
        refine ⟨1171398451812478034356843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6247458409666549516569829 1171398451812478034356843)
        ·
          refine ⟨1757097677718717051535265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1171398451812478034356843 1757097677718717051535265)
          ·
            refine ⟨1317823258289037788651449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1757097677718717051535265 1317823258289037788651449)
            ·
              refine ⟨988367443716778341488587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1317823258289037788651449 988367443716778341488587)
              ·
                refine ⟨1482551165575167512232881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 988367443716778341488587 1482551165575167512232881)
                ·
                  refine ⟨1111913374181375634174661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1482551165575167512232881 1111913374181375634174661)
                  ·
                    refine ⟨208483757659007931407749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1111913374181375634174661 208483757659007931407749)
                    ·
                      rfl

theorem cell22_609031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 2, 2, 1, 2, 4].length) (baseStart_609031 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_609031 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_609031 prefixEnd_609031 := by exact prefixLift 609031
  have htrace : WordTrace (prefixWord ++ tailWord_609031) baseStart_609031 baseEnd_609031 := by
    simpa [prefixWord, tailWord_609031, baseEnd_609031] using wordTrace_append hprefix tailTrace_609031
  have hstable : (prefixWord ++ tailWord_609031).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_609031).length < 2 ^ (prefixWord ++ tailWord_609031).sum := by decide
  have hdescent : baseEnd_609031 < baseStart_609031 := by decide
  rcases family_descends (prefixWord ++ tailWord_609031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_609074 : List Nat := [3, 2, 1, 1, 3, 1, 1, 5, 5]
def baseStart_609074 : Nat := 118140960795 + 609074 * 2 ^ 59
def prefixEnd_609074 : Nat := 4983230072969 + 3 ^ 40 * 609074 * 2
def baseEnd_609074 : Nat := 69499492479256717527539

theorem tailTrace_609074 : CollatzResearch.WordTrace tailWord_609074 prefixEnd_609074 69499492479256717527539 := by
  unfold tailWord_609074
  simp only [CollatzResearch.WordTrace]
  refine ⟨5553688448859098600682569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14809835863624262935153517 5553688448859098600682569)
  ·
    refine ⟨4165266336644323950511927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5553688448859098600682569 4165266336644323950511927)
    ·
      refine ⟨6247899504966485925767891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4165266336644323950511927 6247899504966485925767891)
      ·
        refine ⟨9371849257449728888651837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6247899504966485925767891 9371849257449728888651837)
        ·
          refine ⟨3514443471543648333244439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9371849257449728888651837 3514443471543648333244439)
          ·
            refine ⟨5271665207315472499866659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3514443471543648333244439 5271665207315472499866659)
            ·
              refine ⟨7907497810973208749799989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5271665207315472499866659 7907497810973208749799989)
              ·
                refine ⟨741327919778738320293749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 7907497810973208749799989 741327919778738320293749)
                ·
                  refine ⟨69499492479256717527539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 741327919778738320293749 69499492479256717527539)
                  ·
                    rfl

theorem cell22_609074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 1, 5, 5].length) (baseStart_609074 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_609074 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_609074 prefixEnd_609074 := by exact prefixLift 609074
  have htrace : WordTrace (prefixWord ++ tailWord_609074) baseStart_609074 baseEnd_609074 := by
    simpa [prefixWord, tailWord_609074, baseEnd_609074] using wordTrace_append hprefix tailTrace_609074
  have hstable : (prefixWord ++ tailWord_609074).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_609074).length < 2 ^ (prefixWord ++ tailWord_609074).sum := by decide
  have hdescent : baseEnd_609074 < baseStart_609074 := by decide
  rcases family_descends (prefixWord ++ tailWord_609074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_609108 : List Nat := [2, 4, 1, 1, 4, 2, 1, 2, 5]
def baseStart_609108 : Nat := 118140960795 + 609108 * 2 ^ 59
def prefixEnd_609108 : Nat := 4983230072969 + 3 ^ 40 * 609108 * 2
def baseEnd_609108 : Nat := 69503372110868465744171

theorem tailTrace_609108 : CollatzResearch.WordTrace tailWord_609108 prefixEnd_609108 69503372110868465744171 := by
  unfold tailWord_609108
  simp only [CollatzResearch.WordTrace]
  refine ⟨11107996938656609104733989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14810662584875478806311985 11107996938656609104733989)
  ·
    refine ⟨2082749425998114207137623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11107996938656609104733989 2082749425998114207137623)
    ·
      refine ⟨3124124138997171310706435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2082749425998114207137623 3124124138997171310706435)
      ·
        refine ⟨4686186208495756966059653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3124124138997171310706435 4686186208495756966059653)
        ·
          refine ⟨878659914092954431136185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4686186208495756966059653 878659914092954431136185)
          ·
            refine ⟨658994935569715823352139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 878659914092954431136185 658994935569715823352139)
            ·
              refine ⟨988492403354573735028209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 658994935569715823352139 988492403354573735028209)
              ·
                refine ⟨741369302515930301271157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 988492403354573735028209 741369302515930301271157)
                ·
                  refine ⟨69503372110868465744171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 741369302515930301271157 69503372110868465744171)
                  ·
                    rfl

theorem cell22_609108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 2, 1, 2, 5].length) (baseStart_609108 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_609108 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_609108 prefixEnd_609108 := by exact prefixLift 609108
  have htrace : WordTrace (prefixWord ++ tailWord_609108) baseStart_609108 baseEnd_609108 := by
    simpa [prefixWord, tailWord_609108, baseEnd_609108] using wordTrace_append hprefix tailTrace_609108
  have hstable : (prefixWord ++ tailWord_609108).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_609108).length < 2 ^ (prefixWord ++ tailWord_609108).sum := by decide
  have hdescent : baseEnd_609108 < baseStart_609108 := by decide
  rcases family_descends (prefixWord ++ tailWord_609108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_609119 : List Nat := [1, 1, 2, 3, 1, 3, 4, 1, 6]
def baseStart_609119 : Nat := 118140960795 + 609119 * 2 ^ 59
def prefixEnd_609119 : Nat := 4983230072969 + 3 ^ 40 * 609119 * 2
def baseEnd_609119 : Nat := 69504627285801678402493

theorem tailTrace_609119 : CollatzResearch.WordTrace tailWord_609119 prefixEnd_609119 69504627285801678402493 := by
  unfold tailWord_609119
  simp only [CollatzResearch.WordTrace]
  refine ⟨22216395080273367088118411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14810930053515578058745607 22216395080273367088118411)
  ·
    refine ⟨33324592620410050632177617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22216395080273367088118411 33324592620410050632177617)
    ·
      refine ⟨24993444465307537974133213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33324592620410050632177617 24993444465307537974133213)
      ·
        refine ⟨9372541674490326740299955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24993444465307537974133213 9372541674490326740299955)
        ·
          refine ⟨14058812511735490110449933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9372541674490326740299955 14058812511735490110449933)
          ·
            refine ⟨5272054691900808791418725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14058812511735490110449933 5272054691900808791418725)
            ·
              refine ⟨988510254731401648391011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5272054691900808791418725 988510254731401648391011)
              ·
                refine ⟨1482765382097102472586517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 988510254731401648391011 1482765382097102472586517)
                ·
                  refine ⟨69504627285801678402493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1482765382097102472586517 69504627285801678402493)
                  ·
                    rfl

theorem cell22_609119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 4, 1, 6].length) (baseStart_609119 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_609119 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_609119 prefixEnd_609119 := by exact prefixLift 609119
  have htrace : WordTrace (prefixWord ++ tailWord_609119) baseStart_609119 baseEnd_609119 := by
    simpa [prefixWord, tailWord_609119, baseEnd_609119] using wordTrace_append hprefix tailTrace_609119
  have hstable : (prefixWord ++ tailWord_609119).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_609119).length < 2 ^ (prefixWord ++ tailWord_609119).sum := by decide
  have hdescent : baseEnd_609119 < baseStart_609119 := by decide
  rcases family_descends (prefixWord ++ tailWord_609119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_609149 : List Nat := [1, 4, 1, 1, 2, 1, 4, 1, 1, 6]
def baseStart_609149 : Nat := 118140960795 + 609149 * 2 ^ 59
def prefixEnd_609149 : Nat := 4983230072969 + 3 ^ 40 * 609149 * 2
def baseEnd_609149 : Nat := 208524151470494956957387

theorem tailTrace_609149 : CollatzResearch.WordTrace tailWord_609149 prefixEnd_609149 208524151470494956957387 := by
  unfold tailWord_609149
  simp only [CollatzResearch.WordTrace]
  refine ⟨22217489270164682211710501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14811659513443121474473667 22217489270164682211710501)
  ·
    refine ⟨4165779238155877914695719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 22217489270164682211710501 4165779238155877914695719)
    ·
      refine ⟨6248668857233816872043579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4165779238155877914695719 6248668857233816872043579)
      ·
        refine ⟨9373003285850725308065369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6248668857233816872043579 9373003285850725308065369)
        ·
          refine ⟨7029752464388043981049027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9373003285850725308065369 7029752464388043981049027)
          ·
            refine ⟨10544628696582065971573541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7029752464388043981049027 10544628696582065971573541)
            ·
              refine ⟨1977117880609137369670039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10544628696582065971573541 1977117880609137369670039)
              ·
                refine ⟨2965676820913706054505059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1977117880609137369670039 2965676820913706054505059)
                ·
                  refine ⟨4448515231370559081757589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2965676820913706054505059 4448515231370559081757589)
                  ·
                    refine ⟨208524151470494956957387, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4448515231370559081757589 208524151470494956957387)
                    ·
                      rfl

theorem cell22_609149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 4, 1, 1, 6].length) (baseStart_609149 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_609149 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_609149 prefixEnd_609149 := by exact prefixLift 609149
  have htrace : WordTrace (prefixWord ++ tailWord_609149) baseStart_609149 baseEnd_609149 := by
    simpa [prefixWord, tailWord_609149, baseEnd_609149] using wordTrace_append hprefix tailTrace_609149
  have hstable : (prefixWord ++ tailWord_609149).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_609149).length < 2 ^ (prefixWord ++ tailWord_609149).sum := by decide
  have hdescent : baseEnd_609149 < baseStart_609149 := by decide
  rcases family_descends (prefixWord ++ tailWord_609149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_609170 : List Nat := [3, 2, 3, 2, 3, 1, 1, 1, 6]
def baseStart_609170 : Nat := 118140960795 + 609170 * 2 ^ 59
def prefixEnd_609170 : Nat := 4983230072969 + 3 ^ 40 * 609170 * 2
def baseEnd_609170 : Nat := 69510446733219300727441

theorem tailTrace_609170 : CollatzResearch.WordTrace tailWord_609170 prefixEnd_609170 69510446733219300727441 := by
  unfold tailWord_609170
  simp only [CollatzResearch.WordTrace]
  refine ⟨5554563800772150699556241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14812170135392401865483309 5554563800772150699556241)
  ·
    refine ⟨4165922850579113024667181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5554563800772150699556241 4165922850579113024667181)
    ·
      refine ⟨1562221068967167384250193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4165922850579113024667181 1562221068967167384250193)
      ·
        refine ⟨1171665801725375538187645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1562221068967167384250193 1171665801725375538187645)
        ·
          refine ⟨439374675647015826820367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1171665801725375538187645 439374675647015826820367)
          ·
            refine ⟨659062013470523740230551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 439374675647015826820367 659062013470523740230551)
            ·
              refine ⟨988593020205785610345827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 659062013470523740230551 988593020205785610345827)
              ·
                refine ⟨1482889530308678415518741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 988593020205785610345827 1482889530308678415518741)
                ·
                  refine ⟨69510446733219300727441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1482889530308678415518741 69510446733219300727441)
                  ·
                    rfl

theorem cell22_609170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 3, 1, 1, 1, 6].length) (baseStart_609170 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_609170 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_609170 prefixEnd_609170 := by exact prefixLift 609170
  have htrace : WordTrace (prefixWord ++ tailWord_609170) baseStart_609170 baseEnd_609170 := by
    simpa [prefixWord, tailWord_609170, baseEnd_609170] using wordTrace_append hprefix tailTrace_609170
  have hstable : (prefixWord ++ tailWord_609170).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_609170).length < 2 ^ (prefixWord ++ tailWord_609170).sum := by decide
  have hdescent : baseEnd_609170 < baseStart_609170 := by decide
  rcases family_descends (prefixWord ++ tailWord_609170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_609185 : List Nat := [1, 2, 3, 4, 1, 1, 4, 1, 2, 3]
def baseStart_609185 : Nat := 118140960795 + 609185 * 2 ^ 59
def prefixEnd_609185 : Nat := 4983230072969 + 3 ^ 40 * 609185 * 2
def baseEnd_609185 : Nat := 208536475006202863057277

theorem tailTrace_609185 : CollatzResearch.WordTrace tailWord_609185 prefixEnd_609185 208536475006202863057277 := by
  unfold tailWord_609185
  simp only [CollatzResearch.WordTrace]
  refine ⟨22218802298034260360021009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14812534865356173573347339 22218802298034260360021009)
  ·
    refine ⟨16664101723525695270015757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22218802298034260360021009 16664101723525695270015757)
    ·
      refine ⟨6249038146322135726255909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16664101723525695270015757 6249038146322135726255909)
      ·
        refine ⟨1171694652435400448672983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6249038146322135726255909 1171694652435400448672983)
        ·
          refine ⟨1757541978653100673009475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1171694652435400448672983 1757541978653100673009475)
          ·
            refine ⟨2636312967979651009514213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1757541978653100673009475 2636312967979651009514213)
            ·
              refine ⟨494308681496184564283915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2636312967979651009514213 494308681496184564283915)
              ·
                refine ⟨741463022244276846425873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 494308681496184564283915 741463022244276846425873)
                ·
                  refine ⟨556097266683207634819405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 741463022244276846425873 556097266683207634819405)
                  ·
                    refine ⟨208536475006202863057277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 556097266683207634819405 208536475006202863057277)
                    ·
                      rfl

theorem cell22_609185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 4, 1, 2, 3].length) (baseStart_609185 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_609185 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_609185 prefixEnd_609185 := by exact prefixLift 609185
  have htrace : WordTrace (prefixWord ++ tailWord_609185) baseStart_609185 baseEnd_609185 := by
    simpa [prefixWord, tailWord_609185, baseEnd_609185] using wordTrace_append hprefix tailTrace_609185
  have hstable : (prefixWord ++ tailWord_609185).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_609185).length < 2 ^ (prefixWord ++ tailWord_609185).sum := by decide
  have hdescent : baseEnd_609185 < baseStart_609185 := by decide
  rcases family_descends (prefixWord ++ tailWord_609185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_609230 : List Nat := [4, 1, 1, 1, 2, 4, 1, 4, 1, 3]
def baseStart_609230 : Nat := 118140960795 + 609230 * 2 ^ 59
def prefixEnd_609230 : Nat := 4983230072969 + 3 ^ 40 * 609230 * 2
def baseEnd_609230 : Nat := 208551879425837745682139

theorem tailTrace_609230 : CollatzResearch.WordTrace tailWord_609230 prefixEnd_609230 208551879425837745682139 := by
  unfold tailWord_609230
  simp only [CollatzResearch.WordTrace]
  refine ⟨2777555447858904130676143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14813629055247488696939429 2777555447858904130676143)
  ·
    refine ⟨4166333171788356196014215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2777555447858904130676143 4166333171788356196014215)
    ·
      refine ⟨6249499757682534294021323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4166333171788356196014215 6249499757682534294021323)
      ·
        refine ⟨9374249636523801441031985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6249499757682534294021323 9374249636523801441031985)
        ·
          refine ⟨7030687227392851080773989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9374249636523801441031985 7030687227392851080773989)
          ·
            refine ⟨1318253855136159577645123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7030687227392851080773989 1318253855136159577645123)
            ·
              refine ⟨1977380782704239366467685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1318253855136159577645123 1977380782704239366467685)
              ·
                refine ⟨370758896757044881212691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1977380782704239366467685 370758896757044881212691)
                ·
                  refine ⟨556138345135567321819037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 370758896757044881212691 556138345135567321819037)
                  ·
                    refine ⟨208551879425837745682139, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 556138345135567321819037 208551879425837745682139)
                    ·
                      rfl

theorem cell22_609230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 4, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 4, 1, 4, 1, 3].length) (baseStart_609230 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_609230 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_609230 prefixEnd_609230 := by exact prefixLift 609230
  have htrace : WordTrace (prefixWord ++ tailWord_609230) baseStart_609230 baseEnd_609230 := by
    simpa [prefixWord, tailWord_609230, baseEnd_609230] using wordTrace_append hprefix tailTrace_609230
  have hstable : (prefixWord ++ tailWord_609230).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_609230).length < 2 ^ (prefixWord ++ tailWord_609230).sum := by decide
  have hdescent : baseEnd_609230 < baseStart_609230 := by decide
  rcases family_descends (prefixWord ++ tailWord_609230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_609241 : List Nat := [1, 2, 1, 2, 5, 2, 1, 1, 2, 5]
def baseStart_609241 : Nat := 118140960795 + 609241 * 2 ^ 59
def prefixEnd_609241 : Nat := 4983230072969 + 3 ^ 40 * 609241 * 2
def baseEnd_609241 : Nat := 208555644950637383657105

theorem tailTrace_609241 : CollatzResearch.WordTrace tailWord_609241 prefixEnd_609241 208555644950637383657105 := by
  unfold tailWord_609241
  simp only [CollatzResearch.WordTrace]
  refine ⟨22220844785831381924059577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14813896523887587949373051 22220844785831381924059577)
  ·
    refine ⟨16665633589373536443044683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22220844785831381924059577 16665633589373536443044683)
    ·
      refine ⟨24998450384060304664567025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16665633589373536443044683 24998450384060304664567025)
      ·
        refine ⟨18748837788045228498425269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24998450384060304664567025 18748837788045228498425269)
        ·
          refine ⟨1757703542629240171727369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 18748837788045228498425269 1757703542629240171727369)
          ·
            refine ⟨1318277656971930128795527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1757703542629240171727369 1318277656971930128795527)
            ·
              refine ⟨1977416485457895193193291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1318277656971930128795527 1977416485457895193193291)
              ·
                refine ⟨2966124728186842789789937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1977416485457895193193291 2966124728186842789789937)
                ·
                  refine ⟨2224593546140132092342453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2966124728186842789789937 2224593546140132092342453)
                  ·
                    refine ⟨208555644950637383657105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2224593546140132092342453 208555644950637383657105)
                    ·
                      rfl

theorem cell22_609241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 2, 1, 1, 2, 5].length) (baseStart_609241 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_609241 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_609241 prefixEnd_609241 := by exact prefixLift 609241
  have htrace : WordTrace (prefixWord ++ tailWord_609241) baseStart_609241 baseEnd_609241 := by
    simpa [prefixWord, tailWord_609241, baseEnd_609241] using wordTrace_append hprefix tailTrace_609241
  have hstable : (prefixWord ++ tailWord_609241).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_609241).length < 2 ^ (prefixWord ++ tailWord_609241).sum := by decide
  have hdescent : baseEnd_609241 < baseStart_609241 := by decide
  rcases family_descends (prefixWord ++ tailWord_609241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_609256 : List Nat := [2, 1, 4, 1, 1, 1, 4, 1, 3, 4]
def baseStart_609256 : Nat := 118140960795 + 609256 * 2 ^ 59
def prefixEnd_609256 : Nat := 4983230072969 + 3 ^ 40 * 609256 * 2
def baseEnd_609256 : Nat := 208560779757182344532059

theorem tailTrace_609256 : CollatzResearch.WordTrace tailWord_609256 prefixEnd_609256 208560779757182344532059 := by
  unfold tailWord_609256
  simp only [CollatzResearch.WordTrace]
  refine ⟨11110695940388519742927811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14814261253851359657237081 11110695940388519742927811)
  ·
    refine ⟨16666043910582779614391717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11110695940388519742927811 16666043910582779614391717)
    ·
      refine ⟨3124883233234271177698447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 16666043910582779614391717 3124883233234271177698447)
      ·
        refine ⟨4687324849851406766547671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3124883233234271177698447 4687324849851406766547671)
        ·
          refine ⟨7030987274777110149821507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4687324849851406766547671 7030987274777110149821507)
          ·
            refine ⟨10546480912165665224732261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7030987274777110149821507 10546480912165665224732261)
            ·
              refine ⟨1977465171031062229637299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10546480912165665224732261 1977465171031062229637299)
              ·
                refine ⟨2966197756546593344455949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1977465171031062229637299 2966197756546593344455949)
                ·
                  refine ⟨1112324158704972504170981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2966197756546593344455949 1112324158704972504170981)
                  ·
                    refine ⟨208560779757182344532059, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1112324158704972504170981 208560779757182344532059)
                    ·
                      rfl

theorem cell22_609256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 4, 1, 3, 4].length) (baseStart_609256 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_609256 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_609256 prefixEnd_609256 := by exact prefixLift 609256
  have htrace : WordTrace (prefixWord ++ tailWord_609256) baseStart_609256 baseEnd_609256 := by
    simpa [prefixWord, tailWord_609256, baseEnd_609256] using wordTrace_append hprefix tailTrace_609256
  have hstable : (prefixWord ++ tailWord_609256).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_609256).length < 2 ^ (prefixWord ++ tailWord_609256).sum := by decide
  have hdescent : baseEnd_609256 < baseStart_609256 := by decide
  rcases family_descends (prefixWord ++ tailWord_609256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_609288 : List Nat := [2, 1, 3, 2, 1, 3, 2, 4, 4]
def baseStart_609288 : Nat := 118140960795 + 609288 * 2 ^ 59
def prefixEnd_609288 : Nat := 4983230072969 + 3 ^ 40 * 609288 * 2
def baseEnd_609288 : Nat := 69523911337048309243987

theorem tailTrace_609288 : CollatzResearch.WordTrace tailWord_609288 prefixEnd_609288 69523911337048309243987 := by
  unfold tailWord_609288
  simp only [CollatzResearch.WordTrace]
  refine ⟨11111279508330554475510259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14815039344440739300680345 11111279508330554475510259)
  ·
    refine ⟨16666919262495831713265389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11111279508330554475510259 16666919262495831713265389)
    ·
      refine ⟨6250094723435936892474521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16666919262495831713265389 6250094723435936892474521)
      ·
        refine ⟨4687571042576952669355891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6250094723435936892474521 4687571042576952669355891)
        ·
          refine ⟨7031356563865429004033837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4687571042576952669355891 7031356563865429004033837)
          ·
            refine ⟨2636758711449535876512689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7031356563865429004033837 2636758711449535876512689)
            ·
              refine ⟨1977569033587151907384517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2636758711449535876512689 1977569033587151907384517)
              ·
                refine ⟨370794193797590982634597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1977569033587151907384517 370794193797590982634597)
                ·
                  refine ⟨69523911337048309243987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 370794193797590982634597 69523911337048309243987)
                  ·
                    rfl

theorem cell22_609288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 2, 4, 4].length) (baseStart_609288 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_609288 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_609288 prefixEnd_609288 := by exact prefixLift 609288
  have htrace : WordTrace (prefixWord ++ tailWord_609288) baseStart_609288 baseEnd_609288 := by
    simpa [prefixWord, tailWord_609288, baseEnd_609288] using wordTrace_append hprefix tailTrace_609288
  have hstable : (prefixWord ++ tailWord_609288).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_609288).length < 2 ^ (prefixWord ++ tailWord_609288).sum := by decide
  have hdescent : baseEnd_609288 < baseStart_609288 := by decide
  rcases family_descends (prefixWord ++ tailWord_609288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_609299 : List Nat := [1, 1, 1, 2, 1, 4, 1, 11]
def baseStart_609299 : Nat := 118140960795 + 609299 * 2 ^ 59
def prefixEnd_609299 : Nat := 4983230072969 + 3 ^ 40 * 609299 * 2
def baseEnd_609299 : Nat := 23175055503993840634103

theorem tailTrace_609299 : CollatzResearch.WordTrace tailWord_609299 prefixEnd_609299 23175055503993840634103 := by
  unfold tailWord_609299
  simp only [CollatzResearch.WordTrace]
  refine ⟨22222960219621257829670951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14815306813080838553113967 22222960219621257829670951)
  ·
    refine ⟨33334440329431886744506427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22222960219621257829670951 33334440329431886744506427)
    ·
      refine ⟨50001660494147830116759641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33334440329431886744506427 50001660494147830116759641)
      ·
        refine ⟨37501245370610872587569731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50001660494147830116759641 37501245370610872587569731)
        ·
          refine ⟨56251868055916308881354597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37501245370610872587569731 56251868055916308881354597)
          ·
            refine ⟨10547225260484307915253987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 56251868055916308881354597 10547225260484307915253987)
            ·
              refine ⟨15820837890726461872880981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10547225260484307915253987 15820837890726461872880981)
              ·
                refine ⟨23175055503993840634103, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 15820837890726461872880981 23175055503993840634103)
                ·
                  rfl

theorem cell22_609299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 11].length) (baseStart_609299 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_609299 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_609299 prefixEnd_609299 := by exact prefixLift 609299
  have htrace : WordTrace (prefixWord ++ tailWord_609299) baseStart_609299 baseEnd_609299 := by
    simpa [prefixWord, tailWord_609299, baseEnd_609299] using wordTrace_append hprefix tailTrace_609299
  have hstable : (prefixWord ++ tailWord_609299).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_609299).length < 2 ^ (prefixWord ++ tailWord_609299).sum := by decide
  have hdescent : baseEnd_609299 < baseStart_609299 := by decide
  rcases family_descends (prefixWord ++ tailWord_609299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_609301 : List Nat := [1, 3, 2, 1, 4, 1, 1, 2, 1, 6]
def baseStart_609301 : Nat := 118140960795 + 609301 * 2 ^ 59
def prefixEnd_609301 : Nat := 4983230072969 + 3 ^ 40 * 609301 * 2
def baseEnd_609301 : Nat := 208576184176817227156921

theorem tailTrace_609301 : CollatzResearch.WordTrace tailWord_609301 prefixEnd_609301 208576184176817227156921 := by
  unfold tailWord_609301
  simp only [CollatzResearch.WordTrace]
  refine ⟨22223033165614012171243757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14815355443742674780829171 22223033165614012171243757)
  ·
    refine ⟨8333637437105254564216409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22223033165614012171243757 8333637437105254564216409)
    ·
      refine ⟨6250228077828940923162307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8333637437105254564216409 6250228077828940923162307)
      ·
        refine ⟨9375342116743411384743461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6250228077828940923162307 9375342116743411384743461)
        ·
          refine ⟨1757876646889389634639399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9375342116743411384743461 1757876646889389634639399)
          ·
            refine ⟨2636814970334084451959099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1757876646889389634639399 2636814970334084451959099)
            ·
              refine ⟨3955222455501126677938649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2636814970334084451959099 3955222455501126677938649)
              ·
                refine ⟨2966416841625845008453987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3955222455501126677938649 2966416841625845008453987)
                ·
                  refine ⟨4449625262438767512680981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2966416841625845008453987 4449625262438767512680981)
                  ·
                    refine ⟨208576184176817227156921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4449625262438767512680981 208576184176817227156921)
                    ·
                      rfl

theorem cell22_609301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 1, 2, 1, 6].length) (baseStart_609301 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_609301 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_609301 prefixEnd_609301 := by exact prefixLift 609301
  have htrace : WordTrace (prefixWord ++ tailWord_609301) baseStart_609301 baseEnd_609301 := by
    simpa [prefixWord, tailWord_609301, baseEnd_609301] using wordTrace_append hprefix tailTrace_609301
  have hstable : (prefixWord ++ tailWord_609301).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_609301).length < 2 ^ (prefixWord ++ tailWord_609301).sum := by decide
  have hdescent : baseEnd_609301 < baseStart_609301 := by decide
  rcases family_descends (prefixWord ++ tailWord_609301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_609303 : List Nat := [1, 1, 3, 5, 1, 1, 3, 1, 1, 5]
def baseStart_609303 : Nat := 118140960795 + 609303 * 2 ^ 59
def prefixEnd_609303 : Nat := 4983230072969 + 3 ^ 40 * 609303 * 2
def baseEnd_609303 : Nat := 208576868817689888606915

theorem tailTrace_609303 : CollatzResearch.WordTrace tailWord_609303 prefixEnd_609303 208576868817689888606915 := by
  unfold tailWord_609303
  simp only [CollatzResearch.WordTrace]
  refine ⟨22223106111606766512816563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14815404074404511008544375 22223106111606766512816563)
  ·
    refine ⟨33334659167410149769224845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22223106111606766512816563 33334659167410149769224845)
    ·
      refine ⟨12500497187778806163459317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33334659167410149769224845 12500497187778806163459317)
      ·
        refine ⟨1171921611354263077824311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 12500497187778806163459317 1171921611354263077824311)
        ·
          refine ⟨1757882417031394616736467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1171921611354263077824311 1757882417031394616736467)
          ·
            refine ⟨2636823625547091925104701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1757882417031394616736467 2636823625547091925104701)
            ·
              refine ⟨988808859580159471914263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2636823625547091925104701 988808859580159471914263)
              ·
                refine ⟨1483213289370239207871395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 988808859580159471914263 1483213289370239207871395)
                ·
                  refine ⟨2224819934055358811807093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1483213289370239207871395 2224819934055358811807093)
                  ·
                    refine ⟨208576868817689888606915, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2224819934055358811807093 208576868817689888606915)
                    ·
                      rfl

theorem cell22_609303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 3, 1, 1, 5].length) (baseStart_609303 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_609303 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_609303 prefixEnd_609303 := by exact prefixLift 609303
  have htrace : WordTrace (prefixWord ++ tailWord_609303) baseStart_609303 baseEnd_609303 := by
    simpa [prefixWord, tailWord_609303, baseEnd_609303] using wordTrace_append hprefix tailTrace_609303
  have hstable : (prefixWord ++ tailWord_609303).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_609303).length < 2 ^ (prefixWord ++ tailWord_609303).sum := by decide
  have hdescent : baseEnd_609303 < baseStart_609303 := by decide
  rcases family_descends (prefixWord ++ tailWord_609303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_609322 : List Nat := [3, 1, 4, 1, 3, 2, 1, 3, 4]
def baseStart_609322 : Nat := 118140960795 + 609322 * 2 ^ 59
def prefixEnd_609322 : Nat := 4983230072969 + 3 ^ 40 * 609322 * 2
def baseEnd_609322 : Nat := 69527790968660057460619

theorem tailTrace_609322 : CollatzResearch.WordTrace tailWord_609322 prefixEnd_609322 69527790968660057460619 := by
  unfold tailWord_609322
  simp only [CollatzResearch.WordTrace]
  refine ⟨5555949774634483189439555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14815866065691955171838813 5555949774634483189439555)
  ·
    refine ⟨8333924661951724784159333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5555949774634483189439555 8333924661951724784159333)
    ·
      refine ⟨1562610874115948397029875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8333924661951724784159333 1562610874115948397029875)
      ·
        refine ⟨2343916311173922595544813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1562610874115948397029875 2343916311173922595544813)
        ·
          refine ⟨878968616690220973329305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2343916311173922595544813 878968616690220973329305)
          ·
            refine ⟨659226462517665729996979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 878968616690220973329305 659226462517665729996979)
            ·
              refine ⟨988839693776498594995469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 659226462517665729996979 988839693776498594995469)
              ·
                refine ⟨370814885166186973123301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 988839693776498594995469 370814885166186973123301)
                ·
                  refine ⟨69527790968660057460619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 370814885166186973123301 69527790968660057460619)
                  ·
                    rfl

theorem cell22_609322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 2, 1, 3, 4].length) (baseStart_609322 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_609322 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_609322 prefixEnd_609322 := by exact prefixLift 609322
  have htrace : WordTrace (prefixWord ++ tailWord_609322) baseStart_609322 baseEnd_609322 := by
    simpa [prefixWord, tailWord_609322, baseEnd_609322] using wordTrace_append hprefix tailTrace_609322
  have hstable : (prefixWord ++ tailWord_609322).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_609322).length < 2 ^ (prefixWord ++ tailWord_609322).sum := by decide
  have hdescent : baseEnd_609322 < baseStart_609322 := by decide
  rcases family_descends (prefixWord ++ tailWord_609322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_609350 : List Nat := [6, 1, 1, 1, 1, 3, 2, 7]
def baseStart_609350 : Nat := 118140960795 + 609350 * 2 ^ 59
def prefixEnd_609350 : Nat := 4983230072969 + 3 ^ 40 * 609350 * 2
def baseEnd_609350 : Nat := 23176995319799714742419

theorem tailTrace_609350 : CollatzResearch.WordTrace tailWord_609350 prefixEnd_609350 23176995319799714742419 := by
  unfold tailWord_609350
  simp only [CollatzResearch.WordTrace]
  refine ⟨694525635701140423118047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 14816546894957662359851669 694525635701140423118047)
  ·
    refine ⟨1041788453551710634677071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 694525635701140423118047 1041788453551710634677071)
    ·
      refine ⟨1562682680327565952015607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1041788453551710634677071 1562682680327565952015607)
      ·
        refine ⟨2344024020491348928023411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1562682680327565952015607 2344024020491348928023411)
        ·
          refine ⟨3516036030737023392035117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2344024020491348928023411 3516036030737023392035117)
          ·
            refine ⟨1318513511526383772013169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3516036030737023392035117 1318513511526383772013169)
            ·
              refine ⟨988885133644787829009877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1318513511526383772013169 988885133644787829009877)
              ·
                refine ⟨23176995319799714742419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 988885133644787829009877 23176995319799714742419)
                ·
                  rfl

theorem cell22_609350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 3, 2, 7].length) (baseStart_609350 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_609350 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_609350 prefixEnd_609350 := by exact prefixLift 609350
  have htrace : WordTrace (prefixWord ++ tailWord_609350) baseStart_609350 baseEnd_609350 := by
    simpa [prefixWord, tailWord_609350, baseEnd_609350] using wordTrace_append hprefix tailTrace_609350
  have hstable : (prefixWord ++ tailWord_609350).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_609350).length < 2 ^ (prefixWord ++ tailWord_609350).sum := by decide
  have hdescent : baseEnd_609350 < baseStart_609350 := by decide
  rcases family_descends (prefixWord ++ tailWord_609350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_609440 : List Nat := [2, 1, 1, 4, 2, 1, 4, 3, 4]
def baseStart_609440 : Nat := 118140960795 + 609440 * 2 ^ 59
def prefixEnd_609440 : Nat := 4983230072969 + 3 ^ 40 * 609440 * 2
def baseEnd_609440 : Nat := 69541255572489065977165

theorem tailTrace_609440 : CollatzResearch.WordTrace tailWord_609440 prefixEnd_609440 69541255572489065977165 := by
  unfold tailWord_609440
  simp only [CollatzResearch.WordTrace]
  refine ⟨11114051456055219455276887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14818735274740292607035849 11114051456055219455276887)
  ·
    refine ⟨16671077184082829182915331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11114051456055219455276887 16671077184082829182915331)
    ·
      refine ⟨25006615776124243774372997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16671077184082829182915331 25006615776124243774372997)
      ·
        refine ⟨4688740458023295707694937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 25006615776124243774372997 4688740458023295707694937)
        ·
          refine ⟨3516555343517471780771203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4688740458023295707694937 3516555343517471780771203)
          ·
            refine ⟨5274833015276207671156805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3516555343517471780771203 5274833015276207671156805)
            ·
              refine ⟨989031190364288938341901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5274833015276207671156805 989031190364288938341901)
              ·
                refine ⟨370886696386608351878213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 989031190364288938341901 370886696386608351878213)
                ·
                  refine ⟨69541255572489065977165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 370886696386608351878213 69541255572489065977165)
                  ·
                    rfl

theorem cell22_609440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 4, 3, 4].length) (baseStart_609440 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_609440 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_609440 prefixEnd_609440 := by exact prefixLift 609440
  have htrace : WordTrace (prefixWord ++ tailWord_609440) baseStart_609440 baseEnd_609440 := by
    simpa [prefixWord, tailWord_609440, baseEnd_609440] using wordTrace_append hprefix tailTrace_609440
  have hstable : (prefixWord ++ tailWord_609440).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_609440).length < 2 ^ (prefixWord ++ tailWord_609440).sum := by decide
  have hdescent : baseEnd_609440 < baseStart_609440 := by decide
  rcases family_descends (prefixWord ++ tailWord_609440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_609442 : List Nat := [3, 3, 1, 3, 2, 1, 1, 3, 1, 4]
def baseStart_609442 : Nat := 118140960795 + 609442 * 2 ^ 59
def prefixEnd_609442 : Nat := 4983230072969 + 3 ^ 40 * 609442 * 2
def baseEnd_609442 : Nat := 208624451358339859381489

theorem tailTrace_609442 : CollatzResearch.WordTrace tailWord_609442 prefixEnd_609442 208624451358339859381489 := by
  unfold tailWord_609442
  simp only [CollatzResearch.WordTrace]
  refine ⟨5557043964525798313031645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14818783905402128834751053 5557043964525798313031645)
  ·
    refine ⟨2083891486697174367386867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5557043964525798313031645 2083891486697174367386867)
    ·
      refine ⟨3125837230045761551080301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2083891486697174367386867 3125837230045761551080301)
      ·
        refine ⟨1172188961267160581655113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3125837230045761551080301 1172188961267160581655113)
        ·
          refine ⟨879141720950370436241335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1172188961267160581655113 879141720950370436241335)
          ·
            refine ⟨1318712581425555654362003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 879141720950370436241335 1318712581425555654362003)
            ·
              refine ⟨1978068872138333481543005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1318712581425555654362003 1978068872138333481543005)
              ·
                refine ⟨741775827051875055578627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1978068872138333481543005 741775827051875055578627)
                ·
                  refine ⟨1112663740577812583367941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 741775827051875055578627 1112663740577812583367941)
                  ·
                    refine ⟨208624451358339859381489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1112663740577812583367941 208624451358339859381489)
                    ·
                      rfl

theorem cell22_609442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 1, 1, 3, 1, 4].length) (baseStart_609442 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_609442 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_609442 prefixEnd_609442 := by exact prefixLift 609442
  have htrace : WordTrace (prefixWord ++ tailWord_609442) baseStart_609442 baseEnd_609442 := by
    simpa [prefixWord, tailWord_609442, baseEnd_609442] using wordTrace_append hprefix tailTrace_609442
  have hstable : (prefixWord ++ tailWord_609442).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_609442).length < 2 ^ (prefixWord ++ tailWord_609442).sum := by decide
  have hdescent : baseEnd_609442 < baseStart_609442 := by decide
  rcases family_descends (prefixWord ++ tailWord_609442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_609455 : List Nat := [1, 1, 2, 1, 2, 3, 5, 2, 2, 3]
def baseStart_609455 : Nat := 118140960795 + 609455 * 2 ^ 59
def prefixEnd_609455 : Nat := 4983230072969 + 3 ^ 40 * 609455 * 2
def baseEnd_609455 : Nat := 208628901524012158806449

theorem tailTrace_609455 : CollatzResearch.WordTrace tailWord_609455 prefixEnd_609455 208628901524012158806449 := by
  unfold tailWord_609455
  simp only [CollatzResearch.WordTrace]
  refine ⟨22228650007056096472349819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14819100004704064314899879 22228650007056096472349819)
  ·
    refine ⟨33342975010584144708524729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22228650007056096472349819 33342975010584144708524729)
    ·
      refine ⟨25007231257938108531393547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33342975010584144708524729 25007231257938108531393547)
      ·
        refine ⟨37510846886907162797090321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25007231257938108531393547 37510846886907162797090321)
        ·
          refine ⟨28133135165180372097817741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37510846886907162797090321 28133135165180372097817741)
          ·
            refine ⟨10549925686942639536681653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28133135165180372097817741 10549925686942639536681653)
            ·
              refine ⟨989055533150872456563905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 10549925686942639536681653 989055533150872456563905)
              ·
                refine ⟨741791649863154342422929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 989055533150872456563905 741791649863154342422929)
                ·
                  refine ⟨556343737397365756817197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 741791649863154342422929 556343737397365756817197)
                  ·
                    refine ⟨208628901524012158806449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 556343737397365756817197 208628901524012158806449)
                    ·
                      rfl

theorem cell22_609455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 5, 2, 2, 3].length) (baseStart_609455 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_609455 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_609455 prefixEnd_609455 := by exact prefixLift 609455
  have htrace : WordTrace (prefixWord ++ tailWord_609455) baseStart_609455 baseEnd_609455 := by
    simpa [prefixWord, tailWord_609455, baseEnd_609455] using wordTrace_append hprefix tailTrace_609455
  have hstable : (prefixWord ++ tailWord_609455).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_609455).length < 2 ^ (prefixWord ++ tailWord_609455).sum := by decide
  have hdescent : baseEnd_609455 < baseStart_609455 := by decide
  rcases family_descends (prefixWord ++ tailWord_609455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_609472 : List Nat := [2, 1, 1, 2, 7, 1, 1, 1, 1, 5]
def baseStart_609472 : Nat := 118140960795 + 609472 * 2 ^ 59
def prefixEnd_609472 : Nat := 4983230072969 + 3 ^ 40 * 609472 * 2
def baseEnd_609472 : Nat := 208634720971429781131397

theorem tailTrace_609472 : CollatzResearch.WordTrace tailWord_609472 prefixEnd_609472 208634720971429781131397 := by
  unfold tailWord_609472
  simp only [CollatzResearch.WordTrace]
  refine ⟨11114635023997254187859335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14819513365329672250479113 11114635023997254187859335)
  ·
    refine ⟨16671952535995881281789003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11114635023997254187859335 16671952535995881281789003)
    ·
      refine ⟨25007928803993821922683505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16671952535995881281789003 25007928803993821922683505)
      ·
        refine ⟨18755946602995366442012629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25007928803993821922683505 18755946602995366442012629)
        ·
          refine ⟨439592498507703900984671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 18755946602995366442012629 439592498507703900984671)
          ·
            refine ⟨659388747761555851477007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 439592498507703900984671 659388747761555851477007)
            ·
              refine ⟨989083121642333777215511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 659388747761555851477007 989083121642333777215511)
              ·
                refine ⟨1483624682463500665823267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 989083121642333777215511 1483624682463500665823267)
                ·
                  refine ⟨2225437023695250998734901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1483624682463500665823267 2225437023695250998734901)
                  ·
                    refine ⟨208634720971429781131397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2225437023695250998734901 208634720971429781131397)
                    ·
                      rfl

theorem cell22_609472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 7, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 7, 1, 1, 1, 1, 5].length) (baseStart_609472 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_609472 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_609472 prefixEnd_609472 := by exact prefixLift 609472
  have htrace : WordTrace (prefixWord ++ tailWord_609472) baseStart_609472 baseEnd_609472 := by
    simpa [prefixWord, tailWord_609472, baseEnd_609472] using wordTrace_append hprefix tailTrace_609472
  have hstable : (prefixWord ++ tailWord_609472).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_609472).length < 2 ^ (prefixWord ++ tailWord_609472).sum := by decide
  have hdescent : baseEnd_609472 < baseStart_609472 := by decide
  rcases family_descends (prefixWord ++ tailWord_609472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_609481 : List Nat := [1, 2, 1, 1, 2, 1, 1, 2, 3, 8]
def baseStart_609481 : Nat := 118140960795 + 609481 * 2 ^ 59
def prefixEnd_609481 : Nat := 4983230072969 + 3 ^ 40 * 609481 * 2
def baseEnd_609481 : Nat := 208637801855356757656369

theorem tailTrace_609481 : CollatzResearch.WordTrace tailWord_609481 prefixEnd_609481 208637801855356757656369 := by
  unfold tailWord_609481
  simp only [CollatzResearch.WordTrace]
  refine ⟨22229598304961902912796297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14819732203307935275197531 22229598304961902912796297)
  ·
    refine ⟨16672198728721427184597223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22229598304961902912796297 16672198728721427184597223)
    ·
      refine ⟨25008298093082140776895835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16672198728721427184597223 25008298093082140776895835)
      ·
        refine ⟨37512447139623211165343753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25008298093082140776895835 37512447139623211165343753)
        ·
          refine ⟨28134335354717408374007815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37512447139623211165343753 28134335354717408374007815)
          ·
            refine ⟨42201503032076112561011723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28134335354717408374007815 42201503032076112561011723)
            ·
              refine ⟨63302254548114168841517585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42201503032076112561011723 63302254548114168841517585)
              ·
                refine ⟨47476690911085626631138189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 63302254548114168841517585 47476690911085626631138189)
                ·
                  refine ⟨17803759091657109986676821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 47476690911085626631138189 17803759091657109986676821)
                  ·
                    refine ⟨208637801855356757656369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 17803759091657109986676821 208637801855356757656369)
                    ·
                      rfl

theorem cell22_609481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 2, 3, 8].length) (baseStart_609481 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_609481 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_609481 prefixEnd_609481 := by exact prefixLift 609481
  have htrace : WordTrace (prefixWord ++ tailWord_609481) baseStart_609481 baseEnd_609481 := by
    simpa [prefixWord, tailWord_609481, baseEnd_609481] using wordTrace_append hprefix tailTrace_609481
  have hstable : (prefixWord ++ tailWord_609481).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_609481).length < 2 ^ (prefixWord ++ tailWord_609481).sum := by decide
  have hdescent : baseEnd_609481 < baseStart_609481 := by decide
  rcases family_descends (prefixWord ++ tailWord_609481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_609483 : List Nat := [1, 1, 1, 1, 3, 2, 2, 3, 5, 3]
def baseStart_609483 : Nat := 118140960795 + 609483 * 2 ^ 59
def prefixEnd_609483 : Nat := 4983230072969 + 3 ^ 40 * 609483 * 2
def baseEnd_609483 : Nat := 208638486496229419106363

theorem tailTrace_609483 : CollatzResearch.WordTrace tailWord_609483 prefixEnd_609483 208638486496229419106363 := by
  unfold tailWord_609483
  simp only [CollatzResearch.WordTrace]
  refine ⟨22229671250954657254369103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14819780833969771502912735 22229671250954657254369103)
  ·
    refine ⟨33344506876431985881553655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22229671250954657254369103 33344506876431985881553655)
    ·
      refine ⟨50016760314647978822330483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33344506876431985881553655 50016760314647978822330483)
      ·
        refine ⟨75025140471971968233495725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50016760314647978822330483 75025140471971968233495725)
        ·
          refine ⟨28134427676989488087560897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 75025140471971968233495725 28134427676989488087560897)
          ·
            refine ⟨21100820757742116065670673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28134427676989488087560897 21100820757742116065670673)
            ·
              refine ⟨15825615568306587049253005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21100820757742116065670673 15825615568306587049253005)
              ·
                refine ⟨5934605838114970143469877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15825615568306587049253005 5934605838114970143469877)
                ·
                  refine ⟨556369297323278450950301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5934605838114970143469877 556369297323278450950301)
                  ·
                    refine ⟨208638486496229419106363, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 556369297323278450950301 208638486496229419106363)
                    ·
                      rfl

theorem cell22_609483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 3, 5, 3].length) (baseStart_609483 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_609483 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_609483 prefixEnd_609483 := by exact prefixLift 609483
  have htrace : WordTrace (prefixWord ++ tailWord_609483) baseStart_609483 baseEnd_609483 := by
    simpa [prefixWord, tailWord_609483, baseEnd_609483] using wordTrace_append hprefix tailTrace_609483
  have hstable : (prefixWord ++ tailWord_609483).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_609483).length < 2 ^ (prefixWord ++ tailWord_609483).sum := by decide
  have hdescent : baseEnd_609483 < baseStart_609483 := by decide
  rcases family_descends (prefixWord ++ tailWord_609483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_609517 : List Nat := [1, 5, 1, 2, 2, 1, 3, 1, 3, 3]
def baseStart_609517 : Nat := 118140960795 + 609517 * 2 ^ 59
def prefixEnd_609517 : Nat := 4983230072969 + 3 ^ 40 * 609517 * 2
def baseEnd_609517 : Nat := 208650125391064663756259

theorem tailTrace_609517 : CollatzResearch.WordTrace tailWord_609517 prefixEnd_609517 208650125391064663756259 := by
  unfold tailWord_609517
  simp only [CollatzResearch.WordTrace]
  refine ⟨22230911332831481061106805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14820607555220987374071203 22230911332831481061106805)
  ·
    refine ⟨2084147937452951349478763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 22230911332831481061106805 2084147937452951349478763)
    ·
      refine ⟨3126221906179427024218145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2084147937452951349478763 3126221906179427024218145)
      ·
        refine ⟨2344666429634570268163609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3126221906179427024218145 2344666429634570268163609)
        ·
          refine ⟨1758499822225927701122707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2344666429634570268163609 1758499822225927701122707)
          ·
            refine ⟨2637749733338891551684061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1758499822225927701122707 2637749733338891551684061)
            ·
              refine ⟨989156150002084331881523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2637749733338891551684061 989156150002084331881523)
              ·
                refine ⟨1483734225003126497822285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 989156150002084331881523 1483734225003126497822285)
                ·
                  refine ⟨556400334376172436683357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1483734225003126497822285 556400334376172436683357)
                  ·
                    refine ⟨208650125391064663756259, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 556400334376172436683357 208650125391064663756259)
                    ·
                      rfl

theorem cell22_609517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 3, 1, 3, 3].length) (baseStart_609517 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_609517 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_609517 prefixEnd_609517 := by exact prefixLift 609517
  have htrace : WordTrace (prefixWord ++ tailWord_609517) baseStart_609517 baseEnd_609517 := by
    simpa [prefixWord, tailWord_609517, baseEnd_609517] using wordTrace_append hprefix tailTrace_609517
  have hstable : (prefixWord ++ tailWord_609517).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_609517).length < 2 ^ (prefixWord ++ tailWord_609517).sum := by decide
  have hdescent : baseEnd_609517 < baseStart_609517 := by decide
  rcases family_descends (prefixWord ++ tailWord_609517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_609568 : List Nat := [2, 1, 1, 5, 4, 1, 2, 2, 1, 3]
def baseStart_609568 : Nat := 118140960795 + 609568 * 2 ^ 59
def prefixEnd_609568 : Nat := 4983230072969 + 3 ^ 40 * 609568 * 2
def baseEnd_609568 : Nat := 208667583733317530731103

theorem tailTrace_609568 : CollatzResearch.WordTrace tailWord_609568 prefixEnd_609568 208667583733317530731103 := by
  unfold tailWord_609568
  simp only [CollatzResearch.WordTrace]
  refine ⟨11116385727823358385606679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14821847637097811180808905 11116385727823358385606679)
  ·
    refine ⟨16674578591735037578410019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11116385727823358385606679 16674578591735037578410019)
    ·
      refine ⟨25011867887602556367615029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16674578591735037578410019 25011867887602556367615029)
      ·
        refine ⟨2344862614462739659463909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 25011867887602556367615029 2344862614462739659463909)
        ·
          refine ⟨439661740211763686149483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2344862614462739659463909 439661740211763686149483)
          ·
            refine ⟨659492610317645529224225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 439661740211763686149483 659492610317645529224225)
            ·
              refine ⟨494619457738234146918169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 659492610317645529224225 494619457738234146918169)
              ·
                refine ⟨370964593303675610188627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 494619457738234146918169 370964593303675610188627)
                ·
                  refine ⟨556446889955513415282941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 370964593303675610188627 556446889955513415282941)
                  ·
                    refine ⟨208667583733317530731103, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 556446889955513415282941 208667583733317530731103)
                    ·
                      rfl

theorem cell22_609568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 4, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 4, 1, 2, 2, 1, 3].length) (baseStart_609568 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_609568 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_609568 prefixEnd_609568 := by exact prefixLift 609568
  have htrace : WordTrace (prefixWord ++ tailWord_609568) baseStart_609568 baseEnd_609568 := by
    simpa [prefixWord, tailWord_609568, baseEnd_609568] using wordTrace_append hprefix tailTrace_609568
  have hstable : (prefixWord ++ tailWord_609568).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_609568).length < 2 ^ (prefixWord ++ tailWord_609568).sum := by decide
  have hdescent : baseEnd_609568 < baseStart_609568 := by decide
  rcases family_descends (prefixWord ++ tailWord_609568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_609633 : List Nat := [1, 2, 3, 1, 1, 1, 1, 3, 1, 8]
def baseStart_609633 : Nat := 118140960795 + 609633 * 2 ^ 59
def prefixEnd_609633 : Nat := 4983230072969 + 3 ^ 40 * 609633 * 2
def baseEnd_609633 : Nat := 208689834561679027855903

theorem tailTrace_609633 : CollatzResearch.WordTrace tailWord_609633 prefixEnd_609633 208689834561679027855903 := by
  unfold tailWord_609633
  simp only [CollatzResearch.WordTrace]
  refine ⟨22235142200411232872329553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14823428133607488581553035 22235142200411232872329553)
  ·
    refine ⟨16676356650308424654247165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22235142200411232872329553 16676356650308424654247165)
    ·
      refine ⟨6253633743865659245342687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16676356650308424654247165 6253633743865659245342687)
      ·
        refine ⟨9380450615798488868014031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6253633743865659245342687 9380450615798488868014031)
        ·
          refine ⟨14070675923697733302021047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9380450615798488868014031 14070675923697733302021047)
          ·
            refine ⟨21106013885546599953031571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14070675923697733302021047 21106013885546599953031571)
            ·
              refine ⟨31659020828319899929547357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21106013885546599953031571 31659020828319899929547357)
              ·
                refine ⟨11872132810619962473580259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31659020828319899929547357 11872132810619962473580259)
                ·
                  refine ⟨17808199215929943710370389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11872132810619962473580259 17808199215929943710370389)
                  ·
                    refine ⟨208689834561679027855903, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 17808199215929943710370389 208689834561679027855903)
                    ·
                      rfl

theorem cell22_609633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 3, 1, 8].length) (baseStart_609633 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_609633 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_609633 prefixEnd_609633 := by exact prefixLift 609633
  have htrace : WordTrace (prefixWord ++ tailWord_609633) baseStart_609633 baseEnd_609633 := by
    simpa [prefixWord, tailWord_609633, baseEnd_609633] using wordTrace_append hprefix tailTrace_609633
  have hstable : (prefixWord ++ tailWord_609633).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_609633).length < 2 ^ (prefixWord ++ tailWord_609633).sum := by decide
  have hdescent : baseEnd_609633 < baseStart_609633 := by decide
  rcases family_descends (prefixWord ++ tailWord_609633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_609669 : List Nat := [1, 3, 1, 1, 3, 1, 5, 3, 1, 3]
def baseStart_609669 : Nat := 118140960795 + 609669 * 2 ^ 59
def prefixEnd_609669 : Nat := 4983230072969 + 3 ^ 40 * 609669 * 2
def baseEnd_609669 : Nat := 208702158097386933955793

theorem tailTrace_609669 : CollatzResearch.WordTrace tailWord_609669 prefixEnd_609669 208702158097386933955793 := by
  unfold tailWord_609669
  simp only [CollatzResearch.WordTrace]
  refine ⟨22236455228280811020640061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14824303485520540680426707 22236455228280811020640061)
  ·
    refine ⟨8338670710605304132740023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22236455228280811020640061 8338670710605304132740023)
    ·
      refine ⟨12508006065907956199110035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8338670710605304132740023 12508006065907956199110035)
      ·
        refine ⟨18762009098861934298665053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12508006065907956199110035 18762009098861934298665053)
        ·
          refine ⟨7035753412073225361999395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18762009098861934298665053 7035753412073225361999395)
          ·
            refine ⟨10553630118109838042999093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7035753412073225361999395 10553630118109838042999093)
            ·
              refine ⟨989402823572797316531165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 10553630118109838042999093 989402823572797316531165)
              ·
                refine ⟨371026058839798993699187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 989402823572797316531165 371026058839798993699187)
                ·
                  refine ⟨556539088259698490548781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 371026058839798993699187 556539088259698490548781)
                  ·
                    refine ⟨208702158097386933955793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 556539088259698490548781 208702158097386933955793)
                    ·
                      rfl

theorem cell22_609669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 5, 3, 1, 3].length) (baseStart_609669 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_609669 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_609669 prefixEnd_609669 := by exact prefixLift 609669
  have htrace : WordTrace (prefixWord ++ tailWord_609669) baseStart_609669 baseEnd_609669 := by
    simpa [prefixWord, tailWord_609669, baseEnd_609669] using wordTrace_append hprefix tailTrace_609669
  have hstable : (prefixWord ++ tailWord_609669).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_609669).length < 2 ^ (prefixWord ++ tailWord_609669).sum := by decide
  have hdescent : baseEnd_609669 < baseStart_609669 := by decide
  rcases family_descends (prefixWord ++ tailWord_609669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_609742 : List Nat := [4, 1, 1, 1, 2, 1, 2, 3, 4, 3]
def baseStart_609742 : Nat := 118140960795 + 609742 * 2 ^ 59
def prefixEnd_609742 : Nat := 4983230072969 + 3 ^ 40 * 609742 * 2
def baseEnd_609742 : Nat := 208727147489239076880569

theorem tailTrace_609742 : CollatzResearch.WordTrace tailWord_609742 prefixEnd_609742 208727147489239076880569 := by
  unfold tailWord_609742
  simp only [CollatzResearch.WordTrace]
  refine ⟨2779889719627043061005935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14826078504677562992031653 2779889719627043061005935)
  ·
    refine ⟨4169834579440564591508903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2779889719627043061005935 4169834579440564591508903)
    ·
      refine ⟨6254751869160846887263355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4169834579440564591508903 6254751869160846887263355)
      ·
        refine ⟨9382127803741270330895033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6254751869160846887263355 9382127803741270330895033)
        ·
          refine ⟨7036595852805952748171275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9382127803741270330895033 7036595852805952748171275)
          ·
            refine ⟨10554893779208929122256913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7036595852805952748171275 10554893779208929122256913)
            ·
              refine ⟨7916170334406696841692685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10554893779208929122256913 7916170334406696841692685)
              ·
                refine ⟨2968563875402511315634757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7916170334406696841692685 2968563875402511315634757)
                ·
                  refine ⟨556605726637970871681517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2968563875402511315634757 556605726637970871681517)
                  ·
                    refine ⟨208727147489239076880569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 556605726637970871681517 208727147489239076880569)
                    ·
                      rfl

theorem cell22_609742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 2, 3, 4, 3].length) (baseStart_609742 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_609742 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_609742 prefixEnd_609742 := by exact prefixLift 609742
  have htrace : WordTrace (prefixWord ++ tailWord_609742) baseStart_609742 baseEnd_609742 := by
    simpa [prefixWord, tailWord_609742, baseEnd_609742] using wordTrace_append hprefix tailTrace_609742
  have hstable : (prefixWord ++ tailWord_609742).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_609742).length < 2 ^ (prefixWord ++ tailWord_609742).sum := by decide
  have hdescent : baseEnd_609742 < baseStart_609742 := by decide
  rcases family_descends (prefixWord ++ tailWord_609742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_609793 : List Nat := [1, 2, 4, 1, 5, 1, 1, 2, 2, 3]
def baseStart_609793 : Nat := 118140960795 + 609793 * 2 ^ 59
def prefixEnd_609793 : Nat := 4983230072969 + 3 ^ 40 * 609793 * 2
def baseEnd_609793 : Nat := 208744605831491943855413

theorem tailTrace_609793 : CollatzResearch.WordTrace tailWord_609793 prefixEnd_609793 208744605831491943855413 := by
  unfold tailWord_609793
  simp only [CollatzResearch.WordTrace]
  refine ⟨22240977879831580198154033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14827318586554386798769355 22240977879831580198154033)
  ·
    refine ⟨16680733409873685148615525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22240977879831580198154033 16680733409873685148615525)
    ·
      refine ⟨3127637514351315965365411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 16680733409873685148615525 3127637514351315965365411)
      ·
        refine ⟨4691456271526973948048117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3127637514351315965365411 4691456271526973948048117)
        ·
          refine ⟨439824025455653807629511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 4691456271526973948048117 439824025455653807629511)
          ·
            refine ⟨659736038183480711444267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 439824025455653807629511 659736038183480711444267)
            ·
              refine ⟨989604057275221067166401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 659736038183480711444267 989604057275221067166401)
              ·
                refine ⟨742203042956415800374801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 989604057275221067166401 742203042956415800374801)
                ·
                  refine ⟨556652282217311850281101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 742203042956415800374801 556652282217311850281101)
                  ·
                    refine ⟨208744605831491943855413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 556652282217311850281101 208744605831491943855413)
                    ·
                      rfl

theorem cell22_609793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 5, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 5, 1, 1, 2, 2, 3].length) (baseStart_609793 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_609793 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_609793 prefixEnd_609793 := by exact prefixLift 609793
  have htrace : WordTrace (prefixWord ++ tailWord_609793) baseStart_609793 baseEnd_609793 := by
    simpa [prefixWord, tailWord_609793, baseEnd_609793] using wordTrace_append hprefix tailTrace_609793
  have hstable : (prefixWord ++ tailWord_609793).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_609793).length < 2 ^ (prefixWord ++ tailWord_609793).sum := by decide
  have hdescent : baseEnd_609793 < baseStart_609793 := by decide
  rcases family_descends (prefixWord ++ tailWord_609793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_609838 : List Nat := [4, 1, 3, 1, 2, 1, 3, 3, 1, 3]
def baseStart_609838 : Nat := 118140960795 + 609838 * 2 ^ 59
def prefixEnd_609838 : Nat := 4983230072969 + 3 ^ 40 * 609838 * 2
def baseEnd_609838 : Nat := 208760010251126826480275

theorem tailTrace_609838 : CollatzResearch.WordTrace tailWord_609838 prefixEnd_609838 208760010251126826480275 := by
  unfold tailWord_609838
  simp only [CollatzResearch.WordTrace]
  refine ⟨2780327395583569110442771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14828412776445701922361445 2780327395583569110442771)
  ·
    refine ⟨4170491093375353665664157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2780327395583569110442771 4170491093375353665664157)
    ·
      refine ⟨1563934160015757624624059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4170491093375353665664157 1563934160015757624624059)
      ·
        refine ⟨2345901240023636436936089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1563934160015757624624059 2345901240023636436936089)
        ·
          refine ⟨1759425930017727327702067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2345901240023636436936089 1759425930017727327702067)
          ·
            refine ⟨2639138895026590991553101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1759425930017727327702067 2639138895026590991553101)
            ·
              refine ⟨989677085634971621832413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2639138895026590991553101 989677085634971621832413)
              ·
                refine ⟨371128907113114358187155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 989677085634971621832413 371128907113114358187155)
                ·
                  refine ⟨556693360669671537280733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 371128907113114358187155 556693360669671537280733)
                  ·
                    refine ⟨208760010251126826480275, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 556693360669671537280733 208760010251126826480275)
                    ·
                      rfl

theorem cell22_609838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 3, 3, 1, 3].length) (baseStart_609838 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_609838 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_609838 prefixEnd_609838 := by exact prefixLift 609838
  have htrace : WordTrace (prefixWord ++ tailWord_609838) baseStart_609838 baseEnd_609838 := by
    simpa [prefixWord, tailWord_609838, baseEnd_609838] using wordTrace_append hprefix tailTrace_609838
  have hstable : (prefixWord ++ tailWord_609838).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_609838).length < 2 ^ (prefixWord ++ tailWord_609838).sum := by decide
  have hdescent : baseEnd_609838 < baseStart_609838 := by decide
  rcases family_descends (prefixWord ++ tailWord_609838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_609877 : List Nat := [1, 3, 2, 2, 1, 1, 1, 5, 1, 5]
def baseStart_609877 : Nat := 118140960795 + 609877 * 2 ^ 59
def prefixEnd_609877 : Nat := 4983230072969 + 3 ^ 40 * 609877 * 2
def baseEnd_609877 : Nat := 208773360748143724755155

theorem tailTrace_609877 : CollatzResearch.WordTrace tailWord_609877 prefixEnd_609877 208773360748143724755155 := by
  unfold tailWord_609877
  simp only [CollatzResearch.WordTrace]
  refine ⟨22244041611527262544211885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14829361074351508362807923 22244041611527262544211885)
  ·
    refine ⟨8341515604322723454079457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22244041611527262544211885 8341515604322723454079457)
    ·
      refine ⟨6256136703242042590559593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8341515604322723454079457 6256136703242042590559593)
      ·
        refine ⟨4692102527431531942919695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6256136703242042590559593 4692102527431531942919695)
        ·
          refine ⟨7038153791147297914379543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4692102527431531942919695 7038153791147297914379543)
          ·
            refine ⟨10557230686720946871569315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7038153791147297914379543 10557230686720946871569315)
            ·
              refine ⟨15835846030081420307353973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10557230686720946871569315 15835846030081420307353973)
              ·
                refine ⟨1484610565320133153814435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 15835846030081420307353973 1484610565320133153814435)
                ·
                  refine ⟨2226915847980199730721653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1484610565320133153814435 2226915847980199730721653)
                  ·
                    refine ⟨208773360748143724755155, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2226915847980199730721653 208773360748143724755155)
                    ·
                      rfl

theorem cell22_609877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 5, 1, 5].length) (baseStart_609877 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_609877 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_609877 prefixEnd_609877 := by exact prefixLift 609877
  have htrace : WordTrace (prefixWord ++ tailWord_609877) baseStart_609877 baseEnd_609877 := by
    simpa [prefixWord, tailWord_609877, baseEnd_609877] using wordTrace_append hprefix tailTrace_609877
  have hstable : (prefixWord ++ tailWord_609877).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_609877).length < 2 ^ (prefixWord ++ tailWord_609877).sum := by decide
  have hdescent : baseEnd_609877 < baseStart_609877 := by decide
  rcases family_descends (prefixWord ++ tailWord_609877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_609967 : List Nat := [1, 1, 2, 1, 2, 4, 1, 1, 4, 5]
def baseStart_609967 : Nat := 118140960795 + 609967 * 2 ^ 59
def prefixEnd_609967 : Nat := 4983230072969 + 3 ^ 40 * 609967 * 2
def baseEnd_609967 : Nat := 208804169587413490004879

theorem tailTrace_609967 : CollatzResearch.WordTrace tailWord_609967 prefixEnd_609967 208804169587413490004879 := by
  unfold tailWord_609967
  simp only [CollatzResearch.WordTrace]
  refine ⟨22247324181201207914988155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14831549454134138609992103 22247324181201207914988155)
  ·
    refine ⟨33370986271801811872482233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22247324181201207914988155 33370986271801811872482233)
    ·
      refine ⟨25028239703851358904361675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33370986271801811872482233 25028239703851358904361675)
      ·
        refine ⟨37542359555777038356542513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25028239703851358904361675 37542359555777038356542513)
        ·
          refine ⟨28156769666832778767406885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37542359555777038356542513 28156769666832778767406885)
          ·
            refine ⟨5279394312531146018888791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 28156769666832778767406885 5279394312531146018888791)
            ·
              refine ⟨7919091468796719028333187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5279394312531146018888791 7919091468796719028333187)
              ·
                refine ⟨11878637203195078542499781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7919091468796719028333187 11878637203195078542499781)
                ·
                  refine ⟨2227244475599077226718709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11878637203195078542499781 2227244475599077226718709)
                  ·
                    refine ⟨208804169587413490004879, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2227244475599077226718709 208804169587413490004879)
                    ·
                      rfl

theorem cell22_609967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 1, 1, 4, 5].length) (baseStart_609967 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_609967 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_609967 prefixEnd_609967 := by exact prefixLift 609967
  have htrace : WordTrace (prefixWord ++ tailWord_609967) baseStart_609967 baseEnd_609967 := by
    simpa [prefixWord, tailWord_609967, baseEnd_609967] using wordTrace_append hprefix tailTrace_609967
  have hstable : (prefixWord ++ tailWord_609967).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_609967).length < 2 ^ (prefixWord ++ tailWord_609967).sum := by decide
  have hdescent : baseEnd_609967 < baseStart_609967 := by decide
  rcases family_descends (prefixWord ++ tailWord_609967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_609973 : List Nat := [1, 3, 3, 3, 2, 1, 2, 1, 3, 3]
def baseStart_609973 : Nat := 118140960795 + 609973 * 2 ^ 59
def prefixEnd_609973 : Nat := 4983230072969 + 3 ^ 40 * 609973 * 2
def baseEnd_609973 : Nat := 208806223510031474354861

theorem tailTrace_609973 : CollatzResearch.WordTrace tailWord_609973 prefixEnd_609973 208806223510031474354861 := by
  unfold tailWord_609973
  simp only [CollatzResearch.WordTrace]
  refine ⟨22247543019179470939706573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14831695346119647293137715 22247543019179470939706573)
  ·
    refine ⟨8342828632192301602389965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22247543019179470939706573 8342828632192301602389965)
    ·
      refine ⟨3128560737072113100896237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8342828632192301602389965 3128560737072113100896237)
      ·
        refine ⟨1173210276402042412836089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3128560737072113100896237 1173210276402042412836089)
        ·
          refine ⟨879907707301531809627067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1173210276402042412836089 879907707301531809627067)
          ·
            refine ⟨1319861560952297714440601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 879907707301531809627067 1319861560952297714440601)
            ·
              refine ⟨989896170714223285830451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1319861560952297714440601 989896170714223285830451)
              ·
                refine ⟨1484844256071334928745677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 989896170714223285830451 1484844256071334928745677)
                ·
                  refine ⟨556816596026750598279629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1484844256071334928745677 556816596026750598279629)
                  ·
                    refine ⟨208806223510031474354861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 556816596026750598279629 208806223510031474354861)
                    ·
                      rfl

theorem cell22_609973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 1, 2, 1, 3, 3].length) (baseStart_609973 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_609973 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_609973 prefixEnd_609973 := by exact prefixLift 609973
  have htrace : WordTrace (prefixWord ++ tailWord_609973) baseStart_609973 baseEnd_609973 := by
    simpa [prefixWord, tailWord_609973, baseEnd_609973] using wordTrace_append hprefix tailTrace_609973
  have hstable : (prefixWord ++ tailWord_609973).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_609973).length < 2 ^ (prefixWord ++ tailWord_609973).sum := by decide
  have hdescent : baseEnd_609973 < baseStart_609973 := by decide
  rcases family_descends (prefixWord ++ tailWord_609973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_609990 : List Nat := [6, 1, 2, 1, 1, 1, 2, 2, 3, 3]
def baseStart_609990 : Nat := 118140960795 + 609990 * 2 ^ 59
def prefixEnd_609990 : Nat := 4983230072969 + 3 ^ 40 * 609990 * 2
def baseEnd_609990 : Nat := 208812042957449096679809

theorem tailTrace_609990 : CollatzResearch.WordTrace tailWord_609990 prefixEnd_609990 208812042957449096679809 := by
  unfold tailWord_609990
  simp only [CollatzResearch.WordTrace]
  refine ⟨695255095628683838846107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 14832108706745255228716949 695255095628683838846107)
  ·
    refine ⟨1042882643443025758269161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 695255095628683838846107 1042882643443025758269161)
    ·
      refine ⟨782161982582269318701871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1042882643443025758269161 782161982582269318701871)
      ·
        refine ⟨1173242973873403978052807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 782161982582269318701871 1173242973873403978052807)
        ·
          refine ⟨1759864460810105967079211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1173242973873403978052807 1759864460810105967079211)
          ·
            refine ⟨2639796691215158950618817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1759864460810105967079211 2639796691215158950618817)
            ·
              refine ⟨1979847518411369212964113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2639796691215158950618817 1979847518411369212964113)
              ·
                refine ⟨1484885638808526909723085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1979847518411369212964113 1484885638808526909723085)
                ·
                  refine ⟨556832114553197591146157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1484885638808526909723085 556832114553197591146157)
                  ·
                    refine ⟨208812042957449096679809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 556832114553197591146157 208812042957449096679809)
                    ·
                      rfl

theorem cell22_609990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 2, 2, 3, 3].length) (baseStart_609990 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_609990 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_609990 prefixEnd_609990 := by exact prefixLift 609990
  have htrace : WordTrace (prefixWord ++ tailWord_609990) baseStart_609990 baseEnd_609990 := by
    simpa [prefixWord, tailWord_609990, baseEnd_609990] using wordTrace_append hprefix tailTrace_609990
  have hstable : (prefixWord ++ tailWord_609990).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_609990).length < 2 ^ (prefixWord ++ tailWord_609990).sum := by decide
  have hdescent : baseEnd_609990 < baseStart_609990 := by decide
  rcases family_descends (prefixWord ++ tailWord_609990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_610044 : List Nat := [2, 2, 2, 1, 3, 1, 1, 2, 4, 4]
def baseStart_610044 : Nat := 118140960795 + 610044 * 2 ^ 59
def prefixEnd_610044 : Nat := 4983230072969 + 3 ^ 40 * 610044 * 2
def baseEnd_610044 : Nat := 208830528261010955829643

theorem tailTrace_610044 : CollatzResearch.WordTrace tailWord_610044 prefixEnd_610044 208830528261010955829643 := by
  unfold tailWord_610044
  simp only [CollatzResearch.WordTrace]
  refine ⟨11125066300961125032770593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14833421734614833377027457 11125066300961125032770593)
  ·
    refine ⟨8343799725720843774577945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11125066300961125032770593 8343799725720843774577945)
    ·
      refine ⟨6257849794290632830933459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8343799725720843774577945 6257849794290632830933459)
      ·
        refine ⟨9386774691435949246400189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6257849794290632830933459 9386774691435949246400189)
        ·
          refine ⟨3520040509288480967400071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9386774691435949246400189 3520040509288480967400071)
          ·
            refine ⟨5280060763932721451100107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3520040509288480967400071 5280060763932721451100107)
            ·
              refine ⟨7920091145899082176650161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5280060763932721451100107 7920091145899082176650161)
              ·
                refine ⟨5940068359424311632487621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7920091145899082176650161 5940068359424311632487621)
                ·
                  refine ⟨1113762817392058431091429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5940068359424311632487621 1113762817392058431091429)
                  ·
                    refine ⟨208830528261010955829643, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1113762817392058431091429 208830528261010955829643)
                    ·
                      rfl

theorem cell22_610044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 1, 2, 4, 4].length) (baseStart_610044 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_610044 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_610044 prefixEnd_610044 := by exact prefixLift 610044
  have htrace : WordTrace (prefixWord ++ tailWord_610044) baseStart_610044 baseEnd_610044 := by
    simpa [prefixWord, tailWord_610044, baseEnd_610044] using wordTrace_append hprefix tailTrace_610044
  have hstable : (prefixWord ++ tailWord_610044).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_610044).length < 2 ^ (prefixWord ++ tailWord_610044).sum := by decide
  have hdescent : baseEnd_610044 < baseStart_610044 := by decide
  rcases family_descends (prefixWord ++ tailWord_610044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_610181 : List Nat := [1, 3, 1, 1, 3, 2, 1, 1, 6, 3]
def baseStart_610181 : Nat := 118140960795 + 610181 * 2 ^ 59
def prefixEnd_610181 : Nat := 4983230072969 + 3 ^ 40 * 610181 * 2
def baseEnd_610181 : Nat := 208877426160788265154223

theorem tailTrace_610181 : CollatzResearch.WordTrace tailWord_610181 prefixEnd_610181 208877426160788265154223 := by
  unfold tailWord_610181
  simp only [CollatzResearch.WordTrace]
  refine ⟨22255129402425922463278397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14836752934950614975518931 22255129402425922463278397)
  ·
    refine ⟨8345673525909720923729399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22255129402425922463278397 8345673525909720923729399)
    ·
      refine ⟨12518510288864581385594099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8345673525909720923729399 12518510288864581385594099)
      ·
        refine ⟨18777765433296872078391149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12518510288864581385594099 18777765433296872078391149)
        ·
          refine ⟨7041662037486327029396681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18777765433296872078391149 7041662037486327029396681)
          ·
            refine ⟨5281246528114745272047511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7041662037486327029396681 5281246528114745272047511)
            ·
              refine ⟨7921869792172117908071267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5281246528114745272047511 7921869792172117908071267)
              ·
                refine ⟨11882804688258176862106901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7921869792172117908071267 11882804688258176862106901)
                ·
                  refine ⟨557006469762102040411261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 11882804688258176862106901 557006469762102040411261)
                  ·
                    refine ⟨208877426160788265154223, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 557006469762102040411261 208877426160788265154223)
                    ·
                      rfl

theorem cell22_610181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 1, 1, 6, 3].length) (baseStart_610181 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_610181 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_610181 prefixEnd_610181 := by exact prefixLift 610181
  have htrace : WordTrace (prefixWord ++ tailWord_610181) baseStart_610181 baseEnd_610181 := by
    simpa [prefixWord, tailWord_610181, baseEnd_610181] using wordTrace_append hprefix tailTrace_610181
  have hstable : (prefixWord ++ tailWord_610181).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_610181).length < 2 ^ (prefixWord ++ tailWord_610181).sum := by decide
  have hdescent : baseEnd_610181 < baseStart_610181 := by decide
  rcases family_descends (prefixWord ++ tailWord_610181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_610200 : List Nat := [2, 1, 2, 6, 1, 2, 1, 1, 6]
def baseStart_610200 : Nat := 118140960795 + 610200 * 2 ^ 59
def prefixEnd_610200 : Nat := 4983230072969 + 3 ^ 40 * 610200 * 2
def baseEnd_610200 : Nat := 69627976749692849643055

theorem tailTrace_610200 : CollatzResearch.WordTrace tailWord_610200 prefixEnd_610200 69627976749692849643055 := by
  unfold tailWord_610200
  simp only [CollatzResearch.WordTrace]
  refine ⟨11127911194678544354110027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14837214926238059138813369 11127911194678544354110027)
  ·
    refine ⟨16691866792017816531165041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11127911194678544354110027 16691866792017816531165041)
    ·
      refine ⟨12518900094013362398373781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16691866792017816531165041 12518900094013362398373781)
      ·
        refine ⟨586823441906876362423771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 12518900094013362398373781 586823441906876362423771)
        ·
          refine ⟨880235162860314543635657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 586823441906876362423771 880235162860314543635657)
          ·
            refine ⟨660176372145235907726743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 880235162860314543635657 660176372145235907726743)
            ·
              refine ⟨990264558217853861590115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 660176372145235907726743 990264558217853861590115)
              ·
                refine ⟨1485396837326780792385173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 990264558217853861590115 1485396837326780792385173)
                ·
                  refine ⟨69627976749692849643055, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1485396837326780792385173 69627976749692849643055)
                  ·
                    rfl

theorem cell22_610200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 2, 1, 1, 6].length) (baseStart_610200 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_610200 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_610200 prefixEnd_610200 := by exact prefixLift 610200
  have htrace : WordTrace (prefixWord ++ tailWord_610200) baseStart_610200 baseEnd_610200 := by
    simpa [prefixWord, tailWord_610200, baseEnd_610200] using wordTrace_append hprefix tailTrace_610200
  have hstable : (prefixWord ++ tailWord_610200).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_610200).length < 2 ^ (prefixWord ++ tailWord_610200).sum := by decide
  have hdescent : baseEnd_610200 < baseStart_610200 := by decide
  rcases family_descends (prefixWord ++ tailWord_610200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_610215 : List Nat := [1, 1, 6, 1, 2, 2, 1, 3, 2, 3]
def baseStart_610215 : Nat := 118140960795 + 610215 * 2 ^ 59
def prefixEnd_610215 : Nat := 4983230072969 + 3 ^ 40 * 610215 * 2
def baseEnd_610215 : Nat := 208889065055623509804119

theorem tailTrace_610215 : CollatzResearch.WordTrace tailWord_610215 prefixEnd_610215 208889065055623509804119 := by
  unfold tailWord_610215
  simp only [CollatzResearch.WordTrace]
  refine ⟨22256369484302746270016099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14837579656201830846677399 22256369484302746270016099)
  ·
    refine ⟨33384554226454119405024149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22256369484302746270016099 33384554226454119405024149)
    ·
      refine ⟨1564900979365036847110507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 33384554226454119405024149 1564900979365036847110507)
      ·
        refine ⟨2347351469047555270665761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1564900979365036847110507 2347351469047555270665761)
        ·
          refine ⟨1760513601785666452999321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2347351469047555270665761 1760513601785666452999321)
          ·
            refine ⟨1320385201339249839749491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1760513601785666452999321 1320385201339249839749491)
            ·
              refine ⟨1980577802008874759624237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1320385201339249839749491 1980577802008874759624237)
              ·
                refine ⟨742716675753328034859089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1980577802008874759624237 742716675753328034859089)
                ·
                  refine ⟨557037506814996026144317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 742716675753328034859089 557037506814996026144317)
                  ·
                    refine ⟨208889065055623509804119, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 557037506814996026144317 208889065055623509804119)
                    ·
                      rfl

theorem cell22_610215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 2, 1, 3, 2, 3].length) (baseStart_610215 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_610215 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_610215 prefixEnd_610215 := by exact prefixLift 610215
  have htrace : WordTrace (prefixWord ++ tailWord_610215) baseStart_610215 baseEnd_610215 := by
    simpa [prefixWord, tailWord_610215, baseEnd_610215] using wordTrace_append hprefix tailTrace_610215
  have hstable : (prefixWord ++ tailWord_610215).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_610215).length < 2 ^ (prefixWord ++ tailWord_610215).sum := by decide
  have hdescent : baseEnd_610215 < baseStart_610215 := by decide
  rcases family_descends (prefixWord ++ tailWord_610215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_610256 : List Nat := [2, 1, 1, 1, 1, 2, 5, 4, 5]
def baseStart_610256 : Nat := 118140960795 + 610256 * 2 ^ 59
def prefixEnd_610256 : Nat := 4983230072969 + 3 ^ 40 * 610256 * 2
def baseEnd_610256 : Nat := 69634366731171023176331

theorem tailTrace_610256 : CollatzResearch.WordTrace tailWord_610256 prefixEnd_610256 69634366731171023176331 := by
  unfold tailWord_610256
  simp only [CollatzResearch.WordTrace]
  refine ⟨11128932438577105136129311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14838576584769473514839081 11128932438577105136129311)
  ·
    refine ⟨16693398657865657704193967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11128932438577105136129311 16693398657865657704193967)
    ·
      refine ⟨25040097986798486556290951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16693398657865657704193967 25040097986798486556290951)
      ·
        refine ⟨37560146980197729834436427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25040097986798486556290951 37560146980197729834436427)
        ·
          refine ⟨56340220470296594751654641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37560146980197729834436427 56340220470296594751654641)
          ·
            refine ⟨42255165352722446063740981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56340220470296594751654641 42255165352722446063740981)
            ·
              refine ⟨3961421751817729318475717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 42255165352722446063740981 3961421751817729318475717)
              ·
                refine ⟨742766578465824247214197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3961421751817729318475717 742766578465824247214197)
                ·
                  refine ⟨69634366731171023176331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 742766578465824247214197 69634366731171023176331)
                  ·
                    rfl

theorem cell22_610256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 5, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 5, 4, 5].length) (baseStart_610256 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_610256 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_610256 prefixEnd_610256 := by exact prefixLift 610256
  have htrace : WordTrace (prefixWord ++ tailWord_610256) baseStart_610256 baseEnd_610256 := by
    simpa [prefixWord, tailWord_610256, baseEnd_610256] using wordTrace_append hprefix tailTrace_610256
  have hstable : (prefixWord ++ tailWord_610256).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_610256).length < 2 ^ (prefixWord ++ tailWord_610256).sum := by decide
  have hdescent : baseEnd_610256 < baseStart_610256 := by decide
  rcases family_descends (prefixWord ++ tailWord_610256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_610262 : List Nat := [5, 2, 1, 1, 4, 1, 1, 7]
def baseStart_610262 : Nat := 118140960795 + 610262 * 2 ^ 59
def prefixEnd_610262 : Nat := 4983230072969 + 3 ^ 40 * 610262 * 2
def baseEnd_610262 : Nat := 23211683790681228208775

theorem tailTrace_610262 : CollatzResearch.WordTrace tailWord_610262 prefixEnd_610262 23211683790681228208775 := by
  unfold tailWord_610262
  simp only [CollatzResearch.WordTrace]
  refine ⟨1391130232195779581061065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 14838722476754982197984693 1391130232195779581061065)
  ·
    refine ⟨1043347674146834685795799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1391130232195779581061065 1043347674146834685795799)
    ·
      refine ⟨1565021511220252028693699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1043347674146834685795799 1565021511220252028693699)
      ·
        refine ⟨2347532266830378043040549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1565021511220252028693699 2347532266830378043040549)
        ·
          refine ⟨440162300030695883070103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2347532266830378043040549 440162300030695883070103)
          ·
            refine ⟨660243450046043824605155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 440162300030695883070103 660243450046043824605155)
            ·
              refine ⟨990365175069065736907733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 660243450046043824605155 990365175069065736907733)
              ·
                refine ⟨23211683790681228208775, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 990365175069065736907733 23211683790681228208775)
                ·
                  rfl

theorem cell22_610262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 4, 1, 1, 7].length) (baseStart_610262 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_610262 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_610262 prefixEnd_610262 := by exact prefixLift 610262
  have htrace : WordTrace (prefixWord ++ tailWord_610262) baseStart_610262 baseEnd_610262 := by
    simpa [prefixWord, tailWord_610262, baseEnd_610262] using wordTrace_append hprefix tailTrace_610262
  have hstable : (prefixWord ++ tailWord_610262).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_610262).length < 2 ^ (prefixWord ++ tailWord_610262).sum := by decide
  have hdescent : baseEnd_610262 < baseStart_610262 := by decide
  rcases family_descends (prefixWord ++ tailWord_610262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_610271 : List Nat := [1, 1, 2, 3, 4, 1, 1, 1, 1, 7]
def baseStart_610271 : Nat := 118140960795 + 610271 * 2 ^ 59
def prefixEnd_610271 : Nat := 4983230072969 + 3 ^ 40 * 610271 * 2
def baseEnd_610271 : Nat := 208908235000058030403947

theorem tailTrace_610271 : CollatzResearch.WordTrace tailWord_610271 prefixEnd_610271 208908235000058030403947 := by
  unfold tailWord_610271
  simp only [CollatzResearch.WordTrace]
  refine ⟨22258411972099867834054667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14838941314733245222703111 22258411972099867834054667)
  ·
    refine ⟨33387617958149801751082001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22258411972099867834054667 33387617958149801751082001)
    ·
      refine ⟨25040713468612351313311501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33387617958149801751082001 25040713468612351313311501)
      ·
        refine ⟨9390267550729631742491813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25040713468612351313311501 9390267550729631742491813)
        ·
          refine ⟨1760675165761805951717215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9390267550729631742491813 1760675165761805951717215)
          ·
            refine ⟨2641012748642708927575823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1760675165761805951717215 2641012748642708927575823)
            ·
              refine ⟨3961519122964063391363735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2641012748642708927575823 3961519122964063391363735)
              ·
                refine ⟨5942278684446095087045603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3961519122964063391363735 5942278684446095087045603)
                ·
                  refine ⟨8913418026669142630568405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5942278684446095087045603 8913418026669142630568405)
                  ·
                    refine ⟨208908235000058030403947, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 8913418026669142630568405 208908235000058030403947)
                    ·
                      rfl

theorem cell22_610271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 1, 1, 1, 7].length) (baseStart_610271 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_610271 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_610271 prefixEnd_610271 := by exact prefixLift 610271
  have htrace : WordTrace (prefixWord ++ tailWord_610271) baseStart_610271 baseEnd_610271 := by
    simpa [prefixWord, tailWord_610271, baseEnd_610271] using wordTrace_append hprefix tailTrace_610271
  have hstable : (prefixWord ++ tailWord_610271).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_610271).length < 2 ^ (prefixWord ++ tailWord_610271).sum := by decide
  have hdescent : baseEnd_610271 < baseStart_610271 := by decide
  rcases family_descends (prefixWord ++ tailWord_610271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_610294 : List Nat := [5, 1, 1, 1, 4, 1, 2, 3, 1, 3]
def baseStart_610294 : Nat := 118140960795 + 610294 * 2 ^ 59
def prefixEnd_610294 : Nat := 4983230072969 + 3 ^ 40 * 610294 * 2
def baseEnd_610294 : Nat := 208916108370093637078877

theorem tailTrace_610294 : CollatzResearch.WordTrace tailWord_610294 prefixEnd_610294 208916108370093637078877 := by
  unfold tailWord_610294
  simp only [CollatzResearch.WordTrace]
  refine ⟨1391203178188533922633871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 14839500567344361841427957 1391203178188533922633871)
  ·
    refine ⟨2086804767282800883950807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1391203178188533922633871 2086804767282800883950807)
    ·
      refine ⟨3130207150924201325926211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2086804767282800883950807 3130207150924201325926211)
      ·
        refine ⟨4695310726386301988889317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3130207150924201325926211 4695310726386301988889317)
        ·
          refine ⟨880370761197431622916747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4695310726386301988889317 880370761197431622916747)
          ·
            refine ⟨1320556141796147434375121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 880370761197431622916747 1320556141796147434375121)
            ·
              refine ⟨990417106347110575781341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1320556141796147434375121 990417106347110575781341)
              ·
                refine ⟨371406414880166465918003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 990417106347110575781341 371406414880166465918003)
                ·
                  refine ⟨557109622320249698877005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 371406414880166465918003 557109622320249698877005)
                  ·
                    refine ⟨208916108370093637078877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 557109622320249698877005 208916108370093637078877)
                    ·
                      rfl

theorem cell22_610294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 1, 2, 3, 1, 3].length) (baseStart_610294 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_610294 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_610294 prefixEnd_610294 := by exact prefixLift 610294
  have htrace : WordTrace (prefixWord ++ tailWord_610294) baseStart_610294 baseEnd_610294 := by
    simpa [prefixWord, tailWord_610294, baseEnd_610294] using wordTrace_append hprefix tailTrace_610294
  have hstable : (prefixWord ++ tailWord_610294).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_610294).length < 2 ^ (prefixWord ++ tailWord_610294).sum := by decide
  have hdescent : baseEnd_610294 < baseStart_610294 := by decide
  rcases family_descends (prefixWord ++ tailWord_610294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_610318 : List Nat := [4, 1, 1, 2, 2, 1, 4, 1, 6]
def baseStart_610318 : Nat := 118140960795 + 610318 * 2 ^ 59
def prefixEnd_610318 : Nat := 4983230072969 + 3 ^ 40 * 610318 * 2
def baseEnd_610318 : Nat := 69641441353521858159601

theorem tailTrace_610318 : CollatzResearch.WordTrace tailWord_610318 prefixEnd_610318 69641441353521858159601 := by
  unfold tailWord_610318
  simp only [CollatzResearch.WordTrace]
  refine ⟨2782515775366199357626951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14840084135286396574010405 2782515775366199357626951)
  ·
    refine ⟨4173773663049299036440427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2782515775366199357626951 4173773663049299036440427)
    ·
      refine ⟨6260660494573948554660641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4173773663049299036440427 6260660494573948554660641)
      ·
        refine ⟨4695495370930461415995481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6260660494573948554660641 4695495370930461415995481)
        ·
          refine ⟨3521621528197846061996611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4695495370930461415995481 3521621528197846061996611)
          ·
            refine ⟨5282432292296769092994917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3521621528197846061996611 5282432292296769092994917)
            ·
              refine ⟨990456054805644204936547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5282432292296769092994917 990456054805644204936547)
              ·
                refine ⟨1485684082208466307404821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 990456054805644204936547 1485684082208466307404821)
                ·
                  refine ⟨69641441353521858159601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1485684082208466307404821 69641441353521858159601)
                  ·
                    rfl

theorem cell22_610318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 4, 1, 6].length) (baseStart_610318 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_610318 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_610318 prefixEnd_610318 := by exact prefixLift 610318
  have htrace : WordTrace (prefixWord ++ tailWord_610318) baseStart_610318 baseEnd_610318 := by
    simpa [prefixWord, tailWord_610318, baseEnd_610318] using wordTrace_append hprefix tailTrace_610318
  have hstable : (prefixWord ++ tailWord_610318).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_610318).length < 2 ^ (prefixWord ++ tailWord_610318).sum := by decide
  have hdescent : baseEnd_610318 < baseStart_610318 := by decide
  rcases family_descends (prefixWord ++ tailWord_610318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_610324 : List Nat := [2, 4, 3, 2, 1, 1, 3, 1, 5]
def baseStart_610324 : Nat := 118140960795 + 610324 * 2 ^ 59
def prefixEnd_610324 : Nat := 4983230072969 + 3 ^ 40 * 610324 * 2
def baseEnd_610324 : Nat := 69642125994394519609595

theorem tailTrace_610324 : CollatzResearch.WordTrace tailWord_610324 prefixEnd_610324 69642125994394519609595 := by
  unfold tailWord_610324
  simp only [CollatzResearch.WordTrace]
  refine ⟨11130172520453928942867013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14840230027271905257156017 11130172520453928942867013)
  ·
    refine ⟨2086907347585111676787565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11130172520453928942867013 2086907347585111676787565)
    ·
      refine ⟨782590255344416878795337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2086907347585111676787565 782590255344416878795337)
      ·
        refine ⟨586942691508312659096503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 782590255344416878795337 586942691508312659096503)
        ·
          refine ⟨880414037262468988644755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 586942691508312659096503 880414037262468988644755)
          ·
            refine ⟨1320621055893703482967133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 880414037262468988644755 1320621055893703482967133)
            ·
              refine ⟨495232895960138806112675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1320621055893703482967133 495232895960138806112675)
              ·
                refine ⟨742849343940208209169013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 495232895960138806112675 742849343940208209169013)
                ·
                  refine ⟨69642125994394519609595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 742849343940208209169013 69642125994394519609595)
                  ·
                    rfl

theorem cell22_610324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 1, 3, 1, 5].length) (baseStart_610324 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_610324 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_610324 prefixEnd_610324 := by exact prefixLift 610324
  have htrace : WordTrace (prefixWord ++ tailWord_610324) baseStart_610324 baseEnd_610324 := by
    simpa [prefixWord, tailWord_610324, baseEnd_610324] using wordTrace_append hprefix tailTrace_610324
  have hstable : (prefixWord ++ tailWord_610324).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_610324).length < 2 ^ (prefixWord ++ tailWord_610324).sum := by decide
  have hdescent : baseEnd_610324 < baseStart_610324 := by decide
  rcases family_descends (prefixWord ++ tailWord_610324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_610331 : List Nat := [1, 1, 1, 1, 1, 1, 3, 3, 6, 4]
def baseStart_610331 : Nat := 118140960795 + 610331 * 2 ^ 59
def prefixEnd_610331 : Nat := 4983230072969 + 3 ^ 40 * 610331 * 2
def baseEnd_610331 : Nat := 208928774226237873903763

theorem tailTrace_610331 : CollatzResearch.WordTrace tailWord_610331 prefixEnd_610331 208928774226237873903763 := by
  unfold tailWord_610331
  simp only [CollatzResearch.WordTrace]
  refine ⟨22260600351882498081238847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14840400234588332054159231 22260600351882498081238847)
  ·
    refine ⟨33390900527823747121858271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22260600351882498081238847 33390900527823747121858271)
    ·
      refine ⟨50086350791735620682787407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33390900527823747121858271 50086350791735620682787407)
      ·
        refine ⟨75129526187603431024181111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50086350791735620682787407 75129526187603431024181111)
        ·
          refine ⟨112694289281405146536271667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75129526187603431024181111 112694289281405146536271667)
          ·
            refine ⟨169041433922107719804407501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 112694289281405146536271667 169041433922107719804407501)
            ·
              refine ⟨63390537720790394926652813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 169041433922107719804407501 63390537720790394926652813)
              ·
                refine ⟨23771451645296398097494805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 63390537720790394926652813 23771451645296398097494805)
                ·
                  refine ⟨1114286795873268660820069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 23771451645296398097494805 1114286795873268660820069)
                  ·
                    refine ⟨208928774226237873903763, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1114286795873268660820069 208928774226237873903763)
                    ·
                      rfl

theorem cell22_610331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 3, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 3, 6, 4].length) (baseStart_610331 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_610331 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_610331 prefixEnd_610331 := by exact prefixLift 610331
  have htrace : WordTrace (prefixWord ++ tailWord_610331) baseStart_610331 baseEnd_610331 := by
    simpa [prefixWord, tailWord_610331, baseEnd_610331] using wordTrace_append hprefix tailTrace_610331
  have hstable : (prefixWord ++ tailWord_610331).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_610331).length < 2 ^ (prefixWord ++ tailWord_610331).sum := by decide
  have hdescent : baseEnd_610331 < baseStart_610331 := by decide
  rcases family_descends (prefixWord ++ tailWord_610331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_610350 : List Nat := [4, 1, 3, 1, 1, 2, 1, 2, 4, 3]
def baseStart_610350 : Nat := 118140960795 + 610350 * 2 ^ 59
def prefixEnd_610350 : Nat := 4983230072969 + 3 ^ 40 * 610350 * 2
def baseEnd_610350 : Nat := 208935278314528157678705

theorem tailTrace_610350 : CollatzResearch.WordTrace tailWord_610350 prefixEnd_610350 208935278314528157678705 := by
  unfold tailWord_610350
  simp only [CollatzResearch.WordTrace]
  refine ⟨2782661667351708040772563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14840862225875776217453669 2782661667351708040772563)
  ·
    refine ⟨4173992501027562061158845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2782661667351708040772563 4173992501027562061158845)
    ·
      refine ⟨1565247187885335772934567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4173992501027562061158845 1565247187885335772934567)
      ·
        refine ⟨2347870781828003659401851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1565247187885335772934567 2347870781828003659401851)
        ·
          refine ⟨3521806172742005489102777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2347870781828003659401851 3521806172742005489102777)
          ·
            refine ⟨2641354629556504116827083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3521806172742005489102777 2641354629556504116827083)
            ·
              refine ⟨3962031944334756175240625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2641354629556504116827083 3962031944334756175240625)
              ·
                refine ⟨2971523958251067131430469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3962031944334756175240625 2971523958251067131430469)
                ·
                  refine ⟨557160742172075087143213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2971523958251067131430469 557160742172075087143213)
                  ·
                    refine ⟨208935278314528157678705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 557160742172075087143213 208935278314528157678705)
                    ·
                      rfl

theorem cell22_610350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 1, 2, 4, 3].length) (baseStart_610350 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_610350 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_610350 prefixEnd_610350 := by exact prefixLift 610350
  have htrace : WordTrace (prefixWord ++ tailWord_610350) baseStart_610350 baseEnd_610350 := by
    simpa [prefixWord, tailWord_610350, baseEnd_610350] using wordTrace_append hprefix tailTrace_610350
  have hstable : (prefixWord ++ tailWord_610350).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_610350).length < 2 ^ (prefixWord ++ tailWord_610350).sum := by decide
  have hdescent : baseEnd_610350 < baseStart_610350 := by decide
  rcases family_descends (prefixWord ++ tailWord_610350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_610425 : List Nat := [1, 2, 1, 3, 4, 2, 2, 2, 5]
def baseStart_610425 : Nat := 118140960795 + 610425 * 2 ^ 59
def prefixEnd_610425 : Nat := 4983230072969 + 3 ^ 40 * 610425 * 2
def baseEnd_610425 : Nat := 69653650782417654017825

theorem tailTrace_610425 : CollatzResearch.WordTrace tailWord_610425 prefixEnd_610425 69653650782417654017825 := by
  unfold tailWord_610425
  simp only [CollatzResearch.WordTrace]
  refine ⟨22264028813541952135160729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14842685875694634756773819 22264028813541952135160729)
  ·
    refine ⟨16698021610156464101370547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22264028813541952135160729 16698021610156464101370547)
    ·
      refine ⟨25047032415234696152055821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16698021610156464101370547 25047032415234696152055821)
      ·
        refine ⟨9392637155713011057020933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25047032415234696152055821 9392637155713011057020933)
        ·
          refine ⟨1761119466696189573191425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9392637155713011057020933 1761119466696189573191425)
          ·
            refine ⟨1320839600022142179893569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1761119466696189573191425 1320839600022142179893569)
            ·
              refine ⟨990629700016606634920177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1320839600022142179893569 990629700016606634920177)
              ·
                refine ⟨742972275012454976190133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 990629700016606634920177 742972275012454976190133)
                ·
                  refine ⟨69653650782417654017825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 742972275012454976190133 69653650782417654017825)
                  ·
                    rfl

theorem cell22_610425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 2, 2, 2, 5].length) (baseStart_610425 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_610425 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_610425 prefixEnd_610425 := by exact prefixLift 610425
  have htrace : WordTrace (prefixWord ++ tailWord_610425) baseStart_610425 baseEnd_610425 := by
    simpa [prefixWord, tailWord_610425, baseEnd_610425] using wordTrace_append hprefix tailTrace_610425
  have hstable : (prefixWord ++ tailWord_610425).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_610425).length < 2 ^ (prefixWord ++ tailWord_610425).sum := by decide
  have hdescent : baseEnd_610425 < baseStart_610425 := by decide
  rcases family_descends (prefixWord ++ tailWord_610425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_610429 : List Nat := [1, 4, 1, 1, 3, 2, 4, 2, 1, 3]
def baseStart_610429 : Nat := 118140960795 + 610429 * 2 ^ 59
def prefixEnd_610429 : Nat := 4983230072969 + 3 ^ 40 * 610429 * 2
def baseEnd_610429 : Nat := 208962321628998284953463

theorem tailTrace_610429 : CollatzResearch.WordTrace tailWord_610429 prefixEnd_610429 208962321628998284953463 := by
  unfold tailWord_610429
  simp only [CollatzResearch.WordTrace]
  refine ⟨22264174705527460818306341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14842783137018307212204227 22264174705527460818306341)
  ·
    refine ⟨4174532757286398903432439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 22264174705527460818306341 4174532757286398903432439)
    ·
      refine ⟨6261799135929598355148659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4174532757286398903432439 6261799135929598355148659)
      ·
        refine ⟨9392698703894397532722989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6261799135929598355148659 9392698703894397532722989)
        ·
          refine ⟨3522262013960399074771121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9392698703894397532722989 3522262013960399074771121)
          ·
            refine ⟨2641696510470299306078341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3522262013960399074771121 2641696510470299306078341)
            ·
              refine ⟨495318095713181119889689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2641696510470299306078341 495318095713181119889689)
              ·
                refine ⟨371488571784885839917267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 495318095713181119889689 371488571784885839917267)
                ·
                  refine ⟨557232857677328759875901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 371488571784885839917267 557232857677328759875901)
                  ·
                    refine ⟨208962321628998284953463, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 557232857677328759875901 208962321628998284953463)
                    ·
                      rfl

theorem cell22_610429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 4, 2, 1, 3].length) (baseStart_610429 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_610429 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_610429 prefixEnd_610429 := by exact prefixLift 610429
  have htrace : WordTrace (prefixWord ++ tailWord_610429) baseStart_610429 baseEnd_610429 := by
    simpa [prefixWord, tailWord_610429, baseEnd_610429] using wordTrace_append hprefix tailTrace_610429
  have hstable : (prefixWord ++ tailWord_610429).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_610429).length < 2 ^ (prefixWord ++ tailWord_610429).sum := by decide
  have hdescent : baseEnd_610429 < baseStart_610429 := by decide
  rcases family_descends (prefixWord ++ tailWord_610429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_610440 : List Nat := [2, 1, 3, 4, 1, 2, 1, 1, 2, 5]
def baseStart_610440 : Nat := 118140960795 + 610440 * 2 ^ 59
def prefixEnd_610440 : Nat := 4983230072969 + 3 ^ 40 * 610440 * 2
def baseEnd_610440 : Nat := 208966087153797922928429

theorem tailTrace_610440 : CollatzResearch.WordTrace tailWord_610440 prefixEnd_610440 208966087153797922928429 := by
  unfold tailWord_610440
  simp only [CollatzResearch.WordTrace]
  refine ⟨11132287954243804848478387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14843050605658406464637849 11132287954243804848478387)
  ·
    refine ⟨16698431931365707272717581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11132287954243804848478387 16698431931365707272717581)
    ·
      refine ⟨6261911974262140227269093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16698431931365707272717581 6261911974262140227269093)
      ·
        refine ⟨1174108495174151292612955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6261911974262140227269093 1174108495174151292612955)
        ·
          refine ⟨1761162742761226938919433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1174108495174151292612955 1761162742761226938919433)
          ·
            refine ⟨1320872057070920204189575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1761162742761226938919433 1320872057070920204189575)
            ·
              refine ⟨1981308085606380306284363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1320872057070920204189575 1981308085606380306284363)
              ·
                refine ⟨2971962128409570459426545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1981308085606380306284363 2971962128409570459426545)
                ·
                  refine ⟨2228971596307177844569909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2971962128409570459426545 2228971596307177844569909)
                  ·
                    refine ⟨208966087153797922928429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2228971596307177844569909 208966087153797922928429)
                    ·
                      rfl

theorem cell22_610440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 2, 1, 1, 2, 5].length) (baseStart_610440 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_610440 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_610440 prefixEnd_610440 := by exact prefixLift 610440
  have htrace : WordTrace (prefixWord ++ tailWord_610440) baseStart_610440 baseEnd_610440 := by
    simpa [prefixWord, tailWord_610440, baseEnd_610440] using wordTrace_append hprefix tailTrace_610440
  have hstable : (prefixWord ++ tailWord_610440).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_610440).length < 2 ^ (prefixWord ++ tailWord_610440).sum := by decide
  have hdescent : baseEnd_610440 < baseStart_610440 := by decide
  rcases family_descends (prefixWord ++ tailWord_610440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_610453 : List Nat := [1, 3, 2, 1, 1, 1, 5, 2, 6]
def baseStart_610453 : Nat := 118140960795 + 610453 * 2 ^ 59
def prefixEnd_610453 : Nat := 4983230072969 + 3 ^ 40 * 610453 * 2
def baseEnd_610453 : Nat := 69656845773156740784463

theorem tailTrace_610453 : CollatzResearch.WordTrace tailWord_610453 prefixEnd_610453 69656845773156740784463 := by
  unfold tailWord_610453
  simp only [CollatzResearch.WordTrace]
  refine ⟨22265050057440512917180013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14843366704960341944786675 22265050057440512917180013)
  ·
    refine ⟨8349393771540192343942505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22265050057440512917180013 8349393771540192343942505)
    ·
      refine ⟨6262045328655144257956879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8349393771540192343942505 6262045328655144257956879)
      ·
        refine ⟨9393067992982716386935319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6262045328655144257956879 9393067992982716386935319)
        ·
          refine ⟨14089601989474074580402979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9393067992982716386935319 14089601989474074580402979)
          ·
            refine ⟨21134402984211111870604469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14089601989474074580402979 21134402984211111870604469)
            ·
              refine ⟨1981350279769791737869169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 21134402984211111870604469 1981350279769791737869169)
              ·
                refine ⟨1486012709827343803401877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1981350279769791737869169 1486012709827343803401877)
                ·
                  refine ⟨69656845773156740784463, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1486012709827343803401877 69656845773156740784463)
                  ·
                    rfl

theorem cell22_610453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 5, 2, 6].length) (baseStart_610453 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_610453 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_610453 prefixEnd_610453 := by exact prefixLift 610453
  have htrace : WordTrace (prefixWord ++ tailWord_610453) baseStart_610453 baseEnd_610453 := by
    simpa [prefixWord, tailWord_610453, baseEnd_610453] using wordTrace_append hprefix tailTrace_610453
  have hstable : (prefixWord ++ tailWord_610453).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_610453).length < 2 ^ (prefixWord ++ tailWord_610453).sum := by decide
  have hdescent : baseEnd_610453 < baseStart_610453 := by decide
  rcases family_descends (prefixWord ++ tailWord_610453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_610483 : List Nat := [1, 1, 1, 2, 3, 2, 1, 3, 4, 4]
def baseStart_610483 : Nat := 118140960795 + 610483 * 2 ^ 59
def prefixEnd_610483 : Nat := 4983230072969 + 3 ^ 40 * 610483 * 2
def baseEnd_610483 : Nat := 208980806932560144103297

theorem tailTrace_610483 : CollatzResearch.WordTrace tailWord_610483 prefixEnd_610483 208980806932560144103297 := by
  unfold tailWord_610483
  simp only [CollatzResearch.WordTrace]
  refine ⟨22266144247331828040772103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14844096164887885360514735 22266144247331828040772103)
  ·
    refine ⟨33399216370997742061158155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22266144247331828040772103 33399216370997742061158155)
    ·
      refine ⟨50098824556496613091737233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33399216370997742061158155 50098824556496613091737233)
      ·
        refine ⟨37574118417372459818802925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50098824556496613091737233 37574118417372459818802925)
        ·
          refine ⟨14090294406514672432051097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37574118417372459818802925 14090294406514672432051097)
          ·
            refine ⟨10567720804886004324038323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14090294406514672432051097 10567720804886004324038323)
            ·
              refine ⟨15851581207329006486057485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10567720804886004324038323 15851581207329006486057485)
              ·
                refine ⟨5944342952748377432271557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15851581207329006486057485 5944342952748377432271557)
                ·
                  refine ⟨1114564303640320768550917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5944342952748377432271557 1114564303640320768550917)
                  ·
                    refine ⟨208980806932560144103297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1114564303640320768550917 208980806932560144103297)
                    ·
                      rfl

theorem cell22_610483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 3, 4, 4].length) (baseStart_610483 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_610483 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_610483 prefixEnd_610483 := by exact prefixLift 610483
  have htrace : WordTrace (prefixWord ++ tailWord_610483) baseStart_610483 baseEnd_610483 := by
    simpa [prefixWord, tailWord_610483, baseEnd_610483] using wordTrace_append hprefix tailTrace_610483
  have hstable : (prefixWord ++ tailWord_610483).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_610483).length < 2 ^ (prefixWord ++ tailWord_610483).sum := by decide
  have hdescent : baseEnd_610483 < baseStart_610483 := by decide
  rcases family_descends (prefixWord ++ tailWord_610483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_610500 : List Nat := [2, 3, 3, 1, 2, 1, 1, 2, 1, 6]
def baseStart_610500 : Nat := 118140960795 + 610500 * 2 ^ 59
def prefixEnd_610500 : Nat := 4983230072969 + 3 ^ 40 * 610500 * 2
def baseEnd_610500 : Nat := 208986626379977766428245

theorem tailTrace_610500 : CollatzResearch.WordTrace tailWord_610500 prefixEnd_610500 208986626379977766428245 := by
  unfold tailWord_610500
  simp only [CollatzResearch.WordTrace]
  refine ⟨11133382144135119972070477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14844509525513493296093969 11133382144135119972070477)
  ·
    refine ⟨4175018304050669989526429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11133382144135119972070477 4175018304050669989526429)
    ·
      refine ⟨1565631864019001246072411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4175018304050669989526429 1565631864019001246072411)
      ·
        refine ⟨2348447796028501869108617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1565631864019001246072411 2348447796028501869108617)
        ·
          refine ⟨1761335847021376401831463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2348447796028501869108617 1761335847021376401831463)
          ·
            refine ⟨2642003770532064602747195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1761335847021376401831463 2642003770532064602747195)
            ·
              refine ⟨3963005655798096904120793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2642003770532064602747195 3963005655798096904120793)
              ·
                refine ⟨2972254241848572678090595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3963005655798096904120793 2972254241848572678090595)
                ·
                  refine ⟨4458381362772859017135893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2972254241848572678090595 4458381362772859017135893)
                  ·
                    refine ⟨208986626379977766428245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4458381362772859017135893 208986626379977766428245)
                    ·
                      rfl

theorem cell22_610500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 1, 2, 1, 6].length) (baseStart_610500 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_610500 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_610500 prefixEnd_610500 := by exact prefixLift 610500
  have htrace : WordTrace (prefixWord ++ tailWord_610500) baseStart_610500 baseEnd_610500 := by
    simpa [prefixWord, tailWord_610500, baseEnd_610500] using wordTrace_append hprefix tailTrace_610500
  have hstable : (prefixWord ++ tailWord_610500).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_610500).length < 2 ^ (prefixWord ++ tailWord_610500).sum := by decide
  have hdescent : baseEnd_610500 < baseStart_610500 := by decide
  rcases family_descends (prefixWord ++ tailWord_610500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_610603 : List Nat := [1, 1, 1, 1, 2, 1, 2, 1, 1, 11]
def baseStart_610603 : Nat := 118140960795 + 610603 * 2 ^ 59
def prefixEnd_610603 : Nat := 4983230072969 + 3 ^ 40 * 610603 * 2
def baseEnd_610603 : Nat := 209021885384919831102929

theorem tailTrace_610603 : CollatzResearch.WordTrace tailWord_610603 prefixEnd_610603 209021885384919831102929 := by
  unfold tailWord_610603
  simp only [CollatzResearch.WordTrace]
  refine ⟨22270521006897088535140463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14847014004598059023426975 22270521006897088535140463)
  ·
    refine ⟨33405781510345632802710695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22270521006897088535140463 33405781510345632802710695)
    ·
      refine ⟨50108672265518449204066043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33405781510345632802710695 50108672265518449204066043)
      ·
        refine ⟨75163008398277673806099065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50108672265518449204066043 75163008398277673806099065)
        ·
          refine ⟨56372256298708255354574299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 75163008398277673806099065 56372256298708255354574299)
          ·
            refine ⟨84558384448062383031861449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56372256298708255354574299 84558384448062383031861449)
            ·
              refine ⟨63418788336046787273896087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 84558384448062383031861449 63418788336046787273896087)
              ·
                refine ⟨95128182504070180910844131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 63418788336046787273896087 95128182504070180910844131)
                ·
                  refine ⟨142692273756105271366266197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 95128182504070180910844131 142692273756105271366266197)
                  ·
                    refine ⟨209021885384919831102929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 11 142692273756105271366266197 209021885384919831102929)
                    ·
                      rfl

theorem cell22_610603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 1, 1, 11].length) (baseStart_610603 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_610603 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_610603 prefixEnd_610603 := by exact prefixLift 610603
  have htrace : WordTrace (prefixWord ++ tailWord_610603) baseStart_610603 baseEnd_610603 := by
    simpa [prefixWord, tailWord_610603, baseEnd_610603] using wordTrace_append hprefix tailTrace_610603
  have hstable : (prefixWord ++ tailWord_610603).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_610603).length < 2 ^ (prefixWord ++ tailWord_610603).sum := by decide
  have hdescent : baseEnd_610603 < baseStart_610603 := by decide
  rcases family_descends (prefixWord ++ tailWord_610603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_610622 : List Nat := [4, 2, 1, 2, 1, 3, 1, 2, 6]
def baseStart_610622 : Nat := 118140960795 + 610622 * 2 ^ 59
def prefixEnd_610622 : Nat := 4983230072969 + 3 ^ 40 * 610622 * 2
def baseEnd_610622 : Nat := 69676129824403371625957

theorem tailTrace_610622 : CollatzResearch.WordTrace tailWord_610622 prefixEnd_610622 69676129824403371625957 := by
  unfold tailWord_610622
  simp only [CollatzResearch.WordTrace]
  refine ⟨2783901749228531847510265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14847475995885503186721413 2783901749228531847510265)
  ·
    refine ⟨2087926311921398885632699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2783901749228531847510265 2087926311921398885632699)
    ·
      refine ⟨3131889467882098328449049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2087926311921398885632699 3131889467882098328449049)
      ·
        refine ⟨2348917100911573746336787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3131889467882098328449049 2348917100911573746336787)
        ·
          refine ⟨3523375651367360619505181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2348917100911573746336787 3523375651367360619505181)
          ·
            refine ⟨1321265869262760232314443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3523375651367360619505181 1321265869262760232314443)
            ·
              refine ⟨1981898803894140348471665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1321265869262760232314443 1981898803894140348471665)
              ·
                refine ⟨1486424102920605261353749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1981898803894140348471665 1486424102920605261353749)
                ·
                  refine ⟨69676129824403371625957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1486424102920605261353749 69676129824403371625957)
                  ·
                    rfl

theorem cell22_610622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 3, 1, 2, 6].length) (baseStart_610622 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_610622 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_610622 prefixEnd_610622 := by exact prefixLift 610622
  have htrace : WordTrace (prefixWord ++ tailWord_610622) baseStart_610622 baseEnd_610622 := by
    simpa [prefixWord, tailWord_610622, baseEnd_610622] using wordTrace_append hprefix tailTrace_610622
  have hstable : (prefixWord ++ tailWord_610622).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_610622).length < 2 ^ (prefixWord ++ tailWord_610622).sum := by decide
  have hdescent : baseEnd_610622 < baseStart_610622 := by decide
  rcases family_descends (prefixWord ++ tailWord_610622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_610635 : List Nat := [1, 1, 1, 1, 3, 1, 1, 7, 2, 4]
def baseStart_610635 : Nat := 118140960795 + 610635 * 2 ^ 59
def prefixEnd_610635 : Nat := 4983230072969 + 3 ^ 40 * 610635 * 2
def baseEnd_610635 : Nat := 209032839638882414302831

theorem tailTrace_610635 : CollatzResearch.WordTrace tailWord_610635 prefixEnd_610635 209032839638882414302831 := by
  unfold tailWord_610635
  simp only [CollatzResearch.WordTrace]
  refine ⟨22271688142781158000305359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14847792095187438666870239 22271688142781158000305359)
  ·
    refine ⟨33407532214171737000458039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22271688142781158000305359 33407532214171737000458039)
    ·
      refine ⟨50111298321257605500687059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33407532214171737000458039 50111298321257605500687059)
      ·
        refine ⟨75166947481886408251030589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50111298321257605500687059 75166947481886408251030589)
        ·
          refine ⟨28187605305707403094136471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 75166947481886408251030589 28187605305707403094136471)
          ·
            refine ⟨42281407958561104641204707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28187605305707403094136471 42281407958561104641204707)
            ·
              refine ⟨63422111937841656961807061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42281407958561104641204707 63422111937841656961807061)
              ·
                refine ⟨1486455748543163835042353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 63422111937841656961807061 1486455748543163835042353)
                ·
                  refine ⟨1114841811407372876281765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1486455748543163835042353 1114841811407372876281765)
                  ·
                    refine ⟨209032839638882414302831, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1114841811407372876281765 209032839638882414302831)
                    ·
                      rfl

theorem cell22_610635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 7, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 7, 2, 4].length) (baseStart_610635 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_610635 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_610635 prefixEnd_610635 := by exact prefixLift 610635
  have htrace : WordTrace (prefixWord ++ tailWord_610635) baseStart_610635 baseEnd_610635 := by
    simpa [prefixWord, tailWord_610635, baseEnd_610635] using wordTrace_append hprefix tailTrace_610635
  have hstable : (prefixWord ++ tailWord_610635).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_610635).length < 2 ^ (prefixWord ++ tailWord_610635).sum := by decide
  have hdescent : baseEnd_610635 < baseStart_610635 := by decide
  rcases family_descends (prefixWord ++ tailWord_610635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_610690 : List Nat := [3, 4, 2, 1, 3, 1, 1, 3, 4]
def baseStart_610690 : Nat := 118140960795 + 610690 * 2 ^ 59
def prefixEnd_610690 : Nat := 4983230072969 + 3 ^ 40 * 610690 * 2
def baseEnd_610690 : Nat := 69683889087626868059221

theorem tailTrace_610690 : CollatzResearch.WordTrace tailWord_610690 prefixEnd_610690 69683889087626868059221 := by
  unfold tailWord_610690
  simp only [CollatzResearch.WordTrace]
  refine ⟨5568423539395475598389381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14849129438387934929038349 5568423539395475598389381)
  ·
    refine ⟨1044079413636651674698009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5568423539395475598389381 1044079413636651674698009)
    ·
      refine ⟨783059560227488756023507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1044079413636651674698009 783059560227488756023507)
      ·
        refine ⟨1174589340341233134035261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 783059560227488756023507 1174589340341233134035261)
        ·
          refine ⟨440471002627962425263223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1174589340341233134035261 440471002627962425263223)
          ·
            refine ⟨660706503941943637894835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 440471002627962425263223 660706503941943637894835)
            ·
              refine ⟨991059755912915456842253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 660706503941943637894835 991059755912915456842253)
              ·
                refine ⟨371647408467343296315845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 991059755912915456842253 371647408467343296315845)
                ·
                  refine ⟨69683889087626868059221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 371647408467343296315845 69683889087626868059221)
                  ·
                    rfl

theorem cell22_610690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 3, 1, 1, 3, 4].length) (baseStart_610690 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_610690 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_610690 prefixEnd_610690 := by exact prefixLift 610690
  have htrace : WordTrace (prefixWord ++ tailWord_610690) baseStart_610690 baseEnd_610690 := by
    simpa [prefixWord, tailWord_610690, baseEnd_610690] using wordTrace_append hprefix tailTrace_610690
  have hstable : (prefixWord ++ tailWord_610690).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_610690).length < 2 ^ (prefixWord ++ tailWord_610690).sum := by decide
  have hdescent : baseEnd_610690 < baseStart_610690 := by decide
  rcases family_descends (prefixWord ++ tailWord_610690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_610695 : List Nat := [1, 1, 4, 2, 2, 1, 1, 1, 9]
def baseStart_610695 : Nat := 118140960795 + 610695 * 2 ^ 59
def prefixEnd_610695 : Nat := 4983230072969 + 3 ^ 40 * 610695 * 2
def baseEnd_610695 : Nat := 69684459621687419267549

theorem tailTrace_610695 : CollatzResearch.WordTrace tailWord_610695 prefixEnd_610695 69684459621687419267549 := by
  unfold tailWord_610695
  simp only [CollatzResearch.WordTrace]
  refine ⟨22273876522563788247489539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14849251015042525498326359 22273876522563788247489539)
  ·
    refine ⟨33410814783845682371234309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22273876522563788247489539 33410814783845682371234309)
    ·
      refine ⟨6264527771971065444606433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 33410814783845682371234309 6264527771971065444606433)
      ·
        refine ⟨4698395828978299083454825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6264527771971065444606433 4698395828978299083454825)
        ·
          refine ⟨3523796871733724312591119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4698395828978299083454825 3523796871733724312591119)
          ·
            refine ⟨5285695307600586468886679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3523796871733724312591119 5285695307600586468886679)
            ·
              refine ⟨7928542961400879703330019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5285695307600586468886679 7928542961400879703330019)
              ·
                refine ⟨11892814442101319554995029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7928542961400879703330019 11892814442101319554995029)
                ·
                  refine ⟨69684459621687419267549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 11892814442101319554995029 69684459621687419267549)
                  ·
                    rfl

theorem cell22_610695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 1, 1, 9].length) (baseStart_610695 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_610695 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_610695 prefixEnd_610695 := by exact prefixLift 610695
  have htrace : WordTrace (prefixWord ++ tailWord_610695) baseStart_610695 baseEnd_610695 := by
    simpa [prefixWord, tailWord_610695, baseEnd_610695] using wordTrace_append hprefix tailTrace_610695
  have hstable : (prefixWord ++ tailWord_610695).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_610695).length < 2 ^ (prefixWord ++ tailWord_610695).sum := by decide
  have hdescent : baseEnd_610695 < baseStart_610695 := by decide
  rcases family_descends (prefixWord ++ tailWord_610695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_610712 : List Nat := [2, 1, 2, 5, 1, 1, 2, 1, 7]
def baseStart_610712 : Nat := 118140960795 + 610712 * 2 ^ 59
def prefixEnd_610712 : Nat := 4983230072969 + 3 ^ 40 * 610712 * 2
def baseEnd_610712 : Nat := 69686399437493293375865

theorem tailTrace_610712 : CollatzResearch.WordTrace tailWord_610712 prefixEnd_610712 69686399437493293375865 := by
  unfold tailWord_610712
  simp only [CollatzResearch.WordTrace]
  refine ⟨11137248281751100075429195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14849664375668133433905593 11137248281751100075429195)
  ·
    refine ⟨16705872422626650113143793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11137248281751100075429195 16705872422626650113143793)
    ·
      refine ⟨12529404316969987584857845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16705872422626650113143793 12529404316969987584857845)
      ·
        refine ⟨1174631654715936336080423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 12529404316969987584857845 1174631654715936336080423)
        ·
          refine ⟨1761947482073904504120635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1174631654715936336080423 1761947482073904504120635)
          ·
            refine ⟨2642921223110856756180953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1761947482073904504120635 2642921223110856756180953)
            ·
              refine ⟨1982190917333142567135715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2642921223110856756180953 1982190917333142567135715)
              ·
                refine ⟨2973286375999713850703573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1982190917333142567135715 2973286375999713850703573)
                ·
                  refine ⟨69686399437493293375865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2973286375999713850703573 69686399437493293375865)
                  ·
                    rfl

theorem cell22_610712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 2, 1, 7].length) (baseStart_610712 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_610712 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_610712 prefixEnd_610712 := by exact prefixLift 610712
  have htrace : WordTrace (prefixWord ++ tailWord_610712) baseStart_610712 baseEnd_610712 := by
    simpa [prefixWord, tailWord_610712, baseEnd_610712] using wordTrace_append hprefix tailTrace_610712
  have hstable : (prefixWord ++ tailWord_610712).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_610712).length < 2 ^ (prefixWord ++ tailWord_610712).sum := by decide
  have hdescent : baseEnd_610712 < baseStart_610712 := by decide
  rcases family_descends (prefixWord ++ tailWord_610712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_610774 : List Nat := [5, 2, 1, 1, 1, 1, 2, 3, 6]
def baseStart_610774 : Nat := 118140960795 + 610774 * 2 ^ 59
def prefixEnd_610774 : Nat := 4983230072969 + 3 ^ 40 * 610774 * 2
def baseEnd_610774 : Nat := 69693474059844128359135

theorem tailTrace_610774 : CollatzResearch.WordTrace tailWord_610774 prefixEnd_610774 69693474059844128359135 := by
  unfold tailWord_610774
  simp only [CollatzResearch.WordTrace]
  refine ⟨1392297368079849046225961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 14851171926185056493076917 1392297368079849046225961)
  ·
    refine ⟨1044223026059886784669471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1392297368079849046225961 1044223026059886784669471)
    ·
      refine ⟨1566334539089830177004207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1044223026059886784669471 1566334539089830177004207)
      ·
        refine ⟨2349501808634745265506311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1566334539089830177004207 2349501808634745265506311)
        ·
          refine ⟨3524252712952117898259467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2349501808634745265506311 3524252712952117898259467)
          ·
            refine ⟨5286379069428176847389201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3524252712952117898259467 5286379069428176847389201)
            ·
              refine ⟨3964784302071132635541901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5286379069428176847389201 3964784302071132635541901)
              ·
                refine ⟨1486794113276674738328213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3964784302071132635541901 1486794113276674738328213)
                ·
                  refine ⟨69693474059844128359135, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1486794113276674738328213 69693474059844128359135)
                  ·
                    rfl

theorem cell22_610774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 2, 3, 6].length) (baseStart_610774 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_610774 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_610774 prefixEnd_610774 := by exact prefixLift 610774
  have htrace : WordTrace (prefixWord ++ tailWord_610774) baseStart_610774 baseEnd_610774 := by
    simpa [prefixWord, tailWord_610774, baseEnd_610774] using wordTrace_append hprefix tailTrace_610774
  have hstable : (prefixWord ++ tailWord_610774).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_610774).length < 2 ^ (prefixWord ++ tailWord_610774).sum := by decide
  have hdescent : baseEnd_610774 < baseStart_610774 := by decide
  rcases family_descends (prefixWord ++ tailWord_610774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_610823 : List Nat := [1, 1, 4, 3, 3, 2, 1, 2, 2, 3]
def baseStart_610823 : Nat := 118140960795 + 610823 * 2 ^ 59
def prefixEnd_610823 : Nat := 4983230072969 + 3 ^ 40 * 610823 * 2
def baseEnd_610823 : Nat := 209097195880912590602255

theorem tailTrace_610823 : CollatzResearch.WordTrace tailWord_610823 prefixEnd_610823 209097195880912590602255 := by
  unfold tailWord_610823
  simp only [CollatzResearch.WordTrace]
  refine ⟨22278545066100066108149123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14852363377400044072099415 22278545066100066108149123)
  ·
    refine ⟨33417817599150099162223685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22278545066100066108149123 33417817599150099162223685)
    ·
      refine ⟨6265840799840643592916941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 33417817599150099162223685 6265840799840643592916941)
      ·
        refine ⟨2349690299940241347343853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6265840799840643592916941 2349690299940241347343853)
        ·
          refine ⟨881133862477590505253945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2349690299940241347343853 881133862477590505253945)
          ·
            refine ⟨660850396858192878940459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 881133862477590505253945 660850396858192878940459)
            ·
              refine ⟨991275595287289318410689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 660850396858192878940459 991275595287289318410689)
              ·
                refine ⟨743456696465466988808017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 991275595287289318410689 743456696465466988808017)
                ·
                  refine ⟨557592522349100241606013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 743456696465466988808017 557592522349100241606013)
                  ·
                    refine ⟨209097195880912590602255, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 557592522349100241606013 209097195880912590602255)
                    ·
                      rfl

theorem cell22_610823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 2, 1, 2, 2, 3].length) (baseStart_610823 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_610823 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_610823 prefixEnd_610823 := by exact prefixLift 610823
  have htrace : WordTrace (prefixWord ++ tailWord_610823) baseStart_610823 baseEnd_610823 := by
    simpa [prefixWord, tailWord_610823, baseEnd_610823] using wordTrace_append hprefix tailTrace_610823
  have hstable : (prefixWord ++ tailWord_610823).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_610823).length < 2 ^ (prefixWord ++ tailWord_610823).sum := by decide
  have hdescent : baseEnd_610823 < baseStart_610823 := by decide
  rcases family_descends (prefixWord ++ tailWord_610823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_610924 : List Nat := [2, 2, 1, 1, 3, 1, 2, 1, 6, 3]
def baseStart_610924 : Nat := 118140960795 + 610924 * 2 ^ 59
def prefixEnd_610924 : Nat := 4983230072969 + 3 ^ 40 * 610924 * 2
def baseEnd_610924 : Nat := 209131770244981993826945

theorem tailTrace_610924 : CollatzResearch.WordTrace tailWord_610924 prefixEnd_610924 209131770244981993826945 := by
  unfold tailWord_610924
  simp only [CollatzResearch.WordTrace]
  refine ⟨11141114419367080178787913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14854819225822773571717217 11141114419367080178787913)
  ·
    refine ⟨8355835814525310134090935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11141114419367080178787913 8355835814525310134090935)
    ·
      refine ⟨12533753721787965201136403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8355835814525310134090935 12533753721787965201136403)
      ·
        refine ⟨18800630582681947801704605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12533753721787965201136403 18800630582681947801704605)
        ·
          refine ⟨7050236468505730425639227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18800630582681947801704605 7050236468505730425639227)
          ·
            refine ⟨10575354702758595638458841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7050236468505730425639227 10575354702758595638458841)
            ·
              refine ⟨7931516027068946728844131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10575354702758595638458841 7931516027068946728844131)
              ·
                refine ⟨11897274040603420093266197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7931516027068946728844131 11897274040603420093266197)
                ·
                  refine ⟨557684720653285316871853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 11897274040603420093266197 557684720653285316871853)
                  ·
                    refine ⟨209131770244981993826945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 557684720653285316871853 209131770244981993826945)
                    ·
                      rfl

theorem cell22_610924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 6, 3].length) (baseStart_610924 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_610924 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_610924 prefixEnd_610924 := by exact prefixLift 610924
  have htrace : WordTrace (prefixWord ++ tailWord_610924) baseStart_610924 baseEnd_610924 := by
    simpa [prefixWord, tailWord_610924, baseEnd_610924] using wordTrace_append hprefix tailTrace_610924
  have hstable : (prefixWord ++ tailWord_610924).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_610924).length < 2 ^ (prefixWord ++ tailWord_610924).sum := by decide
  have hdescent : baseEnd_610924 < baseStart_610924 := by decide
  rcases family_descends (prefixWord ++ tailWord_610924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_610928 : List Nat := [2, 1, 1, 1, 7, 1, 3, 1, 1, 4]
def baseStart_610928 : Nat := 118140960795 + 610928 * 2 ^ 59
def prefixEnd_610928 : Nat := 4983230072969 + 3 ^ 40 * 610928 * 2
def baseEnd_610928 : Nat := 209133139526727316726933

theorem tailTrace_610928 : CollatzResearch.WordTrace tailWord_610928 prefixEnd_610928 209133139526727316726933 := by
  unfold tailWord_610928
  simp only [CollatzResearch.WordTrace]
  refine ⟨11141187365359834520360719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14854916487146446027147625 11141187365359834520360719)
  ·
    refine ⟨16711781048039751780541079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11141187365359834520360719 16711781048039751780541079)
    ·
      refine ⟨25067671572059627670811619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16711781048039751780541079 25067671572059627670811619)
      ·
        refine ⟨37601507358089441506217429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25067671572059627670811619 37601507358089441506217429)
        ·
          refine ⟨881285328705221285301971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 37601507358089441506217429 881285328705221285301971)
          ·
            refine ⟨1321927993057831927952957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 881285328705221285301971 1321927993057831927952957)
            ·
              refine ⟨495722997396686972982359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1321927993057831927952957 495722997396686972982359)
              ·
                refine ⟨743584496095030459473539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 495722997396686972982359 743584496095030459473539)
                ·
                  refine ⟨1115376744142545689210309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 743584496095030459473539 1115376744142545689210309)
                  ·
                    refine ⟨209133139526727316726933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1115376744142545689210309 209133139526727316726933)
                    ·
                      rfl

theorem cell22_610928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 1, 3, 1, 1, 4].length) (baseStart_610928 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_610928 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_610928 prefixEnd_610928 := by exact prefixLift 610928
  have htrace : WordTrace (prefixWord ++ tailWord_610928) baseStart_610928 baseEnd_610928 := by
    simpa [prefixWord, tailWord_610928, baseEnd_610928] using wordTrace_append hprefix tailTrace_610928
  have hstable : (prefixWord ++ tailWord_610928).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_610928).length < 2 ^ (prefixWord ++ tailWord_610928).sum := by decide
  have hdescent : baseEnd_610928 < baseStart_610928 := by decide
  rcases family_descends (prefixWord ++ tailWord_610928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_610937 : List Nat := [1, 2, 1, 3, 3, 12]
def baseStart_610937 : Nat := 118140960795 + 610937 * 2 ^ 59
def prefixEnd_610937 : Nat := 4983230072969 + 3 ^ 40 * 610937 * 2
def baseEnd_610937 : Nat := 2581928647045114731505

theorem tailTrace_610937 : CollatzResearch.WordTrace tailWord_610937 prefixEnd_610937 2581928647045114731505 := by
  unfold tailWord_610937
  simp only [CollatzResearch.WordTrace]
  refine ⟨22282702987687063577799065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14855135325124709051866043 22282702987687063577799065)
  ·
    refine ⟨16712027240765297683349299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22282702987687063577799065 16712027240765297683349299)
    ·
      refine ⟨25068040861147946525023949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16712027240765297683349299 25068040861147946525023949)
      ·
        refine ⟨9400515322930479946883981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25068040861147946525023949 9400515322930479946883981)
        ·
          refine ⟨3525193246098929980081493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9400515322930479946883981 3525193246098929980081493)
          ·
            refine ⟨2581928647045114731505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 3525193246098929980081493 2581928647045114731505)
            ·
              rfl

theorem cell22_610937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 12].length) (baseStart_610937 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_610937 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_610937 prefixEnd_610937 := by exact prefixLift 610937
  have htrace : WordTrace (prefixWord ++ tailWord_610937) baseStart_610937 baseEnd_610937 := by
    simpa [prefixWord, tailWord_610937, baseEnd_610937] using wordTrace_append hprefix tailTrace_610937
  have hstable : (prefixWord ++ tailWord_610937).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_610937).length < 2 ^ (prefixWord ++ tailWord_610937).sum := by decide
  have hdescent : baseEnd_610937 < baseStart_610937 := by decide
  rcases family_descends (prefixWord ++ tailWord_610937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_611076 : List Nat := [2, 3, 2, 2, 1, 1, 2, 3, 1, 5]
def baseStart_611076 : Nat := 118140960795 + 611076 * 2 ^ 59
def prefixEnd_611076 : Nat := 4983230072969 + 3 ^ 40 * 611076 * 2
def baseEnd_611076 : Nat := 209183802951304264026479

theorem tailTrace_611076 : CollatzResearch.WordTrace tailWord_611076 prefixEnd_611076 209183802951304264026479 := by
  unfold tailWord_611076
  simp only [CollatzResearch.WordTrace]
  refine ⟨11143886367091745158554541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14858515156122326878072721 11143886367091745158554541)
  ·
    refine ⟨4178957387659404434457953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11143886367091745158554541 4178957387659404434457953)
    ·
      refine ⟨3134218040744553325843465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4178957387659404434457953 3134218040744553325843465)
      ·
        refine ⟨2350663530558414994382599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3134218040744553325843465 2350663530558414994382599)
        ·
          refine ⟨3525995295837622491573899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2350663530558414994382599 3525995295837622491573899)
          ·
            refine ⟨5288992943756433737360849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3525995295837622491573899 5288992943756433737360849)
            ·
              refine ⟨3966744707817325303020637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5288992943756433737360849 3966744707817325303020637)
              ·
                refine ⟨1487529265431496988632739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3966744707817325303020637 1487529265431496988632739)
                ·
                  refine ⟨2231293898147245482949109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1487529265431496988632739 2231293898147245482949109)
                  ·
                    refine ⟨209183802951304264026479, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2231293898147245482949109 209183802951304264026479)
                    ·
                      rfl

theorem cell22_611076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 2, 3, 1, 5].length) (baseStart_611076 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_611076 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_611076 prefixEnd_611076 := by exact prefixLift 611076
  have htrace : WordTrace (prefixWord ++ tailWord_611076) baseStart_611076 baseEnd_611076 := by
    simpa [prefixWord, tailWord_611076, baseEnd_611076] using wordTrace_append hprefix tailTrace_611076
  have hstable : (prefixWord ++ tailWord_611076).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_611076).length < 2 ^ (prefixWord ++ tailWord_611076).sum := by decide
  have hdescent : baseEnd_611076 < baseStart_611076 := by decide
  rcases family_descends (prefixWord ++ tailWord_611076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_611089 : List Nat := [1, 2, 2, 1, 1, 3, 4, 8]
def baseStart_611089 : Nat := 118140960795 + 611089 * 2 ^ 59
def prefixEnd_611089 : Nat := 4983230072969 + 3 ^ 40 * 611089 * 2
def baseEnd_611089 : Nat := 23243139235219618161271

theorem tailTrace_611089 : CollatzResearch.WordTrace tailWord_611089 prefixEnd_611089 23243139235219618161271 := by
  unfold tailWord_611089
  simp only [CollatzResearch.WordTrace]
  refine ⟨22288246883136393537332321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14858831255424262358221547 22288246883136393537332321)
  ·
    refine ⟨16716185162352295152999241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22288246883136393537332321 16716185162352295152999241)
    ·
      refine ⟨12537138871764221364749431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16716185162352295152999241 12537138871764221364749431)
      ·
        refine ⟨18805708307646332047124147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12537138871764221364749431 18805708307646332047124147)
        ·
          refine ⟨28208562461469498070686221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18805708307646332047124147 28208562461469498070686221)
          ·
            refine ⟨10578210923051061776507333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28208562461469498070686221 10578210923051061776507333)
            ·
              refine ⟨1983414548072074083095125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10578210923051061776507333 1983414548072074083095125)
              ·
                refine ⟨23243139235219618161271, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1983414548072074083095125 23243139235219618161271)
                ·
                  rfl

theorem cell22_611089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 4, 8].length) (baseStart_611089 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_611089 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_611089 prefixEnd_611089 := by exact prefixLift 611089
  have htrace : WordTrace (prefixWord ++ tailWord_611089) baseStart_611089 baseEnd_611089 := by
    simpa [prefixWord, tailWord_611089, baseEnd_611089] using wordTrace_append hprefix tailTrace_611089
  have hstable : (prefixWord ++ tailWord_611089).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_611089).length < 2 ^ (prefixWord ++ tailWord_611089).sum := by decide
  have hdescent : baseEnd_611089 < baseStart_611089 := by decide
  rcases family_descends (prefixWord ++ tailWord_611089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_611091 : List Nat := [1, 1, 1, 2, 1, 3, 6, 1, 2, 4]
def baseStart_611091 : Nat := 118140960795 + 611091 * 2 ^ 59
def prefixEnd_611091 : Nat := 4983230072969 + 3 ^ 40 * 611091 * 2
def baseEnd_611091 : Nat := 209188937757849224901433

theorem tailTrace_611091 : CollatzResearch.WordTrace tailWord_611091 prefixEnd_611091 209188937757849224901433 := by
  unfold tailWord_611091
  simp only [CollatzResearch.WordTrace]
  refine ⟨22288319829129147878905127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14858879886086098585936751 22288319829129147878905127)
  ·
    refine ⟨33432479743693721818357691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22288319829129147878905127 33432479743693721818357691)
    ·
      refine ⟨50148719615540582727536537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33432479743693721818357691 50148719615540582727536537)
      ·
        refine ⟨37611539711655437045652403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50148719615540582727536537 37611539711655437045652403)
        ·
          refine ⟨56417309567483155568478605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37611539711655437045652403 56417309567483155568478605)
          ·
            refine ⟨21156491087806183338179477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 56417309567483155568478605 21156491087806183338179477)
            ·
              refine ⟨991710519740914843977163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 21156491087806183338179477 991710519740914843977163)
              ·
                refine ⟨1487565779611372265965745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 991710519740914843977163 1487565779611372265965745)
                ·
                  refine ⟨1115674334708529199474309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1487565779611372265965745 1115674334708529199474309)
                  ·
                    refine ⟨209188937757849224901433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1115674334708529199474309 209188937757849224901433)
                    ·
                      rfl

theorem cell22_611091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 6, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 6, 1, 2, 4].length) (baseStart_611091 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_611091 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_611091 prefixEnd_611091 := by exact prefixLift 611091
  have htrace : WordTrace (prefixWord ++ tailWord_611091) baseStart_611091 baseEnd_611091 := by
    simpa [prefixWord, tailWord_611091, baseEnd_611091] using wordTrace_append hprefix tailTrace_611091
  have hstable : (prefixWord ++ tailWord_611091).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_611091).length < 2 ^ (prefixWord ++ tailWord_611091).sum := by decide
  have hdescent : baseEnd_611091 < baseStart_611091 := by decide
  rcases family_descends (prefixWord ++ tailWord_611091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_611211 : List Nat := [1, 1, 1, 1, 4, 2, 2, 4, 1, 5]
def baseStart_611211 : Nat := 118140960795 + 611211 * 2 ^ 59
def prefixEnd_611211 : Nat := 4983230072969 + 3 ^ 40 * 611211 * 2
def baseEnd_611211 : Nat := 209230016210208911901065

theorem tailTrace_611211 : CollatzResearch.WordTrace tailWord_611211 prefixEnd_611211 209230016210208911901065 := by
  unfold tailWord_611211
  simp only [CollatzResearch.WordTrace]
  refine ⟨22292696588694408373273487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14861797725796272248848991 22292696588694408373273487)
  ·
    refine ⟨33439044883041612559910231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22292696588694408373273487 33439044883041612559910231)
    ·
      refine ⟨50158567324562418839865347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33439044883041612559910231 50158567324562418839865347)
      ·
        refine ⟨75237850986843628259798021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50158567324562418839865347 75237850986843628259798021)
        ·
          refine ⟨14107097060033180298712129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 75237850986843628259798021 14107097060033180298712129)
          ·
            refine ⟨10580322795024885224034097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14107097060033180298712129 10580322795024885224034097)
            ·
              refine ⟨7935242096268663918025573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10580322795024885224034097 7935242096268663918025573)
              ·
                refine ⟨1487857893050374484629795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7935242096268663918025573 1487857893050374484629795)
                ·
                  refine ⟨2231786839575561726944693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1487857893050374484629795 2231786839575561726944693)
                  ·
                    refine ⟨209230016210208911901065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2231786839575561726944693 209230016210208911901065)
                    ·
                      rfl

theorem cell22_611211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 2, 4, 1, 5].length) (baseStart_611211 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_611211 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_611211 prefixEnd_611211 := by exact prefixLift 611211
  have htrace : WordTrace (prefixWord ++ tailWord_611211) baseStart_611211 baseEnd_611211 := by
    simpa [prefixWord, tailWord_611211, baseEnd_611211] using wordTrace_append hprefix tailTrace_611211
  have hstable : (prefixWord ++ tailWord_611211).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_611211).length < 2 ^ (prefixWord ++ tailWord_611211).sum := by decide
  have hdescent : baseEnd_611211 < baseStart_611211 := by decide
  rcases family_descends (prefixWord ++ tailWord_611211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_611241 : List Nat := [1, 2, 1, 1, 1, 1, 8, 7]
def baseStart_611241 : Nat := 118140960795 + 611241 * 2 ^ 59
def prefixEnd_611241 : Nat := 4983230072969 + 3 ^ 40 * 611241 * 2
def baseEnd_611241 : Nat := 23248920647033203738997

theorem tailTrace_611241 : CollatzResearch.WordTrace tailWord_611241 prefixEnd_611241 23248920647033203738997 := by
  unfold tailWord_611241
  simp only [CollatzResearch.WordTrace]
  refine ⟨22293790778585723496865577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14862527185723815664577051 22293790778585723496865577)
  ·
    refine ⟨16720343083939292622649183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22293790778585723496865577 16720343083939292622649183)
    ·
      refine ⟨25080514625908938933973775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16720343083939292622649183 25080514625908938933973775)
      ·
        refine ⟨37620771938863408400960663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25080514625908938933973775 37620771938863408400960663)
        ·
          refine ⟨56431157908295112601440995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37620771938863408400960663 56431157908295112601440995)
          ·
            refine ⟨84646736862442668902161493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56431157908295112601440995 84646736862442668902161493)
            ·
              refine ⟨991953947606750026197205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 84646736862442668902161493 991953947606750026197205)
              ·
                refine ⟨23248920647033203738997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 991953947606750026197205 23248920647033203738997)
                ·
                  rfl

theorem cell22_611241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 8, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 8, 7].length) (baseStart_611241 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_611241 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_611241 prefixEnd_611241 := by exact prefixLift 611241
  have htrace : WordTrace (prefixWord ++ tailWord_611241) baseStart_611241 baseEnd_611241 := by
    simpa [prefixWord, tailWord_611241, baseEnd_611241] using wordTrace_append hprefix tailTrace_611241
  have hstable : (prefixWord ++ tailWord_611241).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_611241).length < 2 ^ (prefixWord ++ tailWord_611241).sum := by decide
  have hdescent : baseEnd_611241 < baseStart_611241 := by decide
  rcases family_descends (prefixWord ++ tailWord_611241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_611367 : List Nat := [1, 1, 7, 1, 1, 1, 1, 4, 1, 4]
def baseStart_611367 : Nat := 118140960795 + 611367 * 2 ^ 59
def prefixEnd_611367 : Nat := 4983230072969 + 3 ^ 40 * 611367 * 2
def baseEnd_611367 : Nat := 209283418198276505000587

theorem tailTrace_611367 : CollatzResearch.WordTrace tailWord_611367 prefixEnd_611367 209283418198276505000587 := by
  unfold tailWord_611367
  simp only [CollatzResearch.WordTrace]
  refine ⟨22298386376129247015952355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14865590917419498010634903 22298386376129247015952355)
  ·
    refine ⟨33447579564193870523928533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22298386376129247015952355 33447579564193870523928533)
    ·
      refine ⟨783927646035793840404575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 33447579564193870523928533 783927646035793840404575)
      ·
        refine ⟨1175891469053690760606863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 783927646035793840404575 1175891469053690760606863)
        ·
          refine ⟨1763837203580536140910295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1175891469053690760606863 1763837203580536140910295)
          ·
            refine ⟨2645755805370804211365443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1763837203580536140910295 2645755805370804211365443)
            ·
              refine ⟨3968633708056206317048165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2645755805370804211365443 3968633708056206317048165)
              ·
                refine ⟨744118820260538684446531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3968633708056206317048165 744118820260538684446531)
                ·
                  refine ⟨1116178230390808026669797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 744118820260538684446531 1116178230390808026669797)
                  ·
                    refine ⟨209283418198276505000587, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1116178230390808026669797 209283418198276505000587)
                    ·
                      rfl

theorem cell22_611367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 1, 4, 1, 4].length) (baseStart_611367 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_611367 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_611367 prefixEnd_611367 := by exact prefixLift 611367
  have htrace : WordTrace (prefixWord ++ tailWord_611367) baseStart_611367 baseEnd_611367 := by
    simpa [prefixWord, tailWord_611367, baseEnd_611367] using wordTrace_append hprefix tailTrace_611367
  have hstable : (prefixWord ++ tailWord_611367).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_611367).length < 2 ^ (prefixWord ++ tailWord_611367).sum := by decide
  have hdescent : baseEnd_611367 < baseStart_611367 := by decide
  rcases family_descends (prefixWord ++ tailWord_611367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_611378 : List Nat := [3, 2, 1, 1, 2, 2, 1, 3, 1, 6]
def baseStart_611378 : Nat := 118140960795 + 611378 * 2 ^ 59
def prefixEnd_611378 : Nat := 4983230072969 + 3 ^ 40 * 611378 * 2
def baseEnd_611378 : Nat := 209287183723076142975553

theorem tailTrace_611378 : CollatzResearch.WordTrace tailWord_611378 prefixEnd_611378 209287183723076142975553 := by
  unfold tailWord_611378
  simp only [CollatzResearch.WordTrace]
  refine ⟨5574696894772348973650697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14865858386059597263068525 5574696894772348973650697)
  ·
    refine ⟨4181022671079261730238023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5574696894772348973650697 4181022671079261730238023)
    ·
      refine ⟨6271534006618892595357035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4181022671079261730238023 6271534006618892595357035)
      ·
        refine ⟨9407301009928338893035553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6271534006618892595357035 9407301009928338893035553)
        ·
          refine ⟨7055475757446254169776665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9407301009928338893035553 7055475757446254169776665)
          ·
            refine ⟨5291606818084690627332499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7055475757446254169776665 5291606818084690627332499)
            ·
              refine ⟨7937410227127035940998749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5291606818084690627332499 7937410227127035940998749)
              ·
                refine ⟨2976528835172638477874531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7937410227127035940998749 2976528835172638477874531)
                ·
                  refine ⟨4464793252758957716811797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2976528835172638477874531 4464793252758957716811797)
                  ·
                    refine ⟨209287183723076142975553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4464793252758957716811797 209287183723076142975553)
                    ·
                      rfl

theorem cell22_611378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 1, 3, 1, 6].length) (baseStart_611378 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_611378 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_611378 prefixEnd_611378 := by exact prefixLift 611378
  have htrace : WordTrace (prefixWord ++ tailWord_611378) baseStart_611378 baseEnd_611378 := by
    simpa [prefixWord, tailWord_611378, baseEnd_611378] using wordTrace_append hprefix tailTrace_611378
  have hstable : (prefixWord ++ tailWord_611378).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_611378).length < 2 ^ (prefixWord ++ tailWord_611378).sum := by decide
  have hdescent : baseEnd_611378 < baseStart_611378 := by decide
  rcases family_descends (prefixWord ++ tailWord_611378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_611410 : List Nat := [3, 2, 2, 1, 3, 2, 2, 7]
def baseStart_611410 : Nat := 118140960795 + 611410 * 2 ^ 59
def prefixEnd_611410 : Nat := 4983230072969 + 3 ^ 40 * 611410 * 2
def baseEnd_611410 : Nat := 23255348664115414019495

theorem tailTrace_611410 : CollatzResearch.WordTrace tailWord_611410 prefixEnd_611410 23255348664115414019495 := by
  unfold tailWord_611410
  simp only [CollatzResearch.WordTrace]
  refine ⟨5574988678743366339941921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14866636476648976906511789 5574988678743366339941921)
  ·
    refine ⟨4181241509057524754956441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5574988678743366339941921 4181241509057524754956441)
    ·
      refine ⟨3135931131793143566217331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4181241509057524754956441 3135931131793143566217331)
      ·
        refine ⟨4703896697689715349325997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3135931131793143566217331 4703896697689715349325997)
        ·
          refine ⟨1763961261633643255997249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4703896697689715349325997 1763961261633643255997249)
          ·
            refine ⟨1322970946225232441997937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1763961261633643255997249 1322970946225232441997937)
            ·
              refine ⟨992228209668924331498453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1322970946225232441997937 992228209668924331498453)
              ·
                refine ⟨23255348664115414019495, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 992228209668924331498453 23255348664115414019495)
                ·
                  rfl

theorem cell22_611410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 2, 2, 7].length) (baseStart_611410 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_611410 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_611410 prefixEnd_611410 := by exact prefixLift 611410
  have htrace : WordTrace (prefixWord ++ tailWord_611410) baseStart_611410 baseEnd_611410 := by
    simpa [prefixWord, tailWord_611410, baseEnd_611410] using wordTrace_append hprefix tailTrace_611410
  have hstable : (prefixWord ++ tailWord_611410).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_611410).length < 2 ^ (prefixWord ++ tailWord_611410).sum := by decide
  have hdescent : baseEnd_611410 < baseStart_611410 := by decide
  rcases family_descends (prefixWord ++ tailWord_611410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_611425 : List Nat := [1, 2, 3, 1, 1, 2, 2, 4, 3, 3]
def baseStart_611425 : Nat := 118140960795 + 611425 * 2 ^ 59
def prefixEnd_611425 : Nat := 4983230072969 + 3 ^ 40 * 611425 * 2
def baseEnd_611425 : Nat := 209303272783583687050409

theorem tailTrace_611425 : CollatzResearch.WordTrace tailWord_611425 prefixEnd_611425 209303272783583687050409 := by
  unfold tailWord_611425
  simp only [CollatzResearch.WordTrace]
  refine ⟨22300501809919122921563729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14867001206612748614375819 22300501809919122921563729)
  ·
    refine ⟨16725376357439342191172797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22300501809919122921563729 16725376357439342191172797)
    ·
      refine ⟨6272016134039753321689799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16725376357439342191172797 6272016134039753321689799)
      ·
        refine ⟨9408024201059629982534699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6272016134039753321689799 9408024201059629982534699)
        ·
          refine ⟨14112036301589444973802049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9408024201059629982534699 14112036301589444973802049)
          ·
            refine ⟨10584027226192083730351537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14112036301589444973802049 10584027226192083730351537)
            ·
              refine ⟨7938020419644062797763653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10584027226192083730351537 7938020419644062797763653)
              ·
                refine ⟨1488378828683261774580685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7938020419644062797763653 1488378828683261774580685)
                ·
                  refine ⟨558142060756223165467757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1488378828683261774580685 558142060756223165467757)
                  ·
                    refine ⟨209303272783583687050409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 558142060756223165467757 209303272783583687050409)
                    ·
                      rfl

theorem cell22_611425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 2, 4, 3, 3].length) (baseStart_611425 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_611425 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_611425 prefixEnd_611425 := by exact prefixLift 611425
  have htrace : WordTrace (prefixWord ++ tailWord_611425) baseStart_611425 baseEnd_611425 := by
    simpa [prefixWord, tailWord_611425, baseEnd_611425] using wordTrace_append hprefix tailTrace_611425
  have hstable : (prefixWord ++ tailWord_611425).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_611425).length < 2 ^ (prefixWord ++ tailWord_611425).sum := by decide
  have hdescent : baseEnd_611425 < baseStart_611425 := by decide
  rcases family_descends (prefixWord ++ tailWord_611425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_611470 : List Nat := [4, 1, 1, 3, 2, 1, 1, 1, 1, 7]
def baseStart_611470 : Nat := 118140960795 + 611470 * 2 ^ 59
def prefixEnd_611470 : Nat := 4983230072969 + 3 ^ 40 * 611470 * 2
def baseEnd_611470 : Nat := 209318677203218569675271

theorem tailTrace_611470 : CollatzResearch.WordTrace tailWord_611470 prefixEnd_611470 209318677203218569675271 := by
  unfold tailWord_611470
  simp only [CollatzResearch.WordTrace]
  refine ⟨2787767886844511950868983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14868095396504063737967909 2787767886844511950868983)
  ·
    refine ⟨4181651830266767926303475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2787767886844511950868983 4181651830266767926303475)
    ·
      refine ⟨6272477745400151889455213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4181651830266767926303475 6272477745400151889455213)
      ·
        refine ⟨2352179154525056958545705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6272477745400151889455213 2352179154525056958545705)
        ·
          refine ⟨1764134365893792718909279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2352179154525056958545705 1764134365893792718909279)
          ·
            refine ⟨2646201548840689078363919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1764134365893792718909279 2646201548840689078363919)
            ·
              refine ⟨3969302323261033617545879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2646201548840689078363919 3969302323261033617545879)
              ·
                refine ⟨5953953484891550426318819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3969302323261033617545879 5953953484891550426318819)
                ·
                  refine ⟨8930930227337325639478229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5953953484891550426318819 8930930227337325639478229)
                  ·
                    refine ⟨209318677203218569675271, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 8930930227337325639478229 209318677203218569675271)
                    ·
                      rfl

theorem cell22_611470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 1, 1, 1, 7].length) (baseStart_611470 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_611470 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_611470 prefixEnd_611470 := by exact prefixLift 611470
  have htrace : WordTrace (prefixWord ++ tailWord_611470) baseStart_611470 baseEnd_611470 := by
    simpa [prefixWord, tailWord_611470, baseEnd_611470] using wordTrace_append hprefix tailTrace_611470
  have hstable : (prefixWord ++ tailWord_611470).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_611470).length < 2 ^ (prefixWord ++ tailWord_611470).sum := by decide
  have hdescent : baseEnd_611470 < baseStart_611470 := by decide
  rcases family_descends (prefixWord ++ tailWord_611470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_611485 : List Nat := [1, 4, 2, 1, 1, 2, 1, 3, 3, 4]
def baseStart_611485 : Nat := 118140960795 + 611485 * 2 ^ 59
def prefixEnd_611485 : Nat := 4983230072969 + 3 ^ 40 * 611485 * 2
def baseEnd_611485 : Nat := 209323812009763530550225

theorem tailTrace_611485 : CollatzResearch.WordTrace tailWord_611485 prefixEnd_611485 209323812009763530550225 := by
  unfold tailWord_611485
  simp only [CollatzResearch.WordTrace]
  refine ⟨22302690189701753168747909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14868460126467835445831939 22302690189701753168747909)
  ·
    refine ⟨4181754410569078719140233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 22302690189701753168747909 4181754410569078719140233)
    ·
      refine ⟨3136315807926809039355175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4181754410569078719140233 3136315807926809039355175)
      ·
        refine ⟨4704473711890213559032763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3136315807926809039355175 4704473711890213559032763)
        ·
          refine ⟨7056710567835320338549145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4704473711890213559032763 7056710567835320338549145)
          ·
            refine ⟨5292532925876490253911859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7056710567835320338549145 5292532925876490253911859)
            ·
              refine ⟨7938799388814735380867789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5292532925876490253911859 7938799388814735380867789)
              ·
                refine ⟨2977049770805525767825421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7938799388814735380867789 2977049770805525767825421)
                ·
                  refine ⟨1116393664052072162934533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2977049770805525767825421 1116393664052072162934533)
                  ·
                    refine ⟨209323812009763530550225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1116393664052072162934533 209323812009763530550225)
                    ·
                      rfl

theorem cell22_611485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 1, 3, 3, 4].length) (baseStart_611485 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_611485 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_611485 prefixEnd_611485 := by exact prefixLift 611485
  have htrace : WordTrace (prefixWord ++ tailWord_611485) baseStart_611485 baseEnd_611485 := by
    simpa [prefixWord, tailWord_611485, baseEnd_611485] using wordTrace_append hprefix tailTrace_611485
  have hstable : (prefixWord ++ tailWord_611485).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_611485).length < 2 ^ (prefixWord ++ tailWord_611485).sum := by decide
  have hdescent : baseEnd_611485 < baseStart_611485 := by decide
  rcases family_descends (prefixWord ++ tailWord_611485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_611517 : List Nat := [1, 4, 1, 2, 1, 1, 4, 4, 4]
def baseStart_611517 : Nat := 118140960795 + 611517 * 2 ^ 59
def prefixEnd_611517 : Nat := 4983230072969 + 3 ^ 40 * 611517 * 2
def baseEnd_611517 : Nat := 69778255421242037916709

theorem tailTrace_611517 : CollatzResearch.WordTrace tailWord_611517 prefixEnd_611517 69778255421242037916709 := by
  unfold tailWord_611517
  simp only [CollatzResearch.WordTrace]
  refine ⟨22303857325585822633912805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14869238217057215089275203 22303857325585822633912805)
  ·
    refine ⟨4181973248547341743858651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 22303857325585822633912805 4181973248547341743858651)
    ·
      refine ⟨6272959872821012615787977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4181973248547341743858651 6272959872821012615787977)
      ·
        refine ⟨4704719904615759461840983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6272959872821012615787977 4704719904615759461840983)
        ·
          refine ⟨7057079856923639192761475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4704719904615759461840983 7057079856923639192761475)
          ·
            refine ⟨10585619785385458789142213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7057079856923639192761475 10585619785385458789142213)
            ·
              refine ⟨1984803709759773522964165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10585619785385458789142213 1984803709759773522964165)
              ·
                refine ⟨372150695579957535555781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1984803709759773522964165 372150695579957535555781)
                ·
                  refine ⟨69778255421242037916709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 372150695579957535555781 69778255421242037916709)
                  ·
                    rfl

theorem cell22_611517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 4, 4, 4].length) (baseStart_611517 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_611517 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_611517 prefixEnd_611517 := by exact prefixLift 611517
  have htrace : WordTrace (prefixWord ++ tailWord_611517) baseStart_611517 baseEnd_611517 := by
    simpa [prefixWord, tailWord_611517, baseEnd_611517] using wordTrace_append hprefix tailTrace_611517
  have hstable : (prefixWord ++ tailWord_611517).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_611517).length < 2 ^ (prefixWord ++ tailWord_611517).sum := by decide
  have hdescent : baseEnd_611517 < baseStart_611517 := by decide
  rcases family_descends (prefixWord ++ tailWord_611517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_611530 : List Nat := [3, 1, 2, 1, 3, 2, 1, 2, 1, 6]
def baseStart_611530 : Nat := 118140960795 + 611530 * 2 ^ 59
def prefixEnd_611530 : Nat := 4983230072969 + 3 ^ 40 * 611530 * 2
def baseEnd_611530 : Nat := 209339216429398413175087

theorem tailTrace_611530 : CollatzResearch.WordTrace tailWord_611530 prefixEnd_611530 209339216429398413175087 := by
  unfold tailWord_611530
  simp only [CollatzResearch.WordTrace]
  refine ⟨5576082868634681463534011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14869554316359150569424029 5576082868634681463534011)
  ·
    refine ⟨8364124302952022195301017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5576082868634681463534011 8364124302952022195301017)
    ·
      refine ⟨6273093227214016646475763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8364124302952022195301017 6273093227214016646475763)
      ·
        refine ⟨9409639840821024969713645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6273093227214016646475763 9409639840821024969713645)
        ·
          refine ⟨3528614940307884363642617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9409639840821024969713645 3528614940307884363642617)
          ·
            refine ⟨2646461205230913272731963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3528614940307884363642617 2646461205230913272731963)
            ·
              refine ⟨3969691807846369909097945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2646461205230913272731963 3969691807846369909097945)
              ·
                refine ⟨2977268855884777431823459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3969691807846369909097945 2977268855884777431823459)
                ·
                  refine ⟨4465903283827166147735189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2977268855884777431823459 4465903283827166147735189)
                  ·
                    refine ⟨209339216429398413175087, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4465903283827166147735189 209339216429398413175087)
                    ·
                      rfl

theorem cell22_611530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 1, 2, 1, 6].length) (baseStart_611530 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_611530 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_611530 prefixEnd_611530 := by exact prefixLift 611530
  have htrace : WordTrace (prefixWord ++ tailWord_611530) baseStart_611530 baseEnd_611530 := by
    simpa [prefixWord, tailWord_611530, baseEnd_611530] using wordTrace_append hprefix tailTrace_611530
  have hstable : (prefixWord ++ tailWord_611530).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_611530).length < 2 ^ (prefixWord ++ tailWord_611530).sum := by decide
  have hdescent : baseEnd_611530 < baseStart_611530 := by decide
  rcases family_descends (prefixWord ++ tailWord_611530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_611605 : List Nat := [1, 3, 2, 1, 2, 1, 1, 2, 4, 5]
def baseStart_611605 : Nat := 118140960795 + 611605 * 2 ^ 59
def prefixEnd_611605 : Nat := 4983230072969 + 3 ^ 40 * 611605 * 2
def baseEnd_611605 : Nat := 209364890462123217549857

theorem tailTrace_611605 : CollatzResearch.WordTrace tailWord_611605 prefixEnd_611605 209364890462123217549857 := by
  unfold tailWord_611605
  simp only [CollatzResearch.WordTrace]
  refine ⟨22307066949267013663116269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14871377966178009108744179 22307066949267013663116269)
  ·
    refine ⟨8365150105975130123668601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22307066949267013663116269 8365150105975130123668601)
    ·
      refine ⟨6273862579481347592751451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8365150105975130123668601 6273862579481347592751451)
      ·
        refine ⟨9410793869222021389127177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6273862579481347592751451 9410793869222021389127177)
        ·
          refine ⟨7058095401916516041845383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9410793869222021389127177 7058095401916516041845383)
          ·
            refine ⟨10587143102874774062768075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7058095401916516041845383 10587143102874774062768075)
            ·
              refine ⟨15880714654312161094152113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10587143102874774062768075 15880714654312161094152113)
              ·
                refine ⟨11910535990734120820614085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15880714654312161094152113 11910535990734120820614085)
                ·
                  refine ⟨2233225498262647653865141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11910535990734120820614085 2233225498262647653865141)
                  ·
                    refine ⟨209364890462123217549857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2233225498262647653865141 209364890462123217549857)
                    ·
                      rfl

theorem cell22_611605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 2, 4, 5].length) (baseStart_611605 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_611605 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_611605 prefixEnd_611605 := by exact prefixLift 611605
  have htrace : WordTrace (prefixWord ++ tailWord_611605) baseStart_611605 baseEnd_611605 := by
    simpa [prefixWord, tailWord_611605, baseEnd_611605] using wordTrace_append hprefix tailTrace_611605
  have hstable : (prefixWord ++ tailWord_611605).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_611605).length < 2 ^ (prefixWord ++ tailWord_611605).sum := by decide
  have hdescent : baseEnd_611605 < baseStart_611605 := by decide
  rcases family_descends (prefixWord ++ tailWord_611605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_611624 : List Nat := [2, 1, 5, 1, 2, 2, 2, 2, 5]
def baseStart_611624 : Nat := 118140960795 + 611624 * 2 ^ 59
def prefixEnd_611624 : Nat := 4983230072969 + 3 ^ 40 * 611624 * 2
def baseEnd_611624 : Nat := 69790464850137833774933

theorem tailTrace_611624 : CollatzResearch.WordTrace tailWord_611624 prefixEnd_611624 69790464850137833774933 := by
  unfold tailWord_611624
  simp only [CollatzResearch.WordTrace]
  refine ⟨11153879968099089954028963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14871839957465453272038617 11153879968099089954028963)
  ·
    refine ⟨16730819952148634931043445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11153879968099089954028963 16730819952148634931043445)
    ·
      refine ⟨1568514370513934524785323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 16730819952148634931043445 1568514370513934524785323)
      ·
        refine ⟨2352771555770901787177985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1568514370513934524785323 2352771555770901787177985)
        ·
          refine ⟨1764578666828176340383489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2352771555770901787177985 1764578666828176340383489)
          ·
            refine ⟨1323434000121132255287617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1764578666828176340383489 1323434000121132255287617)
            ·
              refine ⟨992575500090849191465713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1323434000121132255287617 992575500090849191465713)
              ·
                refine ⟨744431625068136893599285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 992575500090849191465713 744431625068136893599285)
                ·
                  refine ⟨69790464850137833774933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 744431625068136893599285 69790464850137833774933)
                  ·
                    rfl

theorem cell22_611624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 2, 2, 2, 5].length) (baseStart_611624 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_611624 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_611624 prefixEnd_611624 := by exact prefixLift 611624
  have htrace : WordTrace (prefixWord ++ tailWord_611624) baseStart_611624 baseEnd_611624 := by
    simpa [prefixWord, tailWord_611624, baseEnd_611624] using wordTrace_append hprefix tailTrace_611624
  have hstable : (prefixWord ++ tailWord_611624).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_611624).length < 2 ^ (prefixWord ++ tailWord_611624).sum := by decide
  have hdescent : baseEnd_611624 < baseStart_611624 := by decide
  rcases family_descends (prefixWord ++ tailWord_611624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_611637 : List Nat := [1, 3, 3, 1, 2, 2, 1, 2, 3, 4]
def baseStart_611637 : Nat := 118140960795 + 611637 * 2 ^ 59
def prefixEnd_611637 : Nat := 4983230072969 + 3 ^ 40 * 611637 * 2
def baseEnd_611637 : Nat := 209375844716085800749759

theorem tailTrace_611637 : CollatzResearch.WordTrace tailWord_611637 prefixEnd_611637 209375844716085800749759 := by
  unfold tailWord_611637
  simp only [CollatzResearch.WordTrace]
  refine ⟨22308234085151083128281165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14872156056767388752187443 22308234085151083128281165)
  ·
    refine ⟨8365587781931656173105437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22308234085151083128281165 8365587781931656173105437)
    ·
      refine ⟨3137095418224371064914539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8365587781931656173105437 3137095418224371064914539)
      ·
        refine ⟨4705643127336556597371809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3137095418224371064914539 4705643127336556597371809)
        ·
          refine ⟨3529232345502417448028857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4705643127336556597371809 3529232345502417448028857)
          ·
            refine ⟨2646924259126813086021643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3529232345502417448028857 2646924259126813086021643)
            ·
              refine ⟨3970386388690219629032465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2646924259126813086021643 3970386388690219629032465)
              ·
                refine ⟨2977789791517664721774349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3970386388690219629032465 2977789791517664721774349)
                ·
                  refine ⟨1116671171819124270665381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2977789791517664721774349 1116671171819124270665381)
                  ·
                    refine ⟨209375844716085800749759, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1116671171819124270665381 209375844716085800749759)
                    ·
                      rfl

theorem cell22_611637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 1, 2, 3, 4].length) (baseStart_611637 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_611637 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_611637 prefixEnd_611637 := by exact prefixLift 611637
  have htrace : WordTrace (prefixWord ++ tailWord_611637) baseStart_611637 baseEnd_611637 := by
    simpa [prefixWord, tailWord_611637, baseEnd_611637] using wordTrace_append hprefix tailTrace_611637
  have hstable : (prefixWord ++ tailWord_611637).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_611637).length < 2 ^ (prefixWord ++ tailWord_611637).sum := by decide
  have hdescent : baseEnd_611637 < baseStart_611637 := by decide
  rcases family_descends (prefixWord ++ tailWord_611637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_611667 : List Nat := [1, 1, 1, 2, 1, 1, 6, 2, 4, 3]
def baseStart_611667 : Nat := 118140960795 + 611667 * 2 ^ 59
def prefixEnd_611667 : Nat := 4983230072969 + 3 ^ 40 * 611667 * 2
def baseEnd_611667 : Nat := 209386114329175722499667

theorem tailTrace_611667 : CollatzResearch.WordTrace tailWord_611667 prefixEnd_611667 209386114329175722499667 := by
  unfold tailWord_611667
  simp only [CollatzResearch.WordTrace]
  refine ⟨22309328275042398251873255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14872885516694932167915503 22309328275042398251873255)
  ·
    refine ⟨33463992412563597377809883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22309328275042398251873255 33463992412563597377809883)
    ·
      refine ⟨50195988618845396066714825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33463992412563597377809883 50195988618845396066714825)
      ·
        refine ⟨37646991464134047050036119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50195988618845396066714825 37646991464134047050036119)
        ·
          refine ⟨56470487196201070575054179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37646991464134047050036119 56470487196201070575054179)
          ·
            refine ⟨84705730794301605862581269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56470487196201070575054179 84705730794301605862581269)
            ·
              refine ⟨3970581130982887774808497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 84705730794301605862581269 3970581130982887774808497)
              ·
                refine ⟨2977935848237165831106373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3970581130982887774808497 2977935848237165831106373)
                ·
                  refine ⟨558362971544468593332445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2977935848237165831106373 558362971544468593332445)
                  ·
                    refine ⟨209386114329175722499667, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 558362971544468593332445 209386114329175722499667)
                    ·
                      rfl

theorem cell22_611667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 6, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 6, 2, 4, 3].length) (baseStart_611667 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_611667 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_611667 prefixEnd_611667 := by exact prefixLift 611667
  have htrace : WordTrace (prefixWord ++ tailWord_611667) baseStart_611667 baseEnd_611667 := by
    simpa [prefixWord, tailWord_611667, baseEnd_611667] using wordTrace_append hprefix tailTrace_611667
  have hstable : (prefixWord ++ tailWord_611667).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_611667).length < 2 ^ (prefixWord ++ tailWord_611667).sum := by decide
  have hdescent : baseEnd_611667 < baseStart_611667 := by decide
  rcases family_descends (prefixWord ++ tailWord_611667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_611669 : List Nat := [1, 3, 2, 2, 3, 1, 1, 5, 4]
def baseStart_611669 : Nat := 118140960795 + 611669 * 2 ^ 59
def prefixEnd_611669 : Nat := 4983230072969 + 3 ^ 40 * 611669 * 2
def baseEnd_611669 : Nat := 69795599656682794649887

theorem tailTrace_611669 : CollatzResearch.WordTrace tailWord_611669 prefixEnd_611669 69795599656682794649887 := by
  unfold tailWord_611669
  simp only [CollatzResearch.WordTrace]
  refine ⟨22309401221035152593446061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14872934147356768395630707 22309401221035152593446061)
  ·
    refine ⟨8366025457888182222542273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22309401221035152593446061 8366025457888182222542273)
    ·
      refine ⟨6274519093416136666906705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8366025457888182222542273 6274519093416136666906705)
      ·
        refine ⟨4705889320062102500180029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6274519093416136666906705 4705889320062102500180029)
        ·
          refine ⟨1764708495023288437567511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4705889320062102500180029 1764708495023288437567511)
          ·
            refine ⟨2647062742534932656351267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1764708495023288437567511 2647062742534932656351267)
            ·
              refine ⟨3970594113802398984526901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2647062742534932656351267 3970594113802398984526901)
              ·
                refine ⟨372243198168974904799397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3970594113802398984526901 372243198168974904799397)
                ·
                  refine ⟨69795599656682794649887, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 372243198168974904799397 69795599656682794649887)
                  ·
                    rfl

theorem cell22_611669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 1, 5, 4].length) (baseStart_611669 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_611669 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_611669 prefixEnd_611669 := by exact prefixLift 611669
  have htrace : WordTrace (prefixWord ++ tailWord_611669) baseStart_611669 baseEnd_611669 := by
    simpa [prefixWord, tailWord_611669, baseEnd_611669] using wordTrace_append hprefix tailTrace_611669
  have hstable : (prefixWord ++ tailWord_611669).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_611669).length < 2 ^ (prefixWord ++ tailWord_611669).sum := by decide
  have hdescent : baseEnd_611669 < baseStart_611669 := by decide
  rcases family_descends (prefixWord ++ tailWord_611669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_611671 : List Nat := [1, 1, 3, 2, 3, 4, 2, 1, 1, 4]
def baseStart_611671 : Nat := 118140960795 + 611671 * 2 ^ 59
def prefixEnd_611671 : Nat := 4983230072969 + 3 ^ 40 * 611671 * 2
def baseEnd_611671 : Nat := 209387483610921045399655

theorem tailTrace_611671 : CollatzResearch.WordTrace tailWord_611671 prefixEnd_611671 209387483610921045399655 := by
  unfold tailWord_611671
  simp only [CollatzResearch.WordTrace]
  refine ⟨22309474167027906935018867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14872982778018604623345911 22309474167027906935018867)
  ·
    refine ⟨33464211250541860402528301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22309474167027906935018867 33464211250541860402528301)
    ·
      refine ⟨12549079218953197650948113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33464211250541860402528301 12549079218953197650948113)
      ·
        refine ⟨9411809414214898238211085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12549079218953197650948113 9411809414214898238211085)
        ·
          refine ⟨3529428530330586839329157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9411809414214898238211085 3529428530330586839329157)
          ·
            refine ⟨661767849436985032374217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3529428530330586839329157 661767849436985032374217)
            ·
              refine ⟨496325887077738774280663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 661767849436985032374217 496325887077738774280663)
              ·
                refine ⟨744488830616608161420995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 496325887077738774280663 744488830616608161420995)
                ·
                  refine ⟨1116733245924912242131493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 744488830616608161420995 1116733245924912242131493)
                  ·
                    refine ⟨209387483610921045399655, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1116733245924912242131493 209387483610921045399655)
                    ·
                      rfl

theorem cell22_611671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 4, 2, 1, 1, 4].length) (baseStart_611671 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_611671 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_611671 prefixEnd_611671 := by exact prefixLift 611671
  have htrace : WordTrace (prefixWord ++ tailWord_611671) baseStart_611671 baseEnd_611671 := by
    simpa [prefixWord, tailWord_611671, baseEnd_611671] using wordTrace_append hprefix tailTrace_611671
  have hstable : (prefixWord ++ tailWord_611671).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_611671).length < 2 ^ (prefixWord ++ tailWord_611671).sum := by decide
  have hdescent : baseEnd_611671 < baseStart_611671 := by decide
  rcases family_descends (prefixWord ++ tailWord_611671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_611684 : List Nat := [2, 3, 1, 1, 3, 3, 1, 1, 4, 3]
def baseStart_611684 : Nat := 118140960795 + 611684 * 2 ^ 59
def prefixEnd_611684 : Nat := 4983230072969 + 3 ^ 40 * 611684 * 2
def baseEnd_611684 : Nat := 209391933776593344824615

theorem tailTrace_611684 : CollatzResearch.WordTrace tailWord_611684 prefixEnd_611684 209391933776593344824615 := by
  unfold tailWord_611684
  simp only [CollatzResearch.WordTrace]
  refine ⟨11154974157990405077621053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14873298877320540103494737 11154974157990405077621053)
  ·
    refine ⟨4183115309246401904107895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11154974157990405077621053 4183115309246401904107895)
    ·
      refine ⟨6274672963869602856161843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4183115309246401904107895 6274672963869602856161843)
      ·
        refine ⟨9412009445804404284242765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6274672963869602856161843 9412009445804404284242765)
        ·
          refine ⟨3529503542176651606591037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9412009445804404284242765 3529503542176651606591037)
          ·
            refine ⟨1323563828316244352471639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3529503542176651606591037 1323563828316244352471639)
            ·
              refine ⟨1985345742474366528707459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1323563828316244352471639 1985345742474366528707459)
              ·
                refine ⟨2978018613711549793061189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1985345742474366528707459 2978018613711549793061189)
                ·
                  refine ⟨558378490070915586198973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2978018613711549793061189 558378490070915586198973)
                  ·
                    refine ⟨209391933776593344824615, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 558378490070915586198973 209391933776593344824615)
                    ·
                      rfl

theorem cell22_611684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 3, 1, 1, 4, 3].length) (baseStart_611684 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_611684 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_611684 prefixEnd_611684 := by exact prefixLift 611684
  have htrace : WordTrace (prefixWord ++ tailWord_611684) baseStart_611684 baseEnd_611684 := by
    simpa [prefixWord, tailWord_611684, baseEnd_611684] using wordTrace_append hprefix tailTrace_611684
  have hstable : (prefixWord ++ tailWord_611684).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_611684).length < 2 ^ (prefixWord ++ tailWord_611684).sum := by decide
  have hdescent : baseEnd_611684 < baseStart_611684 := by decide
  rcases family_descends (prefixWord ++ tailWord_611684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_611701 : List Nat := [1, 3, 4, 1, 3, 2, 1, 1, 1, 5]
def baseStart_611701 : Nat := 118140960795 + 611701 * 2 ^ 59
def prefixEnd_611701 : Nat := 4983230072969 + 3 ^ 40 * 611701 * 2
def baseEnd_611701 : Nat := 209397753224010967149563

theorem tailTrace_611701 : CollatzResearch.WordTrace tailWord_611701 prefixEnd_611701 209397753224010967149563 := by
  unfold tailWord_611701
  simp only [CollatzResearch.WordTrace]
  refine ⟨22310568356919222058610957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14873712237946148039073971 22310568356919222058610957)
  ·
    refine ⟨8366463133844708271979109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22310568356919222058610957 8366463133844708271979109)
    ·
      refine ⟨1568711837595882800996083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8366463133844708271979109 1568711837595882800996083)
      ·
        refine ⟨2353067756393824201494125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1568711837595882800996083 2353067756393824201494125)
        ·
          refine ⟨882400408647684075560297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2353067756393824201494125 882400408647684075560297)
          ·
            refine ⟨661800306485763056670223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 882400408647684075560297 661800306485763056670223)
            ·
              refine ⟨992700459728644585005335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 661800306485763056670223 992700459728644585005335)
              ·
                refine ⟨1489050689592966877508003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 992700459728644585005335 1489050689592966877508003)
                ·
                  refine ⟨2233576034389450316262005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1489050689592966877508003 2233576034389450316262005)
                  ·
                    refine ⟨209397753224010967149563, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2233576034389450316262005 209397753224010967149563)
                    ·
                      rfl

theorem cell22_611701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 2, 1, 1, 1, 5].length) (baseStart_611701 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_611701 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_611701 prefixEnd_611701 := by exact prefixLift 611701
  have htrace : WordTrace (prefixWord ++ tailWord_611701) baseStart_611701 baseEnd_611701 := by
    simpa [prefixWord, tailWord_611701, baseEnd_611701] using wordTrace_append hprefix tailTrace_611701
  have hstable : (prefixWord ++ tailWord_611701).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_611701).length < 2 ^ (prefixWord ++ tailWord_611701).sum := by decide
  have hdescent : baseEnd_611701 < baseStart_611701 := by decide
  rcases family_descends (prefixWord ++ tailWord_611701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_611746 : List Nat := [3, 3, 1, 2, 1, 2, 3, 1, 3, 3]
def baseStart_611746 : Nat := 118140960795 + 611746 * 2 ^ 59
def prefixEnd_611746 : Nat := 4983230072969 + 3 ^ 40 * 611746 * 2
def baseEnd_611746 : Nat := 209413157643645849774425

theorem tailTrace_611746 : CollatzResearch.WordTrace tailWord_611746 prefixEnd_611746 209413157643645849774425 := by
  unfold tailWord_611746
  simp only [CollatzResearch.WordTrace]
  refine ⟨5578052410439048685999773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14874806427837463162666061 5578052410439048685999773)
  ·
    refine ⟨2091769653914643257249915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5578052410439048685999773 2091769653914643257249915)
    ·
      refine ⟨3137654480871964885874873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2091769653914643257249915 3137654480871964885874873)
      ·
        refine ⟨2353240860653973664406155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3137654480871964885874873 2353240860653973664406155)
        ·
          refine ⟨3529861290980960496609233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2353240860653973664406155 3529861290980960496609233)
          ·
            refine ⟨2647395968235720372456925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3529861290980960496609233 2647395968235720372456925)
            ·
              refine ⟨992773488088395139671347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2647395968235720372456925 992773488088395139671347)
              ·
                refine ⟨1489160232132592709507021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 992773488088395139671347 1489160232132592709507021)
                ·
                  refine ⟨558435087049722266065133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1489160232132592709507021 558435087049722266065133)
                  ·
                    refine ⟨209413157643645849774425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 558435087049722266065133 209413157643645849774425)
                    ·
                      rfl

theorem cell22_611746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 3, 1, 3, 3].length) (baseStart_611746 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_611746 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_611746 prefixEnd_611746 := by exact prefixLift 611746
  have htrace : WordTrace (prefixWord ++ tailWord_611746) baseStart_611746 baseEnd_611746 := by
    simpa [prefixWord, tailWord_611746, baseEnd_611746] using wordTrace_append hprefix tailTrace_611746
  have hstable : (prefixWord ++ tailWord_611746).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_611746).length < 2 ^ (prefixWord ++ tailWord_611746).sum := by decide
  have hdescent : baseEnd_611746 < baseStart_611746 := by decide
  rcases family_descends (prefixWord ++ tailWord_611746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_611752 : List Nat := [2, 1, 6, 1, 3, 1, 2, 1, 2, 3]
def baseStart_611752 : Nat := 118140960795 + 611752 * 2 ^ 59
def prefixEnd_611752 : Nat := 4983230072969 + 3 ^ 40 * 611752 * 2
def baseEnd_611752 : Nat := 209415211566263834124407

theorem tailTrace_611752 : CollatzResearch.WordTrace tailWord_611752 prefixEnd_611752 209415211566263834124407 := by
  unfold tailWord_611752
  simp only [CollatzResearch.WordTrace]
  refine ⟨11156214239867228884358755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14874952319822971845811673 11156214239867228884358755)
  ·
    refine ⟨16734321359800843326538133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11156214239867228884358755 16734321359800843326538133)
    ·
      refine ⟨784421313740664530931475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 16734321359800843326538133 784421313740664530931475)
      ·
        refine ⟨1176631970610996796397213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 784421313740664530931475 1176631970610996796397213)
        ·
          refine ⟨441236988979123798648955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1176631970610996796397213 441236988979123798648955)
          ·
            refine ⟨661855483468685697973433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 441236988979123798648955 661855483468685697973433)
            ·
              refine ⟨496391612601514273480075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 661855483468685697973433 496391612601514273480075)
              ·
                refine ⟨744587418902271410220113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 496391612601514273480075 744587418902271410220113)
                ·
                  refine ⟨558440564176703557665085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 744587418902271410220113 558440564176703557665085)
                  ·
                    refine ⟨209415211566263834124407, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 558440564176703557665085 209415211566263834124407)
                    ·
                      rfl

theorem cell22_611752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 3, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 3, 1, 2, 1, 2, 3].length) (baseStart_611752 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_611752 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_611752 prefixEnd_611752 := by exact prefixLift 611752
  have htrace : WordTrace (prefixWord ++ tailWord_611752) baseStart_611752 baseEnd_611752 := by
    simpa [prefixWord, tailWord_611752, baseEnd_611752] using wordTrace_append hprefix tailTrace_611752
  have hstable : (prefixWord ++ tailWord_611752).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_611752).length < 2 ^ (prefixWord ++ tailWord_611752).sum := by decide
  have hdescent : baseEnd_611752 < baseStart_611752 := by decide
  rcases family_descends (prefixWord ++ tailWord_611752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
