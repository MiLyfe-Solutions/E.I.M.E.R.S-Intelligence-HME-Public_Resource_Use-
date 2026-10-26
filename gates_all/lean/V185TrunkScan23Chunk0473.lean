import V185TrunkScan23Chunk0472

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_2797361 : List Nat := [1, 2, 2, 3, 2, 2, 2, 1, 4, 1, 3]
def baseStart_2797361 : Nat := 118140960795 + 2797361 * 2 ^ 59
def prefixEnd_2797361 : Nat := 4983230072969 + 3 ^ 40 * 2797361 * 2
def baseEnd_2797361 : Nat := 1436390757141935045922677

theorem tailTrace_2797361 : CollatzResearch.WordTrace tailWord_2797361 prefixEnd_2797361 1436390757141935045922677 := by
  unfold tailWord_2797361
  simp only [CollatzResearch.WordTrace]
  refine ⟨102028137618646323068191937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68018758412430882045461291 102028137618646323068191937)
  ·
    refine ⟨76521103213984742301143953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102028137618646323068191937 76521103213984742301143953)
    ·
      refine ⟨57390827410488556725857965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76521103213984742301143953 57390827410488556725857965)
      ·
        refine ⟨21521560278933208772196737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 57390827410488556725857965 21521560278933208772196737)
        ·
          refine ⟨16141170209199906579147553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21521560278933208772196737 16141170209199906579147553)
          ·
            refine ⟨12105877656899929934360665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16141170209199906579147553 12105877656899929934360665)
            ·
              refine ⟨9079408242674947450770499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12105877656899929934360665 9079408242674947450770499)
              ·
                refine ⟨13619112364012421176155749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9079408242674947450770499 13619112364012421176155749)
                ·
                  refine ⟨2553583568252328970529203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13619112364012421176155749 2553583568252328970529203)
                  ·
                    refine ⟨3830375352378493455793805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2553583568252328970529203 3830375352378493455793805)
                    ·
                      refine ⟨1436390757141935045922677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3830375352378493455793805 1436390757141935045922677)
                      ·
                        rfl

theorem cell23_2797361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 2, 1, 4, 1, 3].length) (baseStart_2797361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2797361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2797361 prefixEnd_2797361 := by exact prefixLift 2797361
  have htrace : WordTrace (prefixWord ++ tailWord_2797361) baseStart_2797361 baseEnd_2797361 := by
    simpa [prefixWord, tailWord_2797361, baseEnd_2797361] using wordTrace_append hprefix tailTrace_2797361
  have hstable : (prefixWord ++ tailWord_2797361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2797361).length < 2 ^ (prefixWord ++ tailWord_2797361).sum := by decide
  have hdescent : baseEnd_2797361 < baseStart_2797361 := by decide
  rcases family_descends (prefixWord ++ tailWord_2797361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2797362 : List Nat := [3, 2, 1, 1, 3, 3, 3, 2, 1, 2, 2]
def baseStart_2797362 : Nat := 118140960795 + 2797362 * 2 ^ 59
def prefixEnd_2797362 : Nat := 4983230072969 + 3 ^ 40 * 2797362 * 2
def baseEnd_2797362 : Nat := 1436391270622589542010173

theorem tailTrace_2797362 : CollatzResearch.WordTrace tailWord_2797362 prefixEnd_2797362 1436391270622589542010173 := by
  unfold tailWord_2797362
  simp only [CollatzResearch.WordTrace]
  refine ⟨25507043522910675059744585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68018782727761800159318893 25507043522910675059744585)
  ·
    refine ⟨19130282642183006294808439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25507043522910675059744585 19130282642183006294808439)
    ·
      refine ⟨28695423963274509442212659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19130282642183006294808439 28695423963274509442212659)
      ·
        refine ⟨43043135944911764163318989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28695423963274509442212659 43043135944911764163318989)
        ·
          refine ⟨16141175979341911561244621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43043135944911764163318989 16141175979341911561244621)
          ·
            refine ⟨6052940992253216835466733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16141175979341911561244621 6052940992253216835466733)
            ·
              refine ⟨2269852872094956313300025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6052940992253216835466733 2269852872094956313300025)
              ·
                refine ⟨1702389654071217234975019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2269852872094956313300025 1702389654071217234975019)
                ·
                  refine ⟨2553584481106825852462529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1702389654071217234975019 2553584481106825852462529)
                  ·
                    refine ⟨1915188360830119389346897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2553584481106825852462529 1915188360830119389346897)
                    ·
                      refine ⟨1436391270622589542010173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1915188360830119389346897 1436391270622589542010173)
                      ·
                        rfl

theorem cell23_2797362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 3, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 3, 3, 2, 1, 2, 2].length) (baseStart_2797362 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2797362 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2797362 prefixEnd_2797362 := by exact prefixLift 2797362
  have htrace : WordTrace (prefixWord ++ tailWord_2797362) baseStart_2797362 baseEnd_2797362 := by
    simpa [prefixWord, tailWord_2797362, baseEnd_2797362] using wordTrace_append hprefix tailTrace_2797362
  have hstable : (prefixWord ++ tailWord_2797362).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2797362).length < 2 ^ (prefixWord ++ tailWord_2797362).sum := by decide
  have hdescent : baseEnd_2797362 < baseStart_2797362 := by decide
  rcases family_descends (prefixWord ++ tailWord_2797362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2797382 : List Nat := [6, 1, 1, 2, 1, 3, 1, 2, 1, 2, 3]
def baseStart_2797382 : Nat := 118140960795 + 2797382 * 2 ^ 59
def prefixEnd_2797382 : Nat := 4983230072969 + 3 ^ 40 * 2797382 * 2
def baseEnd_2797382 : Nat := 1436401540235679463760081

theorem tailTrace_2797382 : CollatzResearch.WordTrace tailWord_2797382 prefixEnd_2797382 1436401540235679463760081 := by
  unfold tailWord_2797382
  simp only [CollatzResearch.WordTrace]
  refine ⟨3188403235986570114209575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 68019269034380162436470933 3188403235986570114209575)
  ·
    refine ⟨4782604853979855171314363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3188403235986570114209575 4782604853979855171314363)
    ·
      refine ⟨7173907280969782756971545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4782604853979855171314363 7173907280969782756971545)
      ·
        refine ⟨5380430460727337067728659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7173907280969782756971545 5380430460727337067728659)
        ·
          refine ⟨8070645691091005601592989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5380430460727337067728659 8070645691091005601592989)
          ·
            refine ⟨3026492134159127100597371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8070645691091005601592989 3026492134159127100597371)
            ·
              refine ⟨4539738201238690650896057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3026492134159127100597371 4539738201238690650896057)
              ·
                refine ⟨3404803650929017988172043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4539738201238690650896057 3404803650929017988172043)
                ·
                  refine ⟨5107205476393526982258065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3404803650929017988172043 5107205476393526982258065)
                  ·
                    refine ⟨3830404107295145236693549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5107205476393526982258065 3830404107295145236693549)
                    ·
                      refine ⟨1436401540235679463760081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3830404107295145236693549 1436401540235679463760081)
                      ·
                        rfl

theorem cell23_2797382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 3, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 3, 1, 2, 1, 2, 3].length) (baseStart_2797382 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2797382 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2797382 prefixEnd_2797382 := by exact prefixLift 2797382
  have htrace : WordTrace (prefixWord ++ tailWord_2797382) baseStart_2797382 baseEnd_2797382 := by
    simpa [prefixWord, tailWord_2797382, baseEnd_2797382] using wordTrace_append hprefix tailTrace_2797382
  have hstable : (prefixWord ++ tailWord_2797382).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2797382).length < 2 ^ (prefixWord ++ tailWord_2797382).sum := by decide
  have hdescent : baseEnd_2797382 < baseStart_2797382 := by decide
  rcases family_descends (prefixWord ++ tailWord_2797382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2797388 : List Nat := [2, 2, 1, 3, 4, 1, 1, 1, 3, 3, 2]
def baseStart_2797388 : Nat := 118140960795 + 2797388 * 2 ^ 59
def prefixEnd_2797388 : Nat := 4983230072969 + 3 ^ 40 * 2797388 * 2
def baseEnd_2797388 : Nat := 1436404621119606440285053

theorem tailTrace_2797388 : CollatzResearch.WordTrace tailWord_2797388 prefixEnd_2797388 1436404621119606440285053 := by
  unfold tailWord_2797388
  simp only [CollatzResearch.WordTrace]
  refine ⟨51014561194774253339712409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68019414926365671119616545 51014561194774253339712409)
  ·
    refine ⟨38260920896080690004784307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51014561194774253339712409 38260920896080690004784307)
    ·
      refine ⟨57391381344121035007176461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38260920896080690004784307 57391381344121035007176461)
      ·
        refine ⟨21521768004045388127691173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 57391381344121035007176461 21521768004045388127691173)
        ·
          refine ⟨4035331500758510273942095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21521768004045388127691173 4035331500758510273942095)
          ·
            refine ⟨6052997251137765410913143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4035331500758510273942095 6052997251137765410913143)
            ·
              refine ⟨9079495876706648116369715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6052997251137765410913143 9079495876706648116369715)
              ·
                refine ⟨13619243815059972174554573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9079495876706648116369715 13619243815059972174554573)
                ·
                  refine ⟨5107216430647489565457965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13619243815059972174554573 5107216430647489565457965)
                  ·
                    refine ⟨1915206161492808587046737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5107216430647489565457965 1915206161492808587046737)
                    ·
                      refine ⟨1436404621119606440285053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1915206161492808587046737 1436404621119606440285053)
                      ·
                        rfl

theorem cell23_2797388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 1, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 1, 1, 1, 3, 3, 2].length) (baseStart_2797388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2797388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2797388 prefixEnd_2797388 := by exact prefixLift 2797388
  have htrace : WordTrace (prefixWord ++ tailWord_2797388) baseStart_2797388 baseEnd_2797388 := by
    simpa [prefixWord, tailWord_2797388, baseEnd_2797388] using wordTrace_append hprefix tailTrace_2797388
  have hstable : (prefixWord ++ tailWord_2797388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2797388).length < 2 ^ (prefixWord ++ tailWord_2797388).sum := by decide
  have hdescent : baseEnd_2797388 < baseStart_2797388 := by decide
  rcases family_descends (prefixWord ++ tailWord_2797388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2797401 : List Nat := [1, 2, 1, 2, 2, 3, 3, 2, 1, 4, 2]
def baseStart_2797401 : Nat := 118140960795 + 2797401 * 2 ^ 59
def prefixEnd_2797401 : Nat := 4983230072969 + 3 ^ 40 * 2797401 * 2
def baseEnd_2797401 : Nat := 1436411296368114889422493

theorem tailTrace_2797401 : CollatzResearch.WordTrace tailWord_2797401 prefixEnd_2797401 1436411296368114889422493 := by
  unfold tailWord_2797401
  simp only [CollatzResearch.WordTrace]
  refine ⟨102029596538501409899648057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68019731025667606599765371 102029596538501409899648057)
  ·
    refine ⟨76522197403876057424736043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102029596538501409899648057 76522197403876057424736043)
    ·
      refine ⟨114783296105814086137104065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76522197403876057424736043 114783296105814086137104065)
      ·
        refine ⟨86087472079360564602828049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 114783296105814086137104065 86087472079360564602828049)
        ·
          refine ⟨64565604059520423452121037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 86087472079360564602828049 64565604059520423452121037)
          ·
            refine ⟨24212101522320158794545389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 64565604059520423452121037 24212101522320158794545389)
            ·
              refine ⟨9079538070870059547954521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24212101522320158794545389 9079538070870059547954521)
              ·
                refine ⟨6809653553152544660965891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9079538070870059547954521 6809653553152544660965891)
                ·
                  refine ⟨10214480329728816991448837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6809653553152544660965891 10214480329728816991448837)
                  ·
                    refine ⟨1915215061824153185896657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10214480329728816991448837 1915215061824153185896657)
                    ·
                      refine ⟨1436411296368114889422493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1915215061824153185896657 1436411296368114889422493)
                      ·
                        rfl

theorem cell23_2797401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 3, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 3, 2, 1, 4, 2].length) (baseStart_2797401 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2797401 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2797401 prefixEnd_2797401 := by exact prefixLift 2797401
  have htrace : WordTrace (prefixWord ++ tailWord_2797401) baseStart_2797401 baseEnd_2797401 := by
    simpa [prefixWord, tailWord_2797401, baseEnd_2797401] using wordTrace_append hprefix tailTrace_2797401
  have hstable : (prefixWord ++ tailWord_2797401).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2797401).length < 2 ^ (prefixWord ++ tailWord_2797401).sum := by decide
  have hdescent : baseEnd_2797401 < baseStart_2797401 := by decide
  rcases family_descends (prefixWord ++ tailWord_2797401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2797417 : List Nat := [1, 2, 1, 1, 1, 3, 1, 3, 1, 2, 7]
def baseStart_2797417 : Nat := 118140960795 + 2797417 * 2 ^ 59
def prefixEnd_2797417 : Nat := 4983230072969 + 3 ^ 40 * 2797417 * 2
def baseEnd_2797417 : Nat := 1436419512058586826822419

theorem tailTrace_2797417 : CollatzResearch.WordTrace tailWord_2797417 prefixEnd_2797417 1436419512058586826822419 := by
  unfold tailWord_2797417
  simp only [CollatzResearch.WordTrace]
  refine ⟨102030180106443444632230505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68020120070962296421487003 102030180106443444632230505)
  ·
    refine ⟨76522635079832583474172879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102030180106443444632230505 76522635079832583474172879)
    ·
      refine ⟨114783952619748875211259319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76522635079832583474172879 114783952619748875211259319)
      ·
        refine ⟨172175928929623312816888979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114783952619748875211259319 172175928929623312816888979)
        ·
          refine ⟨258263893394434969225333469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 172175928929623312816888979 258263893394434969225333469)
          ·
            refine ⟨96848960022913113459500051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 258263893394434969225333469 96848960022913113459500051)
            ·
              refine ⟨145273440034369670189250077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 96848960022913113459500051 145273440034369670189250077)
              ·
                refine ⟨54477540012888626320968779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 145273440034369670189250077 54477540012888626320968779)
                ·
                  refine ⟨81716310019332939481453169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 54477540012888626320968779 81716310019332939481453169)
                  ·
                    refine ⟨61287232514499704611089877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 81716310019332939481453169 61287232514499704611089877)
                    ·
                      refine ⟨1436419512058586826822419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 61287232514499704611089877 1436419512058586826822419)
                      ·
                        rfl

theorem cell23_2797417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 3, 1, 2, 7].length) (baseStart_2797417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2797417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2797417 prefixEnd_2797417 := by exact prefixLift 2797417
  have htrace : WordTrace (prefixWord ++ tailWord_2797417) baseStart_2797417 baseEnd_2797417 := by
    simpa [prefixWord, tailWord_2797417, baseEnd_2797417] using wordTrace_append hprefix tailTrace_2797417
  have hstable : (prefixWord ++ tailWord_2797417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2797417).length < 2 ^ (prefixWord ++ tailWord_2797417).sum := by decide
  have hdescent : baseEnd_2797417 < baseStart_2797417 := by decide
  rcases family_descends (prefixWord ++ tailWord_2797417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2797427 : List Nat := [1, 1, 1, 2, 2, 1, 3, 1, 2, 1, 8]
def baseStart_2797427 : Nat := 118140960795 + 2797427 * 2 ^ 59
def prefixEnd_2797427 : Nat := 4983230072969 + 3 ^ 40 * 2797427 * 2
def baseEnd_2797427 : Nat := 1436424646865131787697373

theorem tailTrace_2797427 : CollatzResearch.WordTrace tailWord_2797427 prefixEnd_2797427 1436424646865131787697373 := by
  unfold tailWord_2797427
  simp only [CollatzResearch.WordTrace]
  refine ⟨102030544836407216340094535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68020363224271477560063023 102030544836407216340094535)
  ·
    refine ⟨153045817254610824510141803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102030544836407216340094535 153045817254610824510141803)
    ·
      refine ⟨229568725881916236765212705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 153045817254610824510141803 229568725881916236765212705)
      ·
        refine ⟨172176544411437177573909529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 229568725881916236765212705 172176544411437177573909529)
        ·
          refine ⟨129132408308577883180432147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 172176544411437177573909529 129132408308577883180432147)
          ·
            refine ⟨193698612462866824770648221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 129132408308577883180432147 193698612462866824770648221)
            ·
              refine ⟨72636979673575059288993083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 193698612462866824770648221 72636979673575059288993083)
              ·
                refine ⟨108955469510362588933489625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 72636979673575059288993083 108955469510362588933489625)
                ·
                  refine ⟨81716602132771941700117219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 108955469510362588933489625 81716602132771941700117219)
                  ·
                    refine ⟨122574903199157912550175829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 81716602132771941700117219 122574903199157912550175829)
                    ·
                      refine ⟨1436424646865131787697373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 122574903199157912550175829 1436424646865131787697373)
                      ·
                        rfl

theorem cell23_2797427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 1, 2, 1, 8].length) (baseStart_2797427 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2797427 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2797427 prefixEnd_2797427 := by exact prefixLift 2797427
  have htrace : WordTrace (prefixWord ++ tailWord_2797427) baseStart_2797427 baseEnd_2797427 := by
    simpa [prefixWord, tailWord_2797427, baseEnd_2797427] using wordTrace_append hprefix tailTrace_2797427
  have hstable : (prefixWord ++ tailWord_2797427).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2797427).length < 2 ^ (prefixWord ++ tailWord_2797427).sum := by decide
  have hdescent : baseEnd_2797427 < baseStart_2797427 := by decide
  rcases family_descends (prefixWord ++ tailWord_2797427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2797434 : List Nat := [3, 1, 1, 1, 1, 1, 5, 1, 1, 5, 3]
def baseStart_2797434 : Nat := 118140960795 + 2797434 * 2 ^ 59
def prefixEnd_2797434 : Nat := 4983230072969 + 3 ^ 40 * 2797434 * 2
def baseEnd_2797434 : Nat := 1436428241229713260309841

theorem tailTrace_2797434 : CollatzResearch.WordTrace tailWord_2797434 prefixEnd_2797434 1436428241229713260309841 := by
  unfold tailWord_2797434
  simp only [CollatzResearch.WordTrace]
  refine ⟨25507700036845464133899839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68020533431587904357066237 25507700036845464133899839)
  ·
    refine ⟨38261550055268196200849759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25507700036845464133899839 38261550055268196200849759)
    ·
      refine ⟨57392325082902294301274639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38261550055268196200849759 57392325082902294301274639)
      ·
        refine ⟨86088487624353441451911959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57392325082902294301274639 86088487624353441451911959)
        ·
          refine ⟨129132731436530162177867939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86088487624353441451911959 129132731436530162177867939)
          ·
            refine ⟨193699097154795243266801909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 129132731436530162177867939 193699097154795243266801909)
            ·
              refine ⟨18159290358262054056262679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 193699097154795243266801909 18159290358262054056262679)
              ·
                refine ⟨27238935537393081084394019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18159290358262054056262679 27238935537393081084394019)
                ·
                  refine ⟨40858403306089621626591029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27238935537393081084394019 40858403306089621626591029)
                  ·
                    refine ⟨3830475309945902027492909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 40858403306089621626591029 3830475309945902027492909)
                    ·
                      refine ⟨1436428241229713260309841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3830475309945902027492909 1436428241229713260309841)
                      ·
                        rfl

theorem cell23_2797434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 5, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 5, 1, 1, 5, 3].length) (baseStart_2797434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2797434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2797434 prefixEnd_2797434 := by exact prefixLift 2797434
  have htrace : WordTrace (prefixWord ++ tailWord_2797434) baseStart_2797434 baseEnd_2797434 := by
    simpa [prefixWord, tailWord_2797434, baseEnd_2797434] using wordTrace_append hprefix tailTrace_2797434
  have hstable : (prefixWord ++ tailWord_2797434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2797434).length < 2 ^ (prefixWord ++ tailWord_2797434).sum := by decide
  have hdescent : baseEnd_2797434 < baseStart_2797434 := by decide
  rcases family_descends (prefixWord ++ tailWord_2797434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2797458 : List Nat := [3, 2, 3, 2, 1, 1, 1, 5, 5]
def baseStart_2797458 : Nat := 118140960795 + 2797458 * 2 ^ 59
def prefixEnd_2797458 : Nat := 4983230072969 + 3 ^ 40 * 2797458 * 2
def baseEnd_2797458 : Nat := 159604507196157907378859

theorem tailTrace_2797458 : CollatzResearch.WordTrace tailWord_2797458 prefixEnd_2797458 159604507196157907378859 := by
  unfold tailWord_2797458
  simp only [CollatzResearch.WordTrace]
  refine ⟨25507918874823727158618257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68021116999529939089648685 25507918874823727158618257)
  ·
    refine ⟨19130939156117795368963693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25507918874823727158618257 19130939156117795368963693)
    ·
      refine ⟨7174102183544173263361385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19130939156117795368963693 7174102183544173263361385)
      ·
        refine ⟨5380576637658129947521039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7174102183544173263361385 5380576637658129947521039)
        ·
          refine ⟨8070864956487194921281559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5380576637658129947521039 8070864956487194921281559)
          ·
            refine ⟨12106297434730792381922339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8070864956487194921281559 12106297434730792381922339)
            ·
              refine ⟨18159446152096188572883509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12106297434730792381922339 18159446152096188572883509)
              ·
                refine ⟨1702448076759017678707829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 18159446152096188572883509 1702448076759017678707829)
                ·
                  refine ⟨159604507196157907378859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1702448076759017678707829 159604507196157907378859)
                  ·
                    rfl

theorem cell23_2797458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 1, 5, 5].length) (baseStart_2797458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2797458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2797458 prefixEnd_2797458 := by exact prefixLift 2797458
  have htrace : WordTrace (prefixWord ++ tailWord_2797458) baseStart_2797458 baseEnd_2797458 := by
    simpa [prefixWord, tailWord_2797458, baseEnd_2797458] using wordTrace_append hprefix tailTrace_2797458
  have hstable : (prefixWord ++ tailWord_2797458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2797458).length < 2 ^ (prefixWord ++ tailWord_2797458).sum := by decide
  have hdescent : baseEnd_2797458 < baseStart_2797458 := by decide
  rcases family_descends (prefixWord ++ tailWord_2797458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2797486 : List Nat := [4, 1, 5, 1, 2, 1, 1, 1, 1, 4, 2]
def baseStart_2797486 : Nat := 118140960795 + 2797486 * 2 ^ 59
def prefixEnd_2797486 : Nat := 4983230072969 + 3 ^ 40 * 2797486 * 2
def baseEnd_2797486 : Nat := 1436454942223747056859603

theorem tailTrace_2797486 : CollatzResearch.WordTrace tailWord_2797486 prefixEnd_2797486 1436454942223747056859603 := by
  unfold tailWord_2797486
  simp only [CollatzResearch.WordTrace]
  refine ⟨12754087092899183677061539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 68021797828795646277661541 12754087092899183677061539)
  ·
    refine ⟨19131130639348775515592309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12754087092899183677061539 19131130639348775515592309)
    ·
      refine ⟨1793543497438947704586779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 19131130639348775515592309 1793543497438947704586779)
      ·
        refine ⟨2690315246158421556880169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1793543497438947704586779 2690315246158421556880169)
        ·
          refine ⟨2017736434618816167660127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2690315246158421556880169 2017736434618816167660127)
          ·
            refine ⟨3026604651928224251490191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2017736434618816167660127 3026604651928224251490191)
            ·
              refine ⟨4539906977892336377235287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3026604651928224251490191 4539906977892336377235287)
              ·
                refine ⟨6809860466838504565852931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4539906977892336377235287 6809860466838504565852931)
                ·
                  refine ⟨10214790700257756848779397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6809860466838504565852931 10214790700257756848779397)
                  ·
                    refine ⟨1915273256298329409146137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10214790700257756848779397 1915273256298329409146137)
                    ·
                      refine ⟨1436454942223747056859603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1915273256298329409146137 1436454942223747056859603)
                      ·
                        rfl

theorem cell23_2797486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 2, 1, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 2, 1, 1, 1, 1, 4, 2].length) (baseStart_2797486 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2797486 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2797486 prefixEnd_2797486 := by exact prefixLift 2797486
  have htrace : WordTrace (prefixWord ++ tailWord_2797486) baseStart_2797486 baseEnd_2797486 := by
    simpa [prefixWord, tailWord_2797486, baseEnd_2797486] using wordTrace_append hprefix tailTrace_2797486
  have hstable : (prefixWord ++ tailWord_2797486).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2797486).length < 2 ^ (prefixWord ++ tailWord_2797486).sum := by decide
  have hdescent : baseEnd_2797486 < baseStart_2797486 := by decide
  rcases family_descends (prefixWord ++ tailWord_2797486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2797491 : List Nat := [1, 1, 1, 2, 3, 1, 3, 3, 2, 4, 2]
def baseStart_2797491 : Nat := 118140960795 + 2797491 * 2 ^ 59
def prefixEnd_2797491 : Nat := 4983230072969 + 3 ^ 40 * 2797491 * 2
def baseEnd_2797491 : Nat := 1436457509627019537297079

theorem tailTrace_2797491 : CollatzResearch.WordTrace tailWord_2797491 prefixEnd_2797491 1436457509627019537297079 := by
  unfold tailWord_2797491
  simp only [CollatzResearch.WordTrace]
  refine ⟨102032879108175355270424327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68021919405450236846949551 102032879108175355270424327)
  ·
    refine ⟨153049318662263032905636491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102032879108175355270424327 153049318662263032905636491)
    ·
      refine ⟨229573977993394549358454737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 153049318662263032905636491 229573977993394549358454737)
      ·
        refine ⟨172180483495045912018841053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 229573977993394549358454737 172180483495045912018841053)
        ·
          refine ⟨64567681310642217007065395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 172180483495045912018841053 64567681310642217007065395)
          ·
            refine ⟨96851521965963325510598093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64567681310642217007065395 96851521965963325510598093)
            ·
              refine ⟨36319320737236247066474285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 96851521965963325510598093 36319320737236247066474285)
              ·
                refine ⟨13619745276463592649927857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36319320737236247066474285 13619745276463592649927857)
                ·
                  refine ⟨10214808957347694487445893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13619745276463592649927857 10214808957347694487445893)
                  ·
                    refine ⟨1915276679502692716396105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10214808957347694487445893 1915276679502692716396105)
                    ·
                      refine ⟨1436457509627019537297079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1915276679502692716396105 1436457509627019537297079)
                      ·
                        rfl

theorem cell23_2797491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 3, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 3, 3, 2, 4, 2].length) (baseStart_2797491 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2797491 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2797491 prefixEnd_2797491 := by exact prefixLift 2797491
  have htrace : WordTrace (prefixWord ++ tailWord_2797491) baseStart_2797491 baseEnd_2797491 := by
    simpa [prefixWord, tailWord_2797491, baseEnd_2797491] using wordTrace_append hprefix tailTrace_2797491
  have hstable : (prefixWord ++ tailWord_2797491).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2797491).length < 2 ^ (prefixWord ++ tailWord_2797491).sum := by decide
  have hdescent : baseEnd_2797491 < baseStart_2797491 := by decide
  rcases family_descends (prefixWord ++ tailWord_2797491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2797504 : List Nat := [2, 1, 1, 2, 3, 2, 1, 1, 2, 4, 4]
def baseStart_2797504 : Nat := 118140960795 + 2797504 * 2 ^ 59
def prefixEnd_2797504 : Nat := 4983230072969 + 3 ^ 40 * 2797504 * 2
def baseEnd_2797504 : Nat := 1436464184875527986434519

theorem tailTrace_2797504 : CollatzResearch.WordTrace tailWord_2797504 prefixEnd_2797504 1436464184875527986434519 := by
  unfold tailWord_2797504
  simp only [CollatzResearch.WordTrace]
  refine ⟨51016676628564129245323783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68022235504752172327098377 51016676628564129245323783)
  ·
    refine ⟨76525014942846193867985675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51016676628564129245323783 76525014942846193867985675)
    ·
      refine ⟨114787522414269290801978513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76525014942846193867985675 114787522414269290801978513)
      ·
        refine ⟨86090641810701968101483885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 114787522414269290801978513 86090641810701968101483885)
        ·
          refine ⟨32283990679013238038056457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 86090641810701968101483885 32283990679013238038056457)
          ·
            refine ⟨24212993009259928528542343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32283990679013238038056457 24212993009259928528542343)
            ·
              refine ⟨36319489513889892792813515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24212993009259928528542343 36319489513889892792813515)
              ·
                refine ⟨54479234270834839189220273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36319489513889892792813515 54479234270834839189220273)
                ·
                  refine ⟨40859425703126129391915205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 54479234270834839189220273 40859425703126129391915205)
                  ·
                    refine ⟨7661142319336149260984101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 40859425703126129391915205 7661142319336149260984101)
                    ·
                      refine ⟨1436464184875527986434519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7661142319336149260984101 1436464184875527986434519)
                      ·
                        rfl

theorem cell23_2797504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 1, 1, 2, 4, 4].length) (baseStart_2797504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2797504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2797504 prefixEnd_2797504 := by exact prefixLift 2797504
  have htrace : WordTrace (prefixWord ++ tailWord_2797504) baseStart_2797504 baseEnd_2797504 := by
    simpa [prefixWord, tailWord_2797504, baseEnd_2797504] using wordTrace_append hprefix tailTrace_2797504
  have hstable : (prefixWord ++ tailWord_2797504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2797504).length < 2 ^ (prefixWord ++ tailWord_2797504).sum := by decide
  have hdescent : baseEnd_2797504 < baseStart_2797504 := by decide
  rcases family_descends (prefixWord ++ tailWord_2797504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2797511 : List Nat := [1, 1, 4, 1, 1, 2, 1, 5, 2, 2, 3]
def baseStart_2797511 : Nat := 118140960795 + 2797511 * 2 ^ 59
def prefixEnd_2797511 : Nat := 4983230072969 + 3 ^ 40 * 2797511 * 2
def baseEnd_2797511 : Nat := 1436467779240109459046987

theorem tailTrace_2797511 : CollatzResearch.WordTrace tailWord_2797511 prefixEnd_2797511 1436467779240109459046987 := by
  unfold tailWord_2797511
  simp only [CollatzResearch.WordTrace]
  refine ⟨102033608568102898686152387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68022405712068599124101591 102033608568102898686152387)
  ·
    refine ⟨153050412852154348029228581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102033608568102898686152387 153050412852154348029228581)
    ·
      refine ⟨28696952409778940255480359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 153050412852154348029228581 28696952409778940255480359)
      ·
        refine ⟨43045428614668410383220539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28696952409778940255480359 43045428614668410383220539)
        ·
          refine ⟨64568142922002615574830809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43045428614668410383220539 64568142922002615574830809)
          ·
            refine ⟨48426107191501961681123107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64568142922002615574830809 48426107191501961681123107)
            ·
              refine ⟨72639160787252942521684661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48426107191501961681123107 72639160787252942521684661)
              ·
                refine ⟨6809921323804963361407937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 72639160787252942521684661 6809921323804963361407937)
                ·
                  refine ⟨5107440992853722521055953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6809921323804963361407937 5107440992853722521055953)
                  ·
                    refine ⟨3830580744640291890791965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5107440992853722521055953 3830580744640291890791965)
                    ·
                      refine ⟨1436467779240109459046987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3830580744640291890791965 1436467779240109459046987)
                      ·
                        rfl

theorem cell23_2797511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 5, 2, 2, 3].length) (baseStart_2797511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2797511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2797511 prefixEnd_2797511 := by exact prefixLift 2797511
  have htrace : WordTrace (prefixWord ++ tailWord_2797511) baseStart_2797511 baseEnd_2797511 := by
    simpa [prefixWord, tailWord_2797511, baseEnd_2797511] using wordTrace_append hprefix tailTrace_2797511
  have hstable : (prefixWord ++ tailWord_2797511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2797511).length < 2 ^ (prefixWord ++ tailWord_2797511).sum := by decide
  have hdescent : baseEnd_2797511 < baseStart_2797511 := by decide
  rcases family_descends (prefixWord ++ tailWord_2797511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2797514 : List Nat := [3, 1, 2, 1, 2, 1, 3, 2, 8]
def baseStart_2797514 : Nat := 118140960795 + 2797514 * 2 ^ 59
def prefixEnd_2797514 : Nat := 4983230072969 + 3 ^ 40 * 2797514 * 2
def baseEnd_2797514 : Nat := 159607702186896994145497

theorem tailTrace_2797514 : CollatzResearch.WordTrace tailWord_2797514 prefixEnd_2797514 159607702186896994145497 := by
  unfold tailWord_2797514
  simp only [CollatzResearch.WordTrace]
  refine ⟨25508429496773007549627899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68022478658061353465674397 25508429496773007549627899)
  ·
    refine ⟨38262644245159511324441849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25508429496773007549627899 38262644245159511324441849)
    ·
      refine ⟨28696983183869633493331387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38262644245159511324441849 28696983183869633493331387)
      ·
        refine ⟨43045474775804450239997081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28696983183869633493331387 43045474775804450239997081)
        ·
          refine ⟨32284106081853337679997811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43045474775804450239997081 32284106081853337679997811)
          ·
            refine ⟨48426159122780006519996717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32284106081853337679997811 48426159122780006519996717)
            ·
              refine ⟨18159809671042502444998769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 48426159122780006519996717 18159809671042502444998769)
              ·
                refine ⟨13619857253281876833749077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18159809671042502444998769 13619857253281876833749077)
                ·
                  refine ⟨159607702186896994145497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 13619857253281876833749077 159607702186896994145497)
                  ·
                    rfl

theorem cell23_2797514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 3, 2, 8].length) (baseStart_2797514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2797514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2797514 prefixEnd_2797514 := by exact prefixLift 2797514
  have htrace : WordTrace (prefixWord ++ tailWord_2797514) baseStart_2797514 baseEnd_2797514 := by
    simpa [prefixWord, tailWord_2797514, baseEnd_2797514] using wordTrace_append hprefix tailTrace_2797514
  have hstable : (prefixWord ++ tailWord_2797514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2797514).length < 2 ^ (prefixWord ++ tailWord_2797514).sum := by decide
  have hdescent : baseEnd_2797514 < baseStart_2797514 := by decide
  rcases family_descends (prefixWord ++ tailWord_2797514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2797544 : List Nat := [2, 1, 4, 1, 1, 1, 1, 1, 2, 9]
def baseStart_2797544 : Nat := 118140960795 + 2797544 * 2 ^ 59
def prefixEnd_2797544 : Nat := 4983230072969 + 3 ^ 40 * 2797544 * 2
def baseEnd_2797544 : Nat := 478828241367235943311445

theorem tailTrace_2797544 : CollatzResearch.WordTrace tailWord_2797544 prefixEnd_2797544 478828241367235943311445 := by
  unfold tailWord_2797544
  simp only [CollatzResearch.WordTrace]
  refine ⟨51017406088491672661051843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68023208117988896881402457 51017406088491672661051843)
  ·
    refine ⟨76526109132737508991577765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51017406088491672661051843 76526109132737508991577765)
    ·
      refine ⟨14348645462388282935920831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 76526109132737508991577765 14348645462388282935920831)
      ·
        refine ⟨21522968193582424403881247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14348645462388282935920831 21522968193582424403881247)
        ·
          refine ⟨32284452290373636605821871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21522968193582424403881247 32284452290373636605821871)
          ·
            refine ⟨48426678435560454908732807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32284452290373636605821871 48426678435560454908732807)
            ·
              refine ⟨72640017653340682363099211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48426678435560454908732807 72640017653340682363099211)
              ·
                refine ⟨108960026480011023544648817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 72640017653340682363099211 108960026480011023544648817)
                ·
                  refine ⟨81720019860008267658486613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 108960026480011023544648817 81720019860008267658486613)
                  ·
                    refine ⟨478828241367235943311445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 81720019860008267658486613 478828241367235943311445)
                    ·
                      rfl

theorem cell23_2797544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 1, 2, 9].length) (baseStart_2797544 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2797544 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2797544 prefixEnd_2797544 := by exact prefixLift 2797544
  have htrace : WordTrace (prefixWord ++ tailWord_2797544) baseStart_2797544 baseEnd_2797544 := by
    simpa [prefixWord, tailWord_2797544, baseEnd_2797544] using wordTrace_append hprefix tailTrace_2797544
  have hstable : (prefixWord ++ tailWord_2797544).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2797544).length < 2 ^ (prefixWord ++ tailWord_2797544).sum := by decide
  have hdescent : baseEnd_2797544 < baseStart_2797544 := by decide
  rcases family_descends (prefixWord ++ tailWord_2797544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2797561 : List Nat := [1, 2, 1, 3, 1, 5, 1, 1, 3, 5]
def baseStart_2797561 : Nat := 118140960795 + 2797561 * 2 ^ 59
def prefixEnd_2797561 : Nat := 4983230072969 + 3 ^ 40 * 2797561 * 2
def baseEnd_2797561 : Nat := 478831151090944754473919

theorem tailTrace_2797561 : CollatzResearch.WordTrace tailWord_2797561 prefixEnd_2797561 478831151090944754473919 := by
  unfold tailWord_2797561
  simp only [CollatzResearch.WordTrace]
  refine ⟨102035432217921757225472537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68023621478614504816981691 102035432217921757225472537)
  ·
    refine ⟨76526574163441317919104403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102035432217921757225472537 76526574163441317919104403)
    ·
      refine ⟨114789861245161976878656605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76526574163441317919104403 114789861245161976878656605)
      ·
        refine ⟨43046197966935741329496227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 114789861245161976878656605 43046197966935741329496227)
        ·
          refine ⟨64569296950403611994244341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43046197966935741329496227 64569296950403611994244341)
          ·
            refine ⟨6053371589100338624460407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 64569296950403611994244341 6053371589100338624460407)
            ·
              refine ⟨9080057383650507936690611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6053371589100338624460407 9080057383650507936690611)
              ·
                refine ⟨13620086075475761905035917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9080057383650507936690611 13620086075475761905035917)
                ·
                  refine ⟨5107532278303410714388469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13620086075475761905035917 5107532278303410714388469)
                  ·
                    refine ⟨478831151090944754473919, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5107532278303410714388469 478831151090944754473919)
                    ·
                      rfl

theorem cell23_2797561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 5, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 5, 1, 1, 3, 5].length) (baseStart_2797561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2797561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2797561 prefixEnd_2797561 := by exact prefixLift 2797561
  have htrace : WordTrace (prefixWord ++ tailWord_2797561) baseStart_2797561 baseEnd_2797561 := by
    simpa [prefixWord, tailWord_2797561, baseEnd_2797561] using wordTrace_append hprefix tailTrace_2797561
  have hstable : (prefixWord ++ tailWord_2797561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2797561).length < 2 ^ (prefixWord ++ tailWord_2797561).sum := by decide
  have hdescent : baseEnd_2797561 < baseStart_2797561 := by decide
  rcases family_descends (prefixWord ++ tailWord_2797561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2797618 : List Nat := [3, 2, 1, 1, 2, 3, 2, 1, 3, 2, 3]
def baseStart_2797618 : Nat := 118140960795 + 2797618 * 2 ^ 59
def prefixEnd_2797618 : Nat := 4983230072969 + 3 ^ 40 * 2797618 * 2
def baseEnd_2797618 : Nat := 1436522721670140540408995

theorem tailTrace_2797618 : CollatzResearch.WordTrace tailWord_2797618 prefixEnd_2797618 1436522721670140540408995 := by
  unfold tailWord_2797618
  simp only [CollatzResearch.WordTrace]
  refine ⟨25509377794678813990074377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68025007452476837306865005 25509377794678813990074377)
  ·
    refine ⟨19132033346009110492555783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25509377794678813990074377 19132033346009110492555783)
    ·
      refine ⟨28698050019013665738833675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19132033346009110492555783 28698050019013665738833675)
      ·
        refine ⟨43047075028520498608250513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28698050019013665738833675 43047075028520498608250513)
        ·
          refine ⟨32285306271390373956187885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43047075028520498608250513 32285306271390373956187885)
          ·
            refine ⟨12106989851771390233570457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32285306271390373956187885 12106989851771390233570457)
            ·
              refine ⟨9080242388828542675177843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12106989851771390233570457 9080242388828542675177843)
              ·
                refine ⟨13620363583242814012766765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9080242388828542675177843 13620363583242814012766765)
                ·
                  refine ⟨5107636343716055254787537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13620363583242814012766765 5107636343716055254787537)
                  ·
                    refine ⟨3830727257787041441090653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5107636343716055254787537 3830727257787041441090653)
                    ·
                      refine ⟨1436522721670140540408995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3830727257787041441090653 1436522721670140540408995)
                      ·
                        rfl

theorem cell23_2797618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 2, 1, 3, 2, 3].length) (baseStart_2797618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2797618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2797618 prefixEnd_2797618 := by exact prefixLift 2797618
  have htrace : WordTrace (prefixWord ++ tailWord_2797618) baseStart_2797618 baseEnd_2797618 := by
    simpa [prefixWord, tailWord_2797618, baseEnd_2797618] using wordTrace_append hprefix tailTrace_2797618
  have hstable : (prefixWord ++ tailWord_2797618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2797618).length < 2 ^ (prefixWord ++ tailWord_2797618).sum := by decide
  have hdescent : baseEnd_2797618 < baseStart_2797618 := by decide
  rcases family_descends (prefixWord ++ tailWord_2797618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2797632 : List Nat := [2, 1, 1, 2, 2, 4, 1, 5, 1, 2, 2]
def baseStart_2797632 : Nat := 118140960795 + 2797632 * 2 ^ 59
def prefixEnd_2797632 : Nat := 4983230072969 + 3 ^ 40 * 2797632 * 2
def baseEnd_2797632 : Nat := 1436529910399303485633931

theorem tailTrace_2797632 : CollatzResearch.WordTrace tailWord_2797632 prefixEnd_2797632 1436529910399303485633931 := by
  unfold tailWord_2797632
  simp only [CollatzResearch.WordTrace]
  refine ⟨51019010900332268175653575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68025347867109690900871433 51019010900332268175653575)
  ·
    refine ⟨76528516350498402263480363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51019010900332268175653575 76528516350498402263480363)
    ·
      refine ⟨114792774525747603395220545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76528516350498402263480363 114792774525747603395220545)
      ·
        refine ⟨86094580894310702546415409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 114792774525747603395220545 86094580894310702546415409)
        ·
          refine ⟨64570935670733026909811557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 86094580894310702546415409 64570935670733026909811557)
          ·
            refine ⟨12107050438262442545589667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 64570935670733026909811557 12107050438262442545589667)
            ·
              refine ⟨18160575657393663818384501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12107050438262442545589667 18160575657393663818384501)
              ·
                refine ⟨1702553967880655982973547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 18160575657393663818384501 1702553967880655982973547)
                ·
                  refine ⟨2553830951820983974460321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1702553967880655982973547 2553830951820983974460321)
                  ·
                    refine ⟨1915373213865737980845241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2553830951820983974460321 1915373213865737980845241)
                    ·
                      refine ⟨1436529910399303485633931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1915373213865737980845241 1436529910399303485633931)
                      ·
                        rfl

theorem cell23_2797632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 1, 5, 1, 2, 2].length) (baseStart_2797632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2797632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2797632 prefixEnd_2797632 := by exact prefixLift 2797632
  have htrace : WordTrace (prefixWord ++ tailWord_2797632) baseStart_2797632 baseEnd_2797632 := by
    simpa [prefixWord, tailWord_2797632, baseEnd_2797632] using wordTrace_append hprefix tailTrace_2797632
  have hstable : (prefixWord ++ tailWord_2797632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2797632).length < 2 ^ (prefixWord ++ tailWord_2797632).sum := by decide
  have hdescent : baseEnd_2797632 < baseStart_2797632 := by decide
  rcases family_descends (prefixWord ++ tailWord_2797632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2797638 : List Nat := [6, 1, 1, 1, 1, 1, 12]
def baseStart_2797638 : Nat := 118140960795 + 2797638 * 2 ^ 59
def prefixEnd_2797638 : Nat := 4983230072969 + 3 ^ 40 * 2797638 * 2
def baseEnd_2797638 : Nat := 17734975201027536569863

theorem tailTrace_2797638 : CollatzResearch.WordTrace tailWord_2797638 prefixEnd_2797638 17734975201027536569863 := by
  unfold tailWord_2797638
  simp only [CollatzResearch.WordTrace]
  refine ⟨3188695019957587480500799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 68025493759095199584017045 3188695019957587480500799)
  ·
    refine ⟨4783042529936381220751199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3188695019957587480500799 4783042529936381220751199)
    ·
      refine ⟨7174563794904571831126799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4783042529936381220751199 7174563794904571831126799)
      ·
        refine ⟨10761845692356857746690199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7174563794904571831126799 10761845692356857746690199)
        ·
          refine ⟨16142768538535286620035299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10761845692356857746690199 16142768538535286620035299)
          ·
            refine ⟨24214152807802929930052949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16142768538535286620035299 24214152807802929930052949)
            ·
              refine ⟨17734975201027536569863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 24214152807802929930052949 17734975201027536569863)
              ·
                rfl

theorem cell23_2797638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 12].length) (baseStart_2797638 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2797638 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2797638 prefixEnd_2797638 := by exact prefixLift 2797638
  have htrace : WordTrace (prefixWord ++ tailWord_2797638) baseStart_2797638 baseEnd_2797638 := by
    simpa [prefixWord, tailWord_2797638, baseEnd_2797638] using wordTrace_append hprefix tailTrace_2797638
  have hstable : (prefixWord ++ tailWord_2797638).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2797638).length < 2 ^ (prefixWord ++ tailWord_2797638).sum := by decide
  have hdescent : baseEnd_2797638 < baseStart_2797638 := by decide
  rcases family_descends (prefixWord ++ tailWord_2797638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2797662 : List Nat := [4, 4, 1, 1, 2, 1, 1, 1, 1, 1, 6]
def baseStart_2797662 : Nat := 118140960795 + 2797662 * 2 ^ 59
def prefixEnd_2797662 : Nat := 4983230072969 + 3 ^ 40 * 2797662 * 2
def baseEnd_2797662 : Nat := 1436545314818938368258793

theorem tailTrace_2797662 : CollatzResearch.WordTrace tailWord_2797662 prefixEnd_2797662 1436545314818938368258793 := by
  unfold tailWord_2797662
  simp only [CollatzResearch.WordTrace]
  refine ⟨12754889498819481434362405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 68026077327037234316599493 12754889498819481434362405)
  ·
    refine ⟨2391541781028652768942951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12754889498819481434362405 2391541781028652768942951)
    ·
      refine ⟨3587312671542979153414427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2391541781028652768942951 3587312671542979153414427)
      ·
        refine ⟨5380969007314468730121641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3587312671542979153414427 5380969007314468730121641)
        ·
          refine ⟨4035726755485851547591231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5380969007314468730121641 4035726755485851547591231)
          ·
            refine ⟨6053590133228777321386847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4035726755485851547591231 6053590133228777321386847)
            ·
              refine ⟨9080385199843165982080271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6053590133228777321386847 9080385199843165982080271)
              ·
                refine ⟨13620577799764748973120407, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9080385199843165982080271 13620577799764748973120407)
                ·
                  refine ⟨20430866699647123459680611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13620577799764748973120407 20430866699647123459680611)
                  ·
                    refine ⟨30646300049470685189520917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20430866699647123459680611 30646300049470685189520917)
                    ·
                      refine ⟨1436545314818938368258793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 30646300049470685189520917 1436545314818938368258793)
                      ·
                        rfl

theorem cell23_2797662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 1, 1, 1, 1, 1, 6].length) (baseStart_2797662 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2797662 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2797662 prefixEnd_2797662 := by exact prefixLift 2797662
  have htrace : WordTrace (prefixWord ++ tailWord_2797662) baseStart_2797662 baseEnd_2797662 := by
    simpa [prefixWord, tailWord_2797662, baseEnd_2797662] using wordTrace_append hprefix tailTrace_2797662
  have hstable : (prefixWord ++ tailWord_2797662).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2797662).length < 2 ^ (prefixWord ++ tailWord_2797662).sum := by decide
  have hdescent : baseEnd_2797662 < baseStart_2797662 := by decide
  rcases family_descends (prefixWord ++ tailWord_2797662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2797688 : List Nat := [2, 1, 2, 1, 1, 1, 3, 3, 3, 4, 2]
def baseStart_2797688 : Nat := 118140960795 + 2797688 * 2 ^ 59
def prefixEnd_2797688 : Nat := 4983230072969 + 3 ^ 40 * 2797688 * 2
def baseEnd_2797688 : Nat := 1436558665315955266533673

theorem tailTrace_2797688 : CollatzResearch.WordTrace tailWord_2797688 prefixEnd_2797688 1436558665315955266533673 := by
  unfold tailWord_2797688
  simp only [CollatzResearch.WordTrace]
  refine ⟨51020032144230828957672859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68026709525641105276897145 51020032144230828957672859)
  ·
    refine ⟨76530048216346243436509289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51020032144230828957672859 76530048216346243436509289)
    ·
      refine ⟨57397536162259682577381967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76530048216346243436509289 57397536162259682577381967)
      ·
        refine ⟨86096304243389523866072951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57397536162259682577381967 86096304243389523866072951)
        ·
          refine ⟨129144456365084285799109427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86096304243389523866072951 129144456365084285799109427)
          ·
            refine ⟨193716684547626428698664141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 129144456365084285799109427 193716684547626428698664141)
            ·
              refine ⟨72643756705359910761999053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 193716684547626428698664141 72643756705359910761999053)
              ·
                refine ⟨27241408764509966535749645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 72643756705359910761999053 27241408764509966535749645)
                ·
                  refine ⟨10215528286691237450906117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27241408764509966535749645 10215528286691237450906117)
                  ·
                    refine ⟨1915411553754607022044897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10215528286691237450906117 1915411553754607022044897)
                    ·
                      refine ⟨1436558665315955266533673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1915411553754607022044897 1436558665315955266533673)
                      ·
                        rfl

theorem cell23_2797688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 3, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 3, 3, 4, 2].length) (baseStart_2797688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2797688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2797688 prefixEnd_2797688 := by exact prefixLift 2797688
  have htrace : WordTrace (prefixWord ++ tailWord_2797688) baseStart_2797688 baseEnd_2797688 := by
    simpa [prefixWord, tailWord_2797688, baseEnd_2797688] using wordTrace_append hprefix tailTrace_2797688
  have hstable : (prefixWord ++ tailWord_2797688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2797688).length < 2 ^ (prefixWord ++ tailWord_2797688).sum := by decide
  have hdescent : baseEnd_2797688 < baseStart_2797688 := by decide
  rcases family_descends (prefixWord ++ tailWord_2797688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2797691 : List Nat := [1, 1, 1, 1, 1, 4, 1, 1, 3, 6, 3]
def baseStart_2797691 : Nat := 118140960795 + 2797691 * 2 ^ 59
def prefixEnd_2797691 : Nat := 4983230072969 + 3 ^ 40 * 2797691 * 2
def baseEnd_2797691 : Nat := 1436560205757918754796159

theorem tailTrace_2797691 : CollatzResearch.WordTrace tailWord_2797691 prefixEnd_2797691 1436560205757918754796159 := by
  unfold tailWord_2797691
  simp only [CollatzResearch.WordTrace]
  refine ⟨102040173707450789427704927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68026782471633859618469951 102040173707450789427704927)
  ·
    refine ⟨153060260561176184141557391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102040173707450789427704927 153060260561176184141557391)
    ·
      refine ⟨229590390841764276212336087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 153060260561176184141557391 229590390841764276212336087)
      ·
        refine ⟨344385586262646414318504131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 229590390841764276212336087 344385586262646414318504131)
        ·
          refine ⟨516578379393969621477756197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 344385586262646414318504131 516578379393969621477756197)
          ·
            refine ⟨96858446136369304027079287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 516578379393969621477756197 96858446136369304027079287)
            ·
              refine ⟨145287669204553956040618931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 96858446136369304027079287 145287669204553956040618931)
              ·
                refine ⟨217931503806830934060928397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 145287669204553956040618931 217931503806830934060928397)
                ·
                  refine ⟨81724313927561600272848149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 217931503806830934060928397 81724313927561600272848149)
                  ·
                    refine ⟨3830827215354450012789757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 81724313927561600272848149 3830827215354450012789757)
                    ·
                      refine ⟨1436560205757918754796159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3830827215354450012789757 1436560205757918754796159)
                      ·
                        rfl

theorem cell23_2797691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 1, 3, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 1, 3, 6, 3].length) (baseStart_2797691 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2797691 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2797691 prefixEnd_2797691 := by exact prefixLift 2797691
  have htrace : WordTrace (prefixWord ++ tailWord_2797691) baseStart_2797691 baseEnd_2797691 := by
    simpa [prefixWord, tailWord_2797691, baseEnd_2797691] using wordTrace_append hprefix tailTrace_2797691
  have hstable : (prefixWord ++ tailWord_2797691).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2797691).length < 2 ^ (prefixWord ++ tailWord_2797691).sum := by decide
  have hdescent : baseEnd_2797691 < baseStart_2797691 := by decide
  rcases family_descends (prefixWord ++ tailWord_2797691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2797705 : List Nat := [1, 2, 1, 1, 4, 2, 1, 3, 4, 2, 2]
def baseStart_2797705 : Nat := 118140960795 + 2797705 * 2 ^ 59
def prefixEnd_2797705 : Nat := 4983230072969 + 3 ^ 40 * 2797705 * 2
def baseEnd_2797705 : Nat := 1436567394487081700021095

theorem tailTrace_2797705 : CollatzResearch.WordTrace tailWord_2797705 prefixEnd_2797705 1436567394487081700021095 := by
  unfold tailWord_2797705
  simp only [CollatzResearch.WordTrace]
  refine ⟨102040684329400069818714569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68027122886266713212476379 102040684329400069818714569)
  ·
    refine ⟨76530513247050052364035927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102040684329400069818714569 76530513247050052364035927)
    ·
      refine ⟨114795769870575078546053891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76530513247050052364035927 114795769870575078546053891)
      ·
        refine ⟨172193654805862617819080837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114795769870575078546053891 172193654805862617819080837)
        ·
          refine ⟨32286310276099240841077657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 172193654805862617819080837 32286310276099240841077657)
          ·
            refine ⟨24214732707074430630808243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32286310276099240841077657 24214732707074430630808243)
            ·
              refine ⟨36322099060611645946212365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24214732707074430630808243 36322099060611645946212365)
              ·
                refine ⟨13620787147729367229829637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36322099060611645946212365 13620787147729367229829637)
                ·
                  refine ⟨2553897590199256355593057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13620787147729367229829637 2553897590199256355593057)
                  ·
                    refine ⟨1915423192649442266694793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2553897590199256355593057 1915423192649442266694793)
                    ·
                      refine ⟨1436567394487081700021095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1915423192649442266694793 1436567394487081700021095)
                      ·
                        rfl

theorem cell23_2797705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 1, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 1, 3, 4, 2, 2].length) (baseStart_2797705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2797705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2797705 prefixEnd_2797705 := by exact prefixLift 2797705
  have htrace : WordTrace (prefixWord ++ tailWord_2797705) baseStart_2797705 baseEnd_2797705 := by
    simpa [prefixWord, tailWord_2797705, baseEnd_2797705] using wordTrace_append hprefix tailTrace_2797705
  have hstable : (prefixWord ++ tailWord_2797705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2797705).length < 2 ^ (prefixWord ++ tailWord_2797705).sum := by decide
  have hdescent : baseEnd_2797705 < baseStart_2797705 := by decide
  rcases family_descends (prefixWord ++ tailWord_2797705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2797726 : List Nat := [4, 3, 1, 1, 3, 2, 1, 2, 1, 3, 2]
def baseStart_2797726 : Nat := 118140960795 + 2797726 * 2 ^ 59
def prefixEnd_2797726 : Nat := 4983230072969 + 3 ^ 40 * 2797726 * 2
def baseEnd_2797726 : Nat := 1436578177580826117858499

theorem tailTrace_2797726 : CollatzResearch.WordTrace tailWord_2797726 prefixEnd_2797726 1436578177580826117858499 := by
  unfold tailWord_2797726
  simp only [CollatzResearch.WordTrace]
  refine ⟨12755181282790498800653629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 68027633508215993603486021 12755181282790498800653629)
  ·
    refine ⟨4783192981046437050245111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12755181282790498800653629 4783192981046437050245111)
    ·
      refine ⟨7174789471569655575367667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4783192981046437050245111 7174789471569655575367667)
      ·
        refine ⟨10762184207354483363051501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7174789471569655575367667 10762184207354483363051501)
        ·
          refine ⟨4035819077757931261144313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10762184207354483363051501 4035819077757931261144313)
          ·
            refine ⟨3026864308318448445858235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4035819077757931261144313 3026864308318448445858235)
            ·
              refine ⟨4540296462477672668787353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3026864308318448445858235 4540296462477672668787353)
              ·
                refine ⟨3405222346858254501590515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4540296462477672668787353 3405222346858254501590515)
                ·
                  refine ⟨5107833520287381752385773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3405222346858254501590515 5107833520287381752385773)
                  ·
                    refine ⟨1915437570107768157144665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5107833520287381752385773 1915437570107768157144665)
                    ·
                      refine ⟨1436578177580826117858499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1915437570107768157144665 1436578177580826117858499)
                      ·
                        rfl

theorem cell23_2797726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 2, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 2, 1, 2, 1, 3, 2].length) (baseStart_2797726 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2797726 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2797726 prefixEnd_2797726 := by exact prefixLift 2797726
  have htrace : WordTrace (prefixWord ++ tailWord_2797726) baseStart_2797726 baseEnd_2797726 := by
    simpa [prefixWord, tailWord_2797726, baseEnd_2797726] using wordTrace_append hprefix tailTrace_2797726
  have hstable : (prefixWord ++ tailWord_2797726).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2797726).length < 2 ^ (prefixWord ++ tailWord_2797726).sum := by decide
  have hdescent : baseEnd_2797726 < baseStart_2797726 := by decide
  rcases family_descends (prefixWord ++ tailWord_2797726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2797772 : List Nat := [2, 2, 1, 6, 1, 1, 1, 1, 2, 3, 3]
def baseStart_2797772 : Nat := 118140960795 + 2797772 * 2 ^ 59
def prefixEnd_2797772 : Nat := 4983230072969 + 3 ^ 40 * 2797772 * 2
def baseEnd_2797772 : Nat := 1436601797690932937883287

theorem tailTrace_2797772 : CollatzResearch.WordTrace tailWord_2797772 prefixEnd_2797772 1436601797690932937883287 := by
  unfold tailWord_2797772
  simp only [CollatzResearch.WordTrace]
  refine ⟨51021564010078670130701785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68028752013438226840935713 51021564010078670130701785)
  ·
    refine ⟨38266173007559002598026339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51021564010078670130701785 38266173007559002598026339)
    ·
      refine ⟨57399259511338503897039509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38266173007559002598026339 57399259511338503897039509)
      ·
        refine ⟨2690590289593992370173727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 57399259511338503897039509 2690590289593992370173727)
        ·
          refine ⟨4035885434390988555260591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2690590289593992370173727 4035885434390988555260591)
          ·
            refine ⟨6053828151586482832890887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4035885434390988555260591 6053828151586482832890887)
            ·
              refine ⟨9080742227379724249336331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6053828151586482832890887 9080742227379724249336331)
              ·
                refine ⟨13621113341069586374004497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9080742227379724249336331 13621113341069586374004497)
                ·
                  refine ⟨10215835005802189780503373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13621113341069586374004497 10215835005802189780503373)
                  ·
                    refine ⟨3830938127175821167688765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10215835005802189780503373 3830938127175821167688765)
                    ·
                      refine ⟨1436601797690932937883287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3830938127175821167688765 1436601797690932937883287)
                      ·
                        rfl

theorem cell23_2797772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 1, 1, 1, 2, 3, 3].length) (baseStart_2797772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2797772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2797772 prefixEnd_2797772 := by exact prefixLift 2797772
  have htrace : WordTrace (prefixWord ++ tailWord_2797772) baseStart_2797772 baseEnd_2797772 := by
    simpa [prefixWord, tailWord_2797772, baseEnd_2797772] using wordTrace_append hprefix tailTrace_2797772
  have hstable : (prefixWord ++ tailWord_2797772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2797772).length < 2 ^ (prefixWord ++ tailWord_2797772).sum := by decide
  have hdescent : baseEnd_2797772 < baseStart_2797772 := by decide
  rcases family_descends (prefixWord ++ tailWord_2797772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2797801 : List Nat := [1, 2, 1, 1, 1, 2, 2, 3, 10]
def baseStart_2797801 : Nat := 118140960795 + 2797801 * 2 ^ 59
def prefixEnd_2797801 : Nat := 4983230072969 + 3 ^ 40 * 2797801 * 2
def baseEnd_2797801 : Nat := 159624076514434813824517

theorem tailTrace_2797801 : CollatzResearch.WordTrace tailWord_2797801 prefixEnd_2797801 159624076514434813824517 := by
  unfold tailWord_2797801
  simp only [CollatzResearch.WordTrace]
  refine ⟨102044185737052278214209257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68029457158034852142806171 102044185737052278214209257)
  ·
    refine ⟨76533139302789208660656943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102044185737052278214209257 76533139302789208660656943)
    ·
      refine ⟨114799708954183812990985415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76533139302789208660656943 114799708954183812990985415)
      ·
        refine ⟨172199563431275719486478123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114799708954183812990985415 172199563431275719486478123)
        ·
          refine ⟨258299345146913579229717185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 172199563431275719486478123 258299345146913579229717185)
          ·
            refine ⟨193724508860185184422287889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 258299345146913579229717185 193724508860185184422287889)
            ·
              refine ⟨145293381645138888316715917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 193724508860185184422287889 145293381645138888316715917)
              ·
                refine ⟨54485018116927083118768469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 145293381645138888316715917 54485018116927083118768469)
                ·
                  refine ⟨159624076514434813824517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 54485018116927083118768469 159624076514434813824517)
                  ·
                    rfl

theorem cell23_2797801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 3, 10].length) (baseStart_2797801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2797801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2797801 prefixEnd_2797801 := by exact prefixLift 2797801
  have htrace : WordTrace (prefixWord ++ tailWord_2797801) baseStart_2797801 baseEnd_2797801 := by
    simpa [prefixWord, tailWord_2797801, baseEnd_2797801] using wordTrace_append hprefix tailTrace_2797801
  have hstable : (prefixWord ++ tailWord_2797801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2797801).length < 2 ^ (prefixWord ++ tailWord_2797801).sum := by decide
  have hdescent : baseEnd_2797801 < baseStart_2797801 := by decide
  rcases family_descends (prefixWord ++ tailWord_2797801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2797818 : List Nat := [3, 1, 1, 1, 1, 6, 1, 1, 8]
def baseStart_2797818 : Nat := 118140960795 + 2797818 * 2 ^ 59
def prefixEnd_2797818 : Nat := 4983230072969 + 3 ^ 40 * 2797818 * 2
def baseEnd_2797818 : Nat := 159625046422337750878675

theorem tailTrace_2797818 : CollatzResearch.WordTrace tailWord_2797818 prefixEnd_2797818 159625046422337750878675 := by
  unfold tailWord_2797818
  simp only [CollatzResearch.WordTrace]
  refine ⟨25511201444497672529394527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68029870518660460078385405 25511201444497672529394527)
  ·
    refine ⟨38266802166746508794091791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25511201444497672529394527 38266802166746508794091791)
    ·
      refine ⟨57400203250119763191137687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38266802166746508794091791 57400203250119763191137687)
      ·
        refine ⟨86100304875179644786706531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57400203250119763191137687 86100304875179644786706531)
        ·
          refine ⟨129150457312769467180059797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86100304875179644786706531 129150457312769467180059797)
          ·
            refine ⟨6053927686536068774065303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 129150457312769467180059797 6053927686536068774065303)
            ·
              refine ⟨9080891529804103161097955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6053927686536068774065303 9080891529804103161097955)
              ·
                refine ⟨13621337294706154741646933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9080891529804103161097955 13621337294706154741646933)
                ·
                  refine ⟨159625046422337750878675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 13621337294706154741646933 159625046422337750878675)
                  ·
                    rfl

theorem cell23_2797818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 6, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 6, 1, 1, 8].length) (baseStart_2797818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2797818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2797818 prefixEnd_2797818 := by exact prefixLift 2797818
  have htrace : WordTrace (prefixWord ++ tailWord_2797818) baseStart_2797818 baseEnd_2797818 := by
    simpa [prefixWord, tailWord_2797818, baseEnd_2797818] using wordTrace_append hprefix tailTrace_2797818
  have hstable : (prefixWord ++ tailWord_2797818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2797818).length < 2 ^ (prefixWord ++ tailWord_2797818).sum := by decide
  have hdescent : baseEnd_2797818 < baseStart_2797818 := by decide
  rcases family_descends (prefixWord ++ tailWord_2797818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2797822 : List Nat := [4, 2, 2, 1, 1, 1, 4, 1, 3, 4]
def baseStart_2797822 : Nat := 118140960795 + 2797822 * 2 ^ 59
def prefixEnd_2797822 : Nat := 4983230072969 + 3 ^ 40 * 2797822 * 2
def baseEnd_2797822 : Nat := 478875823907885914086019

theorem tailTrace_2797822 : CollatzResearch.WordTrace tailWord_2797822 prefixEnd_2797822 478875823907885914086019 := by
  unfold tailWord_2797822
  simp only [CollatzResearch.WordTrace]
  refine ⟨12755618958747024850090465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 68029967779984132533815813 12755618958747024850090465)
  ·
    refine ⟨9566714219060268637567849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12755618958747024850090465 9566714219060268637567849)
    ·
      refine ⟨7175035664295201478175887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9566714219060268637567849 7175035664295201478175887)
      ·
        refine ⟨10762553496442802217263831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7175035664295201478175887 10762553496442802217263831)
        ·
          refine ⟨16143830244664203325895747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10762553496442802217263831 16143830244664203325895747)
          ·
            refine ⟨24215745366996304988843621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16143830244664203325895747 24215745366996304988843621)
            ·
              refine ⟨4540452256311807185408179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24215745366996304988843621 4540452256311807185408179)
              ·
                refine ⟨6810678384467710778112269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4540452256311807185408179 6810678384467710778112269)
                ·
                  refine ⟨2554004394175391541792101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6810678384467710778112269 2554004394175391541792101)
                  ·
                    refine ⟨478875823907885914086019, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2554004394175391541792101 478875823907885914086019)
                    ·
                      rfl

theorem cell23_2797822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 4, 1, 3, 4].length) (baseStart_2797822 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2797822 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2797822 prefixEnd_2797822 := by exact prefixLift 2797822
  have htrace : WordTrace (prefixWord ++ tailWord_2797822) baseStart_2797822 baseEnd_2797822 := by
    simpa [prefixWord, tailWord_2797822, baseEnd_2797822] using wordTrace_append hprefix tailTrace_2797822
  have hstable : (prefixWord ++ tailWord_2797822).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2797822).length < 2 ^ (prefixWord ++ tailWord_2797822).sum := by decide
  have hdescent : baseEnd_2797822 < baseStart_2797822 := by decide
  rcases family_descends (prefixWord ++ tailWord_2797822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2797835 : List Nat := [1, 1, 1, 1, 5, 2, 5, 1, 6]
def baseStart_2797835 : Nat := 118140960795 + 2797835 * 2 ^ 59
def prefixEnd_2797835 : Nat := 4983230072969 + 3 ^ 40 * 2797835 * 2
def baseEnd_2797835 : Nat := 159626016330240687932833

theorem tailTrace_2797835 : CollatzResearch.WordTrace tailWord_2797835 prefixEnd_2797835 159626016330240687932833 := by
  unfold tailWord_2797835
  simp only [CollatzResearch.WordTrace]
  refine ⟨102045425818929102020946959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68030283879286068013964639 102045425818929102020946959)
  ·
    refine ⟨153068138728393653031420439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102045425818929102020946959 153068138728393653031420439)
    ·
      refine ⟨229602208092590479547130659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 153068138728393653031420439 229602208092590479547130659)
      ·
        refine ⟨344403312138885719320695989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 229602208092590479547130659 344403312138885719320695989)
        ·
          refine ⟨32287810513020536186315249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 344403312138885719320695989 32287810513020536186315249)
          ·
            refine ⟨24215857884765402139736437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32287810513020536186315249 24215857884765402139736437)
            ·
              refine ⟨2270236676696756450600291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 24215857884765402139736437 2270236676696756450600291)
              ·
                refine ⟨3405355015045134675900437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2270236676696756450600291 3405355015045134675900437)
                ·
                  refine ⟨159626016330240687932833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3405355015045134675900437 159626016330240687932833)
                  ·
                    rfl

theorem cell23_2797835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 5, 1, 6].length) (baseStart_2797835 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2797835 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2797835 prefixEnd_2797835 := by exact prefixLift 2797835
  have htrace : WordTrace (prefixWord ++ tailWord_2797835) baseStart_2797835 baseEnd_2797835 := by
    simpa [prefixWord, tailWord_2797835, baseEnd_2797835] using wordTrace_append hprefix tailTrace_2797835
  have hstable : (prefixWord ++ tailWord_2797835).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2797835).length < 2 ^ (prefixWord ++ tailWord_2797835).sum := by decide
  have hdescent : baseEnd_2797835 < baseStart_2797835 := by decide
  rcases family_descends (prefixWord ++ tailWord_2797835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2797838 : List Nat := [4, 1, 1, 2, 1, 2, 1, 2, 1, 2, 6]
def baseStart_2797838 : Nat := 118140960795 + 2797838 * 2 ^ 59
def prefixEnd_2797838 : Nat := 4983230072969 + 3 ^ 40 * 2797838 * 2
def baseEnd_2797838 : Nat := 1436635687414129679657983

theorem tailTrace_2797838 : CollatzResearch.WordTrace tailWord_2797838 prefixEnd_2797838 1436635687414129679657983 := by
  unfold tailWord_2797838
  simp only [CollatzResearch.WordTrace]
  refine ⟨12755691904739779191663271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 68030356825278822355537445 12755691904739779191663271)
  ·
    refine ⟨19133537857109668787494907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12755691904739779191663271 19133537857109668787494907)
    ·
      refine ⟨28700306785664503181242361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19133537857109668787494907 28700306785664503181242361)
      ·
        refine ⟨21525230089248377385931771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28700306785664503181242361 21525230089248377385931771)
        ·
          refine ⟨32287845133872566078897657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21525230089248377385931771 32287845133872566078897657)
          ·
            refine ⟨24215883850404424559173243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32287845133872566078897657 24215883850404424559173243)
            ·
              refine ⟨36323825775606636838759865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24215883850404424559173243 36323825775606636838759865)
              ·
                refine ⟨27242869331704977629069899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36323825775606636838759865 27242869331704977629069899)
                ·
                  refine ⟨40864303997557466443604849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27242869331704977629069899 40864303997557466443604849)
                  ·
                    refine ⟨30648227998168099832703637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 40864303997557466443604849 30648227998168099832703637)
                    ·
                      refine ⟨1436635687414129679657983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 30648227998168099832703637 1436635687414129679657983)
                      ·
                        rfl

theorem cell23_2797838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 1, 2, 1, 2, 6].length) (baseStart_2797838 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2797838 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2797838 prefixEnd_2797838 := by exact prefixLift 2797838
  have htrace : WordTrace (prefixWord ++ tailWord_2797838) baseStart_2797838 baseEnd_2797838 := by
    simpa [prefixWord, tailWord_2797838, baseEnd_2797838] using wordTrace_append hprefix tailTrace_2797838
  have hstable : (prefixWord ++ tailWord_2797838).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2797838).length < 2 ^ (prefixWord ++ tailWord_2797838).sum := by decide
  have hdescent : baseEnd_2797838 < baseStart_2797838 := by decide
  rcases family_descends (prefixWord ++ tailWord_2797838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2797888 : List Nat := [2, 1, 1, 2, 2, 1, 2, 3, 3, 1, 5]
def baseStart_2797888 : Nat := 118140960795 + 2797888 * 2 ^ 59
def prefixEnd_2797888 : Nat := 4983230072969 + 3 ^ 40 * 2797888 * 2
def baseEnd_2797888 : Nat := 1436661361446854484032753

theorem tailTrace_2797888 : CollatzResearch.WordTrace tailWord_2797888 prefixEnd_2797888 1436661361446854484032753 := by
  unfold tailWord_2797888
  simp only [CollatzResearch.WordTrace]
  refine ⟨51023679443868546036313159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68031572591824728048417545 51023679443868546036313159)
  ·
    refine ⟨76535519165802819054469739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51023679443868546036313159 76535519165802819054469739)
    ·
      refine ⟨114803278748704228581704609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76535519165802819054469739 114803278748704228581704609)
      ·
        refine ⟨86102459061528171436278457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 114803278748704228581704609 86102459061528171436278457)
        ·
          refine ⟨64576844296146128577208843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 86102459061528171436278457 64576844296146128577208843)
          ·
            refine ⟨96865266444219192865813265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64576844296146128577208843 96865266444219192865813265)
            ·
              refine ⟨72648949833164394649359949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 96865266444219192865813265 72648949833164394649359949)
              ·
                refine ⟨27243356187436647993509981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 72648949833164394649359949 27243356187436647993509981)
                ·
                  refine ⟨10216258570288742997566243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27243356187436647993509981 10216258570288742997566243)
                  ·
                    refine ⟨15324387855433114496349365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10216258570288742997566243 15324387855433114496349365)
                    ·
                      refine ⟨1436661361446854484032753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15324387855433114496349365 1436661361446854484032753)
                      ·
                        rfl

theorem cell23_2797888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 3, 3, 1, 5].length) (baseStart_2797888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2797888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2797888 prefixEnd_2797888 := by exact prefixLift 2797888
  have htrace : WordTrace (prefixWord ++ tailWord_2797888) baseStart_2797888 baseEnd_2797888 := by
    simpa [prefixWord, tailWord_2797888, baseEnd_2797888] using wordTrace_append hprefix tailTrace_2797888
  have hstable : (prefixWord ++ tailWord_2797888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2797888).length < 2 ^ (prefixWord ++ tailWord_2797888).sum := by decide
  have hdescent : baseEnd_2797888 < baseStart_2797888 := by decide
  rcases family_descends (prefixWord ++ tailWord_2797888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2797916 : List Nat := [2, 2, 4, 3, 1, 1, 3, 1, 1, 5]
def baseStart_2797916 : Nat := 118140960795 + 2797916 * 2 ^ 59
def prefixEnd_2797916 : Nat := 4983230072969 + 3 ^ 40 * 2797916 * 2
def baseEnd_2797916 : Nat := 478891912968393458160875

theorem tailTrace_2797916 : CollatzResearch.WordTrace tailWord_2797916 prefixEnd_2797916 478891912968393458160875 := by
  unfold tailWord_2797916
  simp only [CollatzResearch.WordTrace]
  refine ⟨51024190065817826427322801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68032253421090435236430401 51024190065817826427322801)
  ·
    refine ⟨38268142549363369820492101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51024190065817826427322801 38268142549363369820492101)
    ·
      refine ⟨7175276728005631841342269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 38268142549363369820492101 7175276728005631841342269)
      ·
        refine ⟨2690728773002111940503351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7175276728005631841342269 2690728773002111940503351)
        ·
          refine ⟨4036093159503167910755027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2690728773002111940503351 4036093159503167910755027)
          ·
            refine ⟨6054139739254751866132541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4036093159503167910755027 6054139739254751866132541)
            ·
              refine ⟨2270302402220531949799703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6054139739254751866132541 2270302402220531949799703)
              ·
                refine ⟨3405453603330797924699555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2270302402220531949799703 3405453603330797924699555)
                ·
                  refine ⟨5108180404996196887049333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3405453603330797924699555 5108180404996196887049333)
                  ·
                    refine ⟨478891912968393458160875, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5108180404996196887049333 478891912968393458160875)
                    ·
                      rfl

theorem cell23_2797916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 1, 3, 1, 1, 5].length) (baseStart_2797916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2797916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2797916 prefixEnd_2797916 := by exact prefixLift 2797916
  have htrace : WordTrace (prefixWord ++ tailWord_2797916) baseStart_2797916 baseEnd_2797916 := by
    simpa [prefixWord, tailWord_2797916, baseEnd_2797916] using wordTrace_append hprefix tailTrace_2797916
  have hstable : (prefixWord ++ tailWord_2797916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2797916).length < 2 ^ (prefixWord ++ tailWord_2797916).sum := by decide
  have hdescent : baseEnd_2797916 < baseStart_2797916 := by decide
  rcases family_descends (prefixWord ++ tailWord_2797916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2797922 : List Nat := [3, 3, 2, 1, 1, 2, 3, 1, 1, 1, 5]
def baseStart_2797922 : Nat := 118140960795 + 2797922 * 2 ^ 59
def prefixEnd_2797922 : Nat := 4983230072969 + 3 ^ 40 * 2797922 * 2
def baseEnd_2797922 : Nat := 1436678819789107351007597

theorem tailTrace_2797922 : CollatzResearch.WordTrace tailWord_2797922 prefixEnd_2797922 1436678819789107351007597 := by
  unfold tailWord_2797922
  simp only [CollatzResearch.WordTrace]
  refine ⟨25512149742403478969841005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68032399313075943919576013 25512149742403478969841005)
  ·
    refine ⟨9567056153401304613690377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25512149742403478969841005 9567056153401304613690377)
    ·
      refine ⟨7175292115050978460267783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9567056153401304613690377 7175292115050978460267783)
      ·
        refine ⟨10762938172576467690401675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7175292115050978460267783 10762938172576467690401675)
        ·
          refine ⟨16144407258864701535602513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10762938172576467690401675 16144407258864701535602513)
          ·
            refine ⟨12108305444148526151701885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16144407258864701535602513 12108305444148526151701885)
            ·
              refine ⟨4540614541555697306888207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12108305444148526151701885 4540614541555697306888207)
              ·
                refine ⟨6810921812333545960332311, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4540614541555697306888207 6810921812333545960332311)
                ·
                  refine ⟨10216382718500318940498467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6810921812333545960332311 10216382718500318940498467)
                  ·
                    refine ⟨15324574077750478410747701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10216382718500318940498467 15324574077750478410747701)
                    ·
                      refine ⟨1436678819789107351007597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15324574077750478410747701 1436678819789107351007597)
                      ·
                        rfl

theorem cell23_2797922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 3, 1, 1, 1, 5].length) (baseStart_2797922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2797922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2797922 prefixEnd_2797922 := by exact prefixLift 2797922
  have htrace : WordTrace (prefixWord ++ tailWord_2797922) baseStart_2797922 baseEnd_2797922 := by
    simpa [prefixWord, tailWord_2797922, baseEnd_2797922] using wordTrace_append hprefix tailTrace_2797922
  have hstable : (prefixWord ++ tailWord_2797922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2797922).length < 2 ^ (prefixWord ++ tailWord_2797922).sum := by decide
  have hdescent : baseEnd_2797922 < baseStart_2797922 := by decide
  rcases family_descends (prefixWord ++ tailWord_2797922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2797936 : List Nat := [2, 1, 1, 1, 4, 4, 1, 4, 1, 2, 2]
def baseStart_2797936 : Nat := 118140960795 + 2797936 * 2 ^ 59
def prefixEnd_2797936 : Nat := 4983230072969 + 3 ^ 40 * 2797936 * 2
def baseEnd_2797936 : Nat := 1436686008518270296232533

theorem tailTrace_2797936 : CollatzResearch.WordTrace tailWord_2797936 prefixEnd_2797936 1436686008518270296232533 := by
  unfold tailWord_2797936
  simp only [CollatzResearch.WordTrace]
  refine ⟨51024554795781598135186831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68032739727708797513582441 51024554795781598135186831)
  ·
    refine ⟨76536832193672397202780247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51024554795781598135186831 76536832193672397202780247)
    ·
      refine ⟨114805248290508595804170371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76536832193672397202780247 114805248290508595804170371)
      ·
        refine ⟨172207872435762893706255557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114805248290508595804170371 172207872435762893706255557)
        ·
          refine ⟨32288976081705542569922917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 172207872435762893706255557 32288976081705542569922917)
          ·
            refine ⟨6054183015319789231860547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 32288976081705542569922917 6054183015319789231860547)
            ·
              refine ⟨9081274522979683847790821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6054183015319789231860547 9081274522979683847790821)
              ·
                refine ⟨1702738973058690721460779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9081274522979683847790821 1702738973058690721460779)
                ·
                  refine ⟨2554108459588036082191169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1702738973058690721460779 2554108459588036082191169)
                  ·
                    refine ⟨1915581344691027061643377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2554108459588036082191169 1915581344691027061643377)
                    ·
                      refine ⟨1436686008518270296232533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1915581344691027061643377 1436686008518270296232533)
                      ·
                        rfl

theorem cell23_2797936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 4, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 4, 1, 4, 1, 2, 2].length) (baseStart_2797936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2797936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2797936 prefixEnd_2797936 := by exact prefixLift 2797936
  have htrace : WordTrace (prefixWord ++ tailWord_2797936) baseStart_2797936 baseEnd_2797936 := by
    simpa [prefixWord, tailWord_2797936, baseEnd_2797936] using wordTrace_append hprefix tailTrace_2797936
  have hstable : (prefixWord ++ tailWord_2797936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2797936).length < 2 ^ (prefixWord ++ tailWord_2797936).sum := by decide
  have hdescent : baseEnd_2797936 < baseStart_2797936 := by decide
  rcases family_descends (prefixWord ++ tailWord_2797936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2798009 : List Nat := [1, 2, 1, 4, 3, 1, 3, 1, 1, 4, 2]
def baseStart_2798009 : Nat := 118140960795 + 2798009 * 2 ^ 59
def prefixEnd_2798009 : Nat := 4983230072969 + 3 ^ 40 * 2798009 * 2
def baseEnd_2798009 : Nat := 1436723492606048510619697

theorem tailTrace_2798009 : CollatzResearch.WordTrace tailWord_2798009 prefixEnd_2798009 1436723492606048510619697 := by
  unfold tailWord_2798009
  simp only [CollatzResearch.WordTrace]
  refine ⟨102051772120298729737781081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68034514746865819825187387 102051772120298729737781081)
  ·
    refine ⟨76538829090224047303335811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102051772120298729737781081 76538829090224047303335811)
    ·
      refine ⟨114808243635336070955003717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76538829090224047303335811 114808243635336070955003717)
      ·
        refine ⟨21526545681625513304063197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 114808243635336070955003717 21526545681625513304063197)
        ·
          refine ⟨8072454630609567489023699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21526545681625513304063197 8072454630609567489023699)
          ·
            refine ⟨12108681945914351233535549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8072454630609567489023699 12108681945914351233535549)
            ·
              refine ⟨4540755729717881712575831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12108681945914351233535549 4540755729717881712575831)
              ·
                refine ⟨6811133594576822568863747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4540755729717881712575831 6811133594576822568863747)
                ·
                  refine ⟨10216700391865233853295621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6811133594576822568863747 10216700391865233853295621)
                  ·
                    refine ⟨1915631323474731347492929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10216700391865233853295621 1915631323474731347492929)
                    ·
                      refine ⟨1436723492606048510619697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1915631323474731347492929 1436723492606048510619697)
                      ·
                        rfl

theorem cell23_2798009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 3, 1, 1, 4, 2].length) (baseStart_2798009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2798009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2798009 prefixEnd_2798009 := by exact prefixLift 2798009
  have htrace : WordTrace (prefixWord ++ tailWord_2798009) baseStart_2798009 baseEnd_2798009 := by
    simpa [prefixWord, tailWord_2798009, baseEnd_2798009] using wordTrace_append hprefix tailTrace_2798009
  have hstable : (prefixWord ++ tailWord_2798009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2798009).length < 2 ^ (prefixWord ++ tailWord_2798009).sum := by decide
  have hdescent : baseEnd_2798009 < baseStart_2798009 := by decide
  rcases family_descends (prefixWord ++ tailWord_2798009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2798025 : List Nat := [1, 2, 1, 1, 2, 1, 4, 2, 1, 5, 3]
def baseStart_2798025 : Nat := 118140960795 + 2798025 * 2 ^ 59
def prefixEnd_2798025 : Nat := 4983230072969 + 3 ^ 40 * 2798025 * 2
def baseEnd_2798025 : Nat := 1436731708296520448019623

theorem tailTrace_2798025 : CollatzResearch.WordTrace tailWord_2798025 prefixEnd_2798025 1436731708296520448019623 := by
  unfold tailWord_2798025
  simp only [CollatzResearch.WordTrace]
  refine ⟨102052355688240764470363529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68034903792160509646909019 102052355688240764470363529)
  ·
    refine ⟨76539266766180573352772647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102052355688240764470363529 76539266766180573352772647)
    ·
      refine ⟨114808900149270860029158971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76539266766180573352772647 114808900149270860029158971)
      ·
        refine ⟨172213350223906290043738457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114808900149270860029158971 172213350223906290043738457)
        ·
          refine ⟨129160012667929717532803843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 172213350223906290043738457 129160012667929717532803843)
          ·
            refine ⟨193740019001894576299205765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 129160012667929717532803843 193740019001894576299205765)
            ·
              refine ⟨36326253562855233056101081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 193740019001894576299205765 36326253562855233056101081)
              ·
                refine ⟨27244690172141424792075811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36326253562855233056101081 27244690172141424792075811)
                ·
                  refine ⟨40867035258212137188113717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27244690172141424792075811 40867035258212137188113717)
                  ·
                    refine ⟨3831284555457387861385661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 40867035258212137188113717 3831284555457387861385661)
                    ·
                      refine ⟨1436731708296520448019623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3831284555457387861385661 1436731708296520448019623)
                      ·
                        rfl

theorem cell23_2798025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 4, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 4, 2, 1, 5, 3].length) (baseStart_2798025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2798025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2798025 prefixEnd_2798025 := by exact prefixLift 2798025
  have htrace : WordTrace (prefixWord ++ tailWord_2798025) baseStart_2798025 baseEnd_2798025 := by
    simpa [prefixWord, tailWord_2798025, baseEnd_2798025] using wordTrace_append hprefix tailTrace_2798025
  have hstable : (prefixWord ++ tailWord_2798025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2798025).length < 2 ^ (prefixWord ++ tailWord_2798025).sum := by decide
  have hdescent : baseEnd_2798025 < baseStart_2798025 := by decide
  rcases family_descends (prefixWord ++ tailWord_2798025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2798049 : List Nat := [1, 2, 3, 1, 2, 2, 5, 2, 5]
def baseStart_2798049 : Nat := 118140960795 + 2798049 * 2 ^ 59
def prefixEnd_2798049 : Nat := 4983230072969 + 3 ^ 40 * 2798049 * 2
def baseEnd_2798049 : Nat := 159638225759136483791057

theorem tailTrace_2798049 : CollatzResearch.WordTrace tailWord_2798049 prefixEnd_2798049 159638225759136483791057 := by
  unfold tailWord_2798049
  simp only [CollatzResearch.WordTrace]
  refine ⟨102053231040153816569237201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68035487360102544379491467 102053231040153816569237201)
  ·
    refine ⟨76539923280115362426927901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102053231040153816569237201 76539923280115362426927901)
    ·
      refine ⟨28702471230043260910097963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 76539923280115362426927901 28702471230043260910097963)
      ·
        refine ⟨43053706845064891365146945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28702471230043260910097963 43053706845064891365146945)
        ·
          refine ⟨32290280133798668523860209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43053706845064891365146945 32290280133798668523860209)
          ·
            refine ⟨24217710100349001392895157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32290280133798668523860209 24217710100349001392895157)
            ·
              refine ⟨2270410321907718880583921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 24217710100349001392895157 2270410321907718880583921)
              ·
                refine ⟨1702807741430789160437941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2270410321907718880583921 1702807741430789160437941)
                ·
                  refine ⟨159638225759136483791057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1702807741430789160437941 159638225759136483791057)
                  ·
                    rfl

theorem cell23_2798049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 5, 2, 5].length) (baseStart_2798049 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2798049 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2798049 prefixEnd_2798049 := by exact prefixLift 2798049
  have htrace : WordTrace (prefixWord ++ tailWord_2798049) baseStart_2798049 baseEnd_2798049 := by
    simpa [prefixWord, tailWord_2798049, baseEnd_2798049] using wordTrace_append hprefix tailTrace_2798049
  have hstable : (prefixWord ++ tailWord_2798049).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2798049).length < 2 ^ (prefixWord ++ tailWord_2798049).sum := by decide
  have hdescent : baseEnd_2798049 < baseStart_2798049 := by decide
  rcases family_descends (prefixWord ++ tailWord_2798049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2798126 : List Nat := [4, 1, 3, 1, 3, 1, 1, 2, 3, 4]
def baseStart_2798126 : Nat := 118140960795 + 2798126 * 2 ^ 59
def prefixEnd_2798126 : Nat := 4983230072969 + 3 ^ 40 * 2798126 * 2
def baseEnd_2798126 : Nat := 478927856614208184285553

theorem tailTrace_2798126 : CollatzResearch.WordTrace tailWord_2798126 prefixEnd_2798126 478927856614208184285553 := by
  unfold tailWord_2798126
  simp only [CollatzResearch.WordTrace]
  refine ⟨12757004932609357339973779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 68037359640583239146526821 12757004932609357339973779)
  ·
    refine ⟨19135507398914036009960669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12757004932609357339973779 19135507398914036009960669)
    ·
      refine ⟨7175815274592763503735251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19135507398914036009960669 7175815274592763503735251)
      ·
        refine ⟨10763722911889145255602877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7175815274592763503735251 10763722911889145255602877)
        ·
          refine ⟨4036396091958429470851079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10763722911889145255602877 4036396091958429470851079)
          ·
            refine ⟨6054594137937644206276619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4036396091958429470851079 6054594137937644206276619)
            ·
              refine ⟨9081891206906466309414929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6054594137937644206276619 9081891206906466309414929)
              ·
                refine ⟨6811418405179849732061197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9081891206906466309414929 6811418405179849732061197)
                ·
                  refine ⟨2554281901942443649522949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6811418405179849732061197 2554281901942443649522949)
                  ·
                    refine ⟨478927856614208184285553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2554281901942443649522949 478927856614208184285553)
                    ·
                      rfl

theorem cell23_2798126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 1, 1, 2, 3, 4].length) (baseStart_2798126 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2798126 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2798126 prefixEnd_2798126 := by exact prefixLift 2798126
  have htrace : WordTrace (prefixWord ++ tailWord_2798126) baseStart_2798126 baseEnd_2798126 := by
    simpa [prefixWord, tailWord_2798126, baseEnd_2798126] using wordTrace_append hprefix tailTrace_2798126
  have hstable : (prefixWord ++ tailWord_2798126).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2798126).length < 2 ^ (prefixWord ++ tailWord_2798126).sum := by decide
  have hdescent : baseEnd_2798126 < baseStart_2798126 := by decide
  rcases family_descends (prefixWord ++ tailWord_2798126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2798159 : List Nat := [1, 1, 2, 1, 1, 2, 4, 4, 2, 3, 2]
def baseStart_2798159 : Nat := 118140960795 + 2798159 * 2 ^ 59
def prefixEnd_2798159 : Nat := 4983230072969 + 3 ^ 40 * 2798159 * 2
def baseEnd_2798159 : Nat := 1436800514704222923744007

theorem tailTrace_2798159 : CollatzResearch.WordTrace tailWord_2798159 prefixEnd_2798159 1436800514704222923744007 := by
  unfold tailWord_2798159
  simp only [CollatzResearch.WordTrace]
  refine ⟨102057243069755305355741531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68038162046503536903827687 102057243069755305355741531)
  ·
    refine ⟨153085864604632958033612297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102057243069755305355741531 153085864604632958033612297)
    ·
      refine ⟨114814398453474718525209223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 153085864604632958033612297 114814398453474718525209223)
      ·
        refine ⟨172221597680212077787813835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114814398453474718525209223 172221597680212077787813835)
        ·
          refine ⟨258332396520318116681720753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 172221597680212077787813835 258332396520318116681720753)
          ·
            refine ⟨193749297390238587511290565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 258332396520318116681720753 193749297390238587511290565)
            ·
              refine ⟨36327993260669735158366981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 193749297390238587511290565 36327993260669735158366981)
              ·
                refine ⟨6811498736375575342193809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 36327993260669735158366981 6811498736375575342193809)
                ·
                  refine ⟨5108624052281681506645357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6811498736375575342193809 5108624052281681506645357)
                  ·
                    refine ⟨1915734019605630564992009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5108624052281681506645357 1915734019605630564992009)
                    ·
                      refine ⟨1436800514704222923744007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1915734019605630564992009 1436800514704222923744007)
                      ·
                        rfl

theorem cell23_2798159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 4, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 4, 4, 2, 3, 2].length) (baseStart_2798159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2798159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2798159 prefixEnd_2798159 := by exact prefixLift 2798159
  have htrace : WordTrace (prefixWord ++ tailWord_2798159) baseStart_2798159 baseEnd_2798159 := by
    simpa [prefixWord, tailWord_2798159, baseEnd_2798159] using wordTrace_append hprefix tailTrace_2798159
  have hstable : (prefixWord ++ tailWord_2798159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2798159).length < 2 ^ (prefixWord ++ tailWord_2798159).sum := by decide
  have hdescent : baseEnd_2798159 < baseStart_2798159 := by decide
  rcases family_descends (prefixWord ++ tailWord_2798159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2798209 : List Nat := [1, 2, 4, 2, 1, 1, 4, 1, 1, 1, 5]
def baseStart_2798209 : Nat := 118140960795 + 2798209 * 2 ^ 59
def prefixEnd_2798209 : Nat := 4983230072969 + 3 ^ 40 * 2798209 * 2
def baseEnd_2798209 : Nat := 1436826188736947728118777

theorem tailTrace_2798209 : CollatzResearch.WordTrace tailWord_2798209 prefixEnd_2798209 1436826188736947728118777 := by
  unfold tailWord_2798209
  simp only [CollatzResearch.WordTrace]
  refine ⟨102059066719574163895061681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68039377813049442596707787 102059066719574163895061681)
  ·
    refine ⟨76544300039680622921296261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102059066719574163895061681 76544300039680622921296261)
    ·
      refine ⟨14352056257440116797743049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 76544300039680622921296261 14352056257440116797743049)
      ·
        refine ⟨10764042193080087598307287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14352056257440116797743049 10764042193080087598307287)
        ·
          refine ⟨16146063289620131397460931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10764042193080087598307287 16146063289620131397460931)
          ·
            refine ⟨24219094934430197096191397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16146063289620131397460931 24219094934430197096191397)
            ·
              refine ⟨4541080300205661955535887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24219094934430197096191397 4541080300205661955535887)
              ·
                refine ⟨6811620450308492933303831, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4541080300205661955535887 6811620450308492933303831)
                ·
                  refine ⟨10217430675462739399955747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6811620450308492933303831 10217430675462739399955747)
                  ·
                    refine ⟨15326146013194109099933621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10217430675462739399955747 15326146013194109099933621)
                    ·
                      refine ⟨1436826188736947728118777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15326146013194109099933621 1436826188736947728118777)
                      ·
                        rfl

theorem cell23_2798209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 4, 1, 1, 1, 5].length) (baseStart_2798209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2798209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2798209 prefixEnd_2798209 := by exact prefixLift 2798209
  have htrace : WordTrace (prefixWord ++ tailWord_2798209) baseStart_2798209 baseEnd_2798209 := by
    simpa [prefixWord, tailWord_2798209, baseEnd_2798209] using wordTrace_append hprefix tailTrace_2798209
  have hstable : (prefixWord ++ tailWord_2798209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2798209).length < 2 ^ (prefixWord ++ tailWord_2798209).sum := by decide
  have hdescent : baseEnd_2798209 < baseStart_2798209 := by decide
  rcases family_descends (prefixWord ++ tailWord_2798209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2798212 : List Nat := [2, 3, 2, 1, 3, 1, 11]
def baseStart_2798212 : Nat := 118140960795 + 2798212 * 2 ^ 59
def prefixEnd_2798212 : Nat := 4983230072969 + 3 ^ 40 * 2798212 * 2
def baseEnd_2798212 : Nat := 17738613940480385387423

theorem tailTrace_2798212 : CollatzResearch.WordTrace tailWord_2798212 prefixEnd_2798212 17738613940480385387423 := by
  unfold tailWord_2798212
  simp only [CollatzResearch.WordTrace]
  refine ⟨51029588069281647703710445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68039450759042196938280593 51029588069281647703710445)
  ·
    refine ⟨19136095525980617888891417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51029588069281647703710445 19136095525980617888891417)
    ·
      refine ⟨14352071644485463416668563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19136095525980617888891417 14352071644485463416668563)
      ·
        refine ⟨21528107466728195125002845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14352071644485463416668563 21528107466728195125002845)
        ·
          refine ⟨8073040300023073171876067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21528107466728195125002845 8073040300023073171876067)
          ·
            refine ⟨12109560450034609757814101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8073040300023073171876067 12109560450034609757814101)
            ·
              refine ⟨17738613940480385387423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 12109560450034609757814101 17738613940480385387423)
              ·
                rfl

theorem cell23_2798212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 11].length) (baseStart_2798212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2798212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2798212 prefixEnd_2798212 := by exact prefixLift 2798212
  have htrace : WordTrace (prefixWord ++ tailWord_2798212) baseStart_2798212 baseEnd_2798212 := by
    simpa [prefixWord, tailWord_2798212, baseEnd_2798212] using wordTrace_append hprefix tailTrace_2798212
  have hstable : (prefixWord ++ tailWord_2798212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2798212).length < 2 ^ (prefixWord ++ tailWord_2798212).sum := by decide
  have hdescent : baseEnd_2798212 < baseStart_2798212 := by decide
  rcases family_descends (prefixWord ++ tailWord_2798212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2798232 : List Nat := [2, 1, 2, 4, 1, 1, 1, 1, 2, 2, 6]
def baseStart_2798232 : Nat := 118140960795 + 2798232 * 2 ^ 59
def prefixEnd_2798232 : Nat := 4983230072969 + 3 ^ 40 * 2798232 * 2
def baseEnd_2798232 : Nat := 1436837998792001138131171

theorem tailTrace_2798232 : CollatzResearch.WordTrace tailWord_2798232 prefixEnd_2798232 1436837998792001138131171 := by
  unfold tailWord_2798232
  simp only [CollatzResearch.WordTrace]
  refine ⟨51029952799245419411574475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68039937065660559215432633 51029952799245419411574475)
  ·
    refine ⟨76544929198868129117361713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51029952799245419411574475 76544929198868129117361713)
    ·
      refine ⟨57408696899151096838021285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76544929198868129117361713 57408696899151096838021285)
      ·
        refine ⟨10764130668590830657128991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 57408696899151096838021285 10764130668590830657128991)
        ·
          refine ⟨16146196002886245985693487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10764130668590830657128991 16146196002886245985693487)
          ·
            refine ⟨24219294004329368978540231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16146196002886245985693487 24219294004329368978540231)
            ·
              refine ⟨36328941006494053467810347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24219294004329368978540231 36328941006494053467810347)
              ·
                refine ⟨54493411509741080201715521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36328941006494053467810347 54493411509741080201715521)
                ·
                  refine ⟨40870058632305810151286641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 54493411509741080201715521 40870058632305810151286641)
                  ·
                    refine ⟨30652543974229357613464981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 40870058632305810151286641 30652543974229357613464981)
                    ·
                      refine ⟨1436837998792001138131171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 30652543974229357613464981 1436837998792001138131171)
                      ·
                        rfl

theorem cell23_2798232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 1, 1, 2, 2, 6].length) (baseStart_2798232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2798232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2798232 prefixEnd_2798232 := by exact prefixLift 2798232
  have htrace : WordTrace (prefixWord ++ tailWord_2798232) baseStart_2798232 baseEnd_2798232 := by
    simpa [prefixWord, tailWord_2798232, baseEnd_2798232] using wordTrace_append hprefix tailTrace_2798232
  have hstable : (prefixWord ++ tailWord_2798232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2798232).length < 2 ^ (prefixWord ++ tailWord_2798232).sum := by decide
  have hdescent : baseEnd_2798232 < baseStart_2798232 := by decide
  rcases family_descends (prefixWord ++ tailWord_2798232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2798296 : List Nat := [2, 1, 2, 2, 3, 2, 1, 3, 1, 4, 2]
def baseStart_2798296 : Nat := 118140960795 + 2798296 * 2 ^ 59
def prefixEnd_2798296 : Nat := 4983230072969 + 3 ^ 40 * 2798296 * 2
def baseEnd_2798296 : Nat := 1436870861553888887730877

theorem tailTrace_2798296 : CollatzResearch.WordTrace tailWord_2798296 prefixEnd_2798296 1436870861553888887730877 := by
  unfold tailWord_2798296
  simp only [CollatzResearch.WordTrace]
  refine ⟨51031119935129488876739371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68041493246839318502319161 51031119935129488876739371)
  ·
    refine ⟨76546679902694233315109057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51031119935129488876739371 76546679902694233315109057)
    ·
      refine ⟨57410009927020674986331793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76546679902694233315109057 57410009927020674986331793)
      ·
        refine ⟨43057507445265506239748845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57410009927020674986331793 43057507445265506239748845)
        ·
          refine ⟨16146565291974564839905817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43057507445265506239748845 16146565291974564839905817)
          ·
            refine ⟨12109923968980923629929363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16146565291974564839905817 12109923968980923629929363)
            ·
              refine ⟨18164885953471385444894045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12109923968980923629929363 18164885953471385444894045)
              ·
                refine ⟨6811832232551769541835267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18164885953471385444894045 6811832232551769541835267)
                ·
                  refine ⟨10217748348827654312752901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6811832232551769541835267 10217748348827654312752901)
                  ·
                    refine ⟨1915827815405185183641169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10217748348827654312752901 1915827815405185183641169)
                    ·
                      refine ⟨1436870861553888887730877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1915827815405185183641169 1436870861553888887730877)
                      ·
                        rfl

theorem cell23_2798296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 1, 3, 1, 4, 2].length) (baseStart_2798296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2798296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2798296 prefixEnd_2798296 := by exact prefixLift 2798296
  have htrace : WordTrace (prefixWord ++ tailWord_2798296) baseStart_2798296 baseEnd_2798296 := by
    simpa [prefixWord, tailWord_2798296, baseEnd_2798296] using wordTrace_append hprefix tailTrace_2798296
  have hstable : (prefixWord ++ tailWord_2798296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2798296).length < 2 ^ (prefixWord ++ tailWord_2798296).sum := by decide
  have hdescent : baseEnd_2798296 < baseStart_2798296 := by decide
  rcases family_descends (prefixWord ++ tailWord_2798296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2798324 : List Nat := [2, 6, 1, 1, 2, 2, 1, 2, 2, 1, 3]
def baseStart_2798324 : Nat := 118140960795 + 2798324 * 2 ^ 59
def prefixEnd_2798324 : Nat := 4983230072969 + 3 ^ 40 * 2798324 * 2
def baseEnd_2798324 : Nat := 1436885239012214778180749

theorem tailTrace_2798324 : CollatzResearch.WordTrace tailWord_2798324 prefixEnd_2798324 1436885239012214778180749 := by
  unfold tailWord_2798324
  simp only [CollatzResearch.WordTrace]
  refine ⟨51031630557078769267749013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68042174076105025690332017 51031630557078769267749013)
  ·
    refine ⟨2392107682363067309425735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 51031630557078769267749013 2392107682363067309425735)
    ·
      refine ⟨3588161523544600964138603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2392107682363067309425735 3588161523544600964138603)
      ·
        refine ⟨5382242285316901446207905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3588161523544600964138603 5382242285316901446207905)
        ·
          refine ⟨4036681713987676084655929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5382242285316901446207905 4036681713987676084655929)
          ·
            refine ⟨3027511285490757063491947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4036681713987676084655929 3027511285490757063491947)
            ·
              refine ⟨4541266928236135595237921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3027511285490757063491947 4541266928236135595237921)
              ·
                refine ⟨3405950196177101696428441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4541266928236135595237921 3405950196177101696428441)
                ·
                  refine ⟨2554462647132826272321331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3405950196177101696428441 2554462647132826272321331)
                  ·
                    refine ⟨3831693970699239408481997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2554462647132826272321331 3831693970699239408481997)
                    ·
                      refine ⟨1436885239012214778180749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3831693970699239408481997 1436885239012214778180749)
                      ·
                        rfl

theorem cell23_2798324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 2, 1, 2, 2, 1, 3].length) (baseStart_2798324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2798324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2798324 prefixEnd_2798324 := by exact prefixLift 2798324
  have htrace : WordTrace (prefixWord ++ tailWord_2798324) baseStart_2798324 baseEnd_2798324 := by
    simpa [prefixWord, tailWord_2798324, baseEnd_2798324] using wordTrace_append hprefix tailTrace_2798324
  have hstable : (prefixWord ++ tailWord_2798324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2798324).length < 2 ^ (prefixWord ++ tailWord_2798324).sum := by decide
  have hdescent : baseEnd_2798324 < baseStart_2798324 := by decide
  rcases family_descends (prefixWord ++ tailWord_2798324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2798369 : List Nat := [1, 2, 3, 2, 1, 2, 1, 3, 1, 3, 4]
def baseStart_2798369 : Nat := 118140960795 + 2798369 * 2 ^ 59
def prefixEnd_2798369 : Nat := 4983230072969 + 3 ^ 40 * 2798369 * 2
def baseEnd_2798369 : Nat := 1436908345641667102118041

theorem tailTrace_2798369 : CollatzResearch.WordTrace tailWord_2798369 prefixEnd_2798369 1436908345641667102118041 := by
  unfold tailWord_2798369
  simp only [CollatzResearch.WordTrace]
  refine ⟨102064902398994511220886161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68043268265996340813924107 102064902398994511220886161)
  ·
    refine ⟨76548676799245883415664621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102064902398994511220886161 76548676799245883415664621)
    ·
      refine ⟨28705753799717206280874233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 76548676799245883415664621 28705753799717206280874233)
      ·
        refine ⟨21529315349787904710655675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28705753799717206280874233 21529315349787904710655675)
        ·
          refine ⟨32293973024681857065983513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21529315349787904710655675 32293973024681857065983513)
          ·
            refine ⟨24220479768511392799487635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32293973024681857065983513 24220479768511392799487635)
            ·
              refine ⟨36330719652767089199231453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24220479768511392799487635 36330719652767089199231453)
              ·
                refine ⟨13624019869787658449711795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36330719652767089199231453 13624019869787658449711795)
                ·
                  refine ⟨20436029804681487674567693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13624019869787658449711795 20436029804681487674567693)
                  ·
                    refine ⟨7663511176755557877962885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20436029804681487674567693 7663511176755557877962885)
                    ·
                      refine ⟨1436908345641667102118041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7663511176755557877962885 1436908345641667102118041)
                      ·
                        rfl

theorem cell23_2798369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 1, 3, 1, 3, 4].length) (baseStart_2798369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2798369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2798369 prefixEnd_2798369 := by exact prefixLift 2798369
  have htrace : WordTrace (prefixWord ++ tailWord_2798369) baseStart_2798369 baseEnd_2798369 := by
    simpa [prefixWord, tailWord_2798369, baseEnd_2798369] using wordTrace_append hprefix tailTrace_2798369
  have hstable : (prefixWord ++ tailWord_2798369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2798369).length < 2 ^ (prefixWord ++ tailWord_2798369).sum := by decide
  have hdescent : baseEnd_2798369 < baseStart_2798369 := by decide
  rcases family_descends (prefixWord ++ tailWord_2798369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2798379 : List Nat := [1, 1, 1, 1, 2, 1, 2, 3, 7, 4]
def baseStart_2798379 : Nat := 118140960795 + 2798379 * 2 ^ 59
def prefixEnd_2798379 : Nat := 4983230072969 + 3 ^ 40 * 2798379 * 2
def baseEnd_2798379 : Nat := 478971160149404020997665

theorem tailTrace_2798379 : CollatzResearch.WordTrace tailWord_2798379 prefixEnd_2798379 478971160149404020997665 := by
  unfold tailWord_2798379
  simp only [CollatzResearch.WordTrace]
  refine ⟨102065267128958282928750191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68043511419305521952500127 102065267128958282928750191)
  ·
    refine ⟨153097900693437424393125287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102065267128958282928750191 153097900693437424393125287)
    ·
      refine ⟨229646851040156136589687931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 153097900693437424393125287 229646851040156136589687931)
      ·
        refine ⟨344470276560234204884531897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 229646851040156136589687931 344470276560234204884531897)
        ·
          refine ⟨258352707420175653663398923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 344470276560234204884531897 258352707420175653663398923)
          ·
            refine ⟨387529061130263480495098385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 258352707420175653663398923 387529061130263480495098385)
            ·
              refine ⟨290646795847697610371323789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 387529061130263480495098385 290646795847697610371323789)
              ·
                refine ⟨108992548442886603889246421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 290646795847697610371323789 108992548442886603889246421)
                ·
                  refine ⟨2554512854130154778654213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 108992548442886603889246421 2554512854130154778654213)
                  ·
                    refine ⟨478971160149404020997665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2554512854130154778654213 478971160149404020997665)
                    ·
                      rfl

theorem cell23_2798379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 3, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 3, 7, 4].length) (baseStart_2798379 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2798379 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2798379 prefixEnd_2798379 := by exact prefixLift 2798379
  have htrace : WordTrace (prefixWord ++ tailWord_2798379) baseStart_2798379 baseEnd_2798379 := by
    simpa [prefixWord, tailWord_2798379, baseEnd_2798379] using wordTrace_append hprefix tailTrace_2798379
  have hstable : (prefixWord ++ tailWord_2798379).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2798379).length < 2 ^ (prefixWord ++ tailWord_2798379).sum := by decide
  have hdescent : baseEnd_2798379 < baseStart_2798379 := by decide
  rcases family_descends (prefixWord ++ tailWord_2798379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2798386 : List Nat := [3, 2, 1, 1, 3, 1, 3, 2, 2, 1, 4]
def baseStart_2798386 : Nat := 118140960795 + 2798386 * 2 ^ 59
def prefixEnd_2798386 : Nat := 4983230072969 + 3 ^ 40 * 2798386 * 2
def baseEnd_2798386 : Nat := 1436917074812793535605463

theorem tailTrace_2798386 : CollatzResearch.WordTrace tailWord_2798386 prefixEnd_2798386 1436917074812793535605463 := by
  unfold tailWord_2798386
  simp only [CollatzResearch.WordTrace]
  refine ⟨25516380609983230781063753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68043681626621948749503341 25516380609983230781063753)
  ·
    refine ⟨19137285457487423085797815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25516380609983230781063753 19137285457487423085797815)
    ·
      refine ⟨28705928186231134628696723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19137285457487423085797815 28705928186231134628696723)
      ·
        refine ⟨43058892279346701943045085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28705928186231134628696723 43058892279346701943045085)
        ·
          refine ⟨16147084604755013228641907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43058892279346701943045085 16147084604755013228641907)
          ·
            refine ⟨24220626907132519842962861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16147084604755013228641907 24220626907132519842962861)
            ·
              refine ⟨9082735090174694941111073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24220626907132519842962861 9082735090174694941111073)
              ·
                refine ⟨6812051317631021205833305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9082735090174694941111073 6812051317631021205833305)
                ·
                  refine ⟨5109038488223265904374979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6812051317631021205833305 5109038488223265904374979)
                  ·
                    refine ⟨7663557732334898856562469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5109038488223265904374979 7663557732334898856562469)
                    ·
                      refine ⟨1436917074812793535605463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7663557732334898856562469 1436917074812793535605463)
                      ·
                        rfl

theorem cell23_2798386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 3, 2, 2, 1, 4].length) (baseStart_2798386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2798386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2798386 prefixEnd_2798386 := by exact prefixLift 2798386
  have htrace : WordTrace (prefixWord ++ tailWord_2798386) baseStart_2798386 baseEnd_2798386 := by
    simpa [prefixWord, tailWord_2798386, baseEnd_2798386] using wordTrace_append hprefix tailTrace_2798386
  have hstable : (prefixWord ++ tailWord_2798386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2798386).length < 2 ^ (prefixWord ++ tailWord_2798386).sum := by decide
  have hdescent : baseEnd_2798386 < baseStart_2798386 := by decide
  rcases family_descends (prefixWord ++ tailWord_2798386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2798419 : List Nat := [1, 1, 1, 2, 1, 1, 3, 3, 2, 5, 3]
def baseStart_2798419 : Nat := 118140960795 + 2798419 * 2 ^ 59
def prefixEnd_2798419 : Nat := 4983230072969 + 3 ^ 40 * 2798419 * 2
def baseEnd_2798419 : Nat := 1436934019674391906492811

theorem tailTrace_2798419 : CollatzResearch.WordTrace tailWord_2798419 prefixEnd_2798419 1436934019674391906492811 := by
  unfold tailWord_2798419
  simp only [CollatzResearch.WordTrace]
  refine ⟨102066726048813369760206311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68044484032542246506804207 102066726048813369760206311)
  ·
    refine ⟨153100089073220054640309467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102066726048813369760206311 153100089073220054640309467)
    ·
      refine ⟨229650133609830081960464201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 153100089073220054640309467 229650133609830081960464201)
      ·
        refine ⟨172237600207372561470348151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 229650133609830081960464201 172237600207372561470348151)
        ·
          refine ⟨258356400311058842205522227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 172237600207372561470348151 258356400311058842205522227)
          ·
            refine ⟨387534600466588263308283341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 258356400311058842205522227 387534600466588263308283341)
            ·
              refine ⟨145325475174970598740606253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 387534600466588263308283341 145325475174970598740606253)
              ·
                refine ⟨54497053190613974527727345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 145325475174970598740606253 54497053190613974527727345)
                ·
                  refine ⟨40872789892960480895795509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 54497053190613974527727345 40872789892960480895795509)
                  ·
                    refine ⟨3831824052465045083980829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 40872789892960480895795509 3831824052465045083980829)
                    ·
                      refine ⟨1436934019674391906492811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3831824052465045083980829 1436934019674391906492811)
                      ·
                        rfl

theorem cell23_2798419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 3, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 3, 2, 5, 3].length) (baseStart_2798419 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2798419 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2798419 prefixEnd_2798419 := by exact prefixLift 2798419
  have htrace : WordTrace (prefixWord ++ tailWord_2798419) baseStart_2798419 baseEnd_2798419 := by
    simpa [prefixWord, tailWord_2798419, baseEnd_2798419] using wordTrace_append hprefix tailTrace_2798419
  have hstable : (prefixWord ++ tailWord_2798419).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2798419).length < 2 ^ (prefixWord ++ tailWord_2798419).sum := by decide
  have hdescent : baseEnd_2798419 < baseStart_2798419 := by decide
  rcases family_descends (prefixWord ++ tailWord_2798419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2798423 : List Nat := [1, 1, 3, 2, 4, 2, 2, 1, 2, 2, 3]
def baseStart_2798423 : Nat := 118140960795 + 2798423 * 2 ^ 59
def prefixEnd_2798423 : Nat := 4983230072969 + 3 ^ 40 * 2798423 * 2
def baseEnd_2798423 : Nat := 1436936073597009890842793

theorem tailTrace_2798423 : CollatzResearch.WordTrace tailWord_2798423 prefixEnd_2798423 1436936073597009890842793 := by
  unfold tailWord_2798423
  simp only [CollatzResearch.WordTrace]
  refine ⟨102066871940798878443351923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68044581293865918962234615 102066871940798878443351923)
  ·
    refine ⟨153100307911198317665027885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102066871940798878443351923 153100307911198317665027885)
    ·
      refine ⟨57412615466699369124385457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 153100307911198317665027885 57412615466699369124385457)
      ·
        refine ⟨43059461600024526843289093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57412615466699369124385457 43059461600024526843289093)
        ·
          refine ⟨8073649050004598783116705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 43059461600024526843289093 8073649050004598783116705)
          ·
            refine ⟨6055236787503449087337529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8073649050004598783116705 6055236787503449087337529)
            ·
              refine ⟨4541427590627586815503147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6055236787503449087337529 4541427590627586815503147)
              ·
                refine ⟨6812141385941380223254721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4541427590627586815503147 6812141385941380223254721)
                ·
                  refine ⟨5109106039456035167441041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6812141385941380223254721 5109106039456035167441041)
                  ·
                    refine ⟨3831829529592026375580781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5109106039456035167441041 3831829529592026375580781)
                    ·
                      refine ⟨1436936073597009890842793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3831829529592026375580781 1436936073597009890842793)
                      ·
                        rfl

theorem cell23_2798423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 2, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 2, 2, 1, 2, 2, 3].length) (baseStart_2798423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2798423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2798423 prefixEnd_2798423 := by exact prefixLift 2798423
  have htrace : WordTrace (prefixWord ++ tailWord_2798423) baseStart_2798423 baseEnd_2798423 := by
    simpa [prefixWord, tailWord_2798423, baseEnd_2798423] using wordTrace_append hprefix tailTrace_2798423
  have hstable : (prefixWord ++ tailWord_2798423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2798423).length < 2 ^ (prefixWord ++ tailWord_2798423).sum := by decide
  have hdescent : baseEnd_2798423 < baseStart_2798423 := by decide
  rcases family_descends (prefixWord ++ tailWord_2798423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2798476 : List Nat := [2, 2, 1, 2, 1, 2, 4, 1, 3, 1, 4]
def baseStart_2798476 : Nat := 118140960795 + 2798476 * 2 ^ 59
def prefixEnd_2798476 : Nat := 4983230072969 + 3 ^ 40 * 2798476 * 2
def baseEnd_2798476 : Nat := 1436963288071698183480049

theorem tailTrace_2798476 : CollatzResearch.WordTrace tailWord_2798476 prefixEnd_2798476 1436963288071698183480049 := by
  unfold tailWord_2798476
  simp only [CollatzResearch.WordTrace]
  refine ⟨51034402504803434247515641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68045870006404578996687521 51034402504803434247515641)
  ·
    refine ⟨38275801878602575685636731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51034402504803434247515641 38275801878602575685636731)
    ·
      refine ⟨57413702817903863528455097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38275801878602575685636731 57413702817903863528455097)
      ·
        refine ⟨43060277113427897646341323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57413702817903863528455097 43060277113427897646341323)
        ·
          refine ⟨64590415670141846469511985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43060277113427897646341323 64590415670141846469511985)
          ·
            refine ⟨48442811752606384852133989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64590415670141846469511985 48442811752606384852133989)
            ·
              refine ⟨9083027203613697159775123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 48442811752606384852133989 9083027203613697159775123)
              ·
                refine ⟨13624540805420545739662685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9083027203613697159775123 13624540805420545739662685)
                ·
                  refine ⟨5109202802032704652373507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13624540805420545739662685 5109202802032704652373507)
                  ·
                    refine ⟨7663804203049056978560261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5109202802032704652373507 7663804203049056978560261)
                    ·
                      refine ⟨1436963288071698183480049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7663804203049056978560261 1436963288071698183480049)
                      ·
                        rfl

theorem cell23_2798476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 4, 1, 3, 1, 4].length) (baseStart_2798476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2798476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2798476 prefixEnd_2798476 := by exact prefixLift 2798476
  have htrace : WordTrace (prefixWord ++ tailWord_2798476) baseStart_2798476 baseEnd_2798476 := by
    simpa [prefixWord, tailWord_2798476, baseEnd_2798476] using wordTrace_append hprefix tailTrace_2798476
  have hstable : (prefixWord ++ tailWord_2798476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2798476).length < 2 ^ (prefixWord ++ tailWord_2798476).sum := by decide
  have hdescent : baseEnd_2798476 < baseStart_2798476 := by decide
  rcases family_descends (prefixWord ++ tailWord_2798476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2798489 : List Nat := [1, 2, 1, 2, 1, 3, 1, 2, 3, 1, 6]
def baseStart_2798489 : Nat := 118140960795 + 2798489 * 2 ^ 59
def prefixEnd_2798489 : Nat := 4983230072969 + 3 ^ 40 * 2798489 * 2
def baseEnd_2798489 : Nat := 1436969963320206632617489

theorem tailTrace_2798489 : CollatzResearch.WordTrace tailWord_2798489 prefixEnd_2798489 1436969963320206632617489 := by
  unfold tailWord_2798489
  simp only [CollatzResearch.WordTrace]
  refine ⟨102069279158559771715254521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68046186105706514476836347 102069279158559771715254521)
  ·
    refine ⟨76551959368919828786440891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102069279158559771715254521 76551959368919828786440891)
    ·
      refine ⟨114827939053379743179661337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76551959368919828786440891 114827939053379743179661337)
      ·
        refine ⟨86120954290034807384746003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 114827939053379743179661337 86120954290034807384746003)
        ·
          refine ⟨129181431435052211077119005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86120954290034807384746003 129181431435052211077119005)
          ·
            refine ⟨48443036788144579153919627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 129181431435052211077119005 48443036788144579153919627)
            ·
              refine ⟨72664555182216868730879441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48443036788144579153919627 72664555182216868730879441)
              ·
                refine ⟨54498416386662651548159581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 72664555182216868730879441 54498416386662651548159581)
                ·
                  refine ⟨20436906144998494330559843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 54498416386662651548159581 20436906144998494330559843)
                  ·
                    refine ⟨30655359217497741495839765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20436906144998494330559843 30655359217497741495839765)
                    ·
                      refine ⟨1436969963320206632617489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 30655359217497741495839765 1436969963320206632617489)
                      ·
                        rfl

theorem cell23_2798489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 2, 3, 1, 6].length) (baseStart_2798489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2798489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2798489 prefixEnd_2798489 := by exact prefixLift 2798489
  have htrace : WordTrace (prefixWord ++ tailWord_2798489) baseStart_2798489 baseEnd_2798489 := by
    simpa [prefixWord, tailWord_2798489, baseEnd_2798489] using wordTrace_append hprefix tailTrace_2798489
  have hstable : (prefixWord ++ tailWord_2798489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2798489).length < 2 ^ (prefixWord ++ tailWord_2798489).sum := by decide
  have hdescent : baseEnd_2798489 < baseStart_2798489 := by decide
  rcases family_descends (prefixWord ++ tailWord_2798489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2798493 : List Nat := [1, 4, 2, 1, 2, 1, 3, 3, 1, 1, 4]
def baseStart_2798493 : Nat := 118140960795 + 2798493 * 2 ^ 59
def prefixEnd_2798493 : Nat := 4983230072969 + 3 ^ 40 * 2798493 * 2
def baseEnd_2798493 : Nat := 1436972017242824616967471

theorem tailTrace_2798493 : CollatzResearch.WordTrace tailWord_2798493 prefixEnd_2798493 1436972017242824616967471 := by
  unfold tailWord_2798493
  simp only [CollatzResearch.WordTrace]
  refine ⟨102069425050545280398400133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68046283367030186932266755 102069425050545280398400133)
  ·
    refine ⟨19138017196977240074700025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 102069425050545280398400133 19138017196977240074700025)
    ·
      refine ⟨14353512897732930056025019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19138017196977240074700025 14353512897732930056025019)
      ·
        refine ⟨21530269346599395084037529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14353512897732930056025019 21530269346599395084037529)
        ·
          refine ⟨16147702009949546313028147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21530269346599395084037529 16147702009949546313028147)
          ·
            refine ⟨24221553014924319469542221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16147702009949546313028147 24221553014924319469542221)
            ·
              refine ⟨9083082380596619801078333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24221553014924319469542221 9083082380596619801078333)
              ·
                refine ⟨3406155892723732425404375, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9083082380596619801078333 3406155892723732425404375)
                ·
                  refine ⟨5109233839085598638106563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3406155892723732425404375 5109233839085598638106563)
                  ·
                    refine ⟨7663850758628397957159845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5109233839085598638106563 7663850758628397957159845)
                    ·
                      refine ⟨1436972017242824616967471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7663850758628397957159845 1436972017242824616967471)
                      ·
                        rfl

theorem cell23_2798493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 3, 3, 1, 1, 4].length) (baseStart_2798493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2798493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2798493 prefixEnd_2798493 := by exact prefixLift 2798493
  have htrace : WordTrace (prefixWord ++ tailWord_2798493) baseStart_2798493 baseEnd_2798493 := by
    simpa [prefixWord, tailWord_2798493, baseEnd_2798493] using wordTrace_append hprefix tailTrace_2798493
  have hstable : (prefixWord ++ tailWord_2798493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2798493).length < 2 ^ (prefixWord ++ tailWord_2798493).sum := by decide
  have hdescent : baseEnd_2798493 < baseStart_2798493 := by decide
  rcases family_descends (prefixWord ++ tailWord_2798493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2798513 : List Nat := [1, 2, 2, 4, 3, 1, 1, 2, 1, 1, 5]
def baseStart_2798513 : Nat := 118140960795 + 2798513 * 2 ^ 59
def prefixEnd_2798513 : Nat := 4983230072969 + 3 ^ 40 * 2798513 * 2
def baseEnd_2798513 : Nat := 1436982286855914538717379

theorem tailTrace_2798513 : CollatzResearch.WordTrace tailWord_2798513 prefixEnd_2798513 1436982286855914538717379 := by
  unfold tailWord_2798513
  simp only [CollatzResearch.WordTrace]
  refine ⟨102070154510472823814128193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68046769673648549209418795 102070154510472823814128193)
  ·
    refine ⟨76552615882854617860596145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102070154510472823814128193 76552615882854617860596145)
    ·
      refine ⟨57414461912140963395447109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76552615882854617860596145 57414461912140963395447109)
      ·
        refine ⟨10765211608526430636646333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 57414461912140963395447109 10765211608526430636646333)
        ·
          refine ⟨4036954353197411488742375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10765211608526430636646333 4036954353197411488742375)
          ·
            refine ⟨6055431529796117233113563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4036954353197411488742375 6055431529796117233113563)
            ·
              refine ⟨9083147294694175849670345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6055431529796117233113563 9083147294694175849670345)
              ·
                refine ⟨6812360471020631887252759, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9083147294694175849670345 6812360471020631887252759)
                ·
                  refine ⟨10218540706530947830879139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6812360471020631887252759 10218540706530947830879139)
                  ·
                    refine ⟨15327811059796421746318709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10218540706530947830879139 15327811059796421746318709)
                    ·
                      refine ⟨1436982286855914538717379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15327811059796421746318709 1436982286855914538717379)
                      ·
                        rfl

theorem cell23_2798513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 1, 1, 2, 1, 1, 5].length) (baseStart_2798513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2798513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2798513 prefixEnd_2798513 := by exact prefixLift 2798513
  have htrace : WordTrace (prefixWord ++ tailWord_2798513) baseStart_2798513 baseEnd_2798513 := by
    simpa [prefixWord, tailWord_2798513, baseEnd_2798513] using wordTrace_append hprefix tailTrace_2798513
  have hstable : (prefixWord ++ tailWord_2798513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2798513).length < 2 ^ (prefixWord ++ tailWord_2798513).sum := by decide
  have hdescent : baseEnd_2798513 < baseStart_2798513 := by decide
  rcases family_descends (prefixWord ++ tailWord_2798513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2798520 : List Nat := [2, 1, 2, 1, 2, 5, 3, 1, 2, 4]
def baseStart_2798520 : Nat := 118140960795 + 2798520 * 2 ^ 59
def prefixEnd_2798520 : Nat := 4983230072969 + 3 ^ 40 * 2798520 * 2
def baseEnd_2798520 : Nat := 478995293740165337109949

theorem tailTrace_2798520 : CollatzResearch.WordTrace tailWord_2798520 prefixEnd_2798520 478995293740165337109949 := by
  unfold tailWord_2798520
  simp only [CollatzResearch.WordTrace]
  refine ⟨51035204910723732004816507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68046939880964976006422009 51035204910723732004816507)
  ·
    refine ⟨76552807366085598007224761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51035204910723732004816507 76552807366085598007224761)
    ·
      refine ⟨57414605524564198505418571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76552807366085598007224761 57414605524564198505418571)
      ·
        refine ⟨86121908286846297758127857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57414605524564198505418571 86121908286846297758127857)
        ·
          refine ⟨64591431215134723318595893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 86121908286846297758127857 64591431215134723318595893)
          ·
            refine ⟨6055446676418880311118365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 64591431215134723318595893 6055446676418880311118365)
            ·
              refine ⟨2270792503657080116669387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6055446676418880311118365 2270792503657080116669387)
              ·
                refine ⟨3406188755485620175004081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2270792503657080116669387 3406188755485620175004081)
                ·
                  refine ⟨2554641566614215131253061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3406188755485620175004081 2554641566614215131253061)
                  ·
                    refine ⟨478995293740165337109949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2554641566614215131253061 478995293740165337109949)
                    ·
                      rfl

theorem cell23_2798520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 5, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 5, 3, 1, 2, 4].length) (baseStart_2798520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2798520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2798520 prefixEnd_2798520 := by exact prefixLift 2798520
  have htrace : WordTrace (prefixWord ++ tailWord_2798520) baseStart_2798520 baseEnd_2798520 := by
    simpa [prefixWord, tailWord_2798520, baseEnd_2798520] using wordTrace_append hprefix tailTrace_2798520
  have hstable : (prefixWord ++ tailWord_2798520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2798520).length < 2 ^ (prefixWord ++ tailWord_2798520).sum := by decide
  have hdescent : baseEnd_2798520 < baseStart_2798520 := by decide
  rcases family_descends (prefixWord ++ tailWord_2798520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2798543 : List Nat := [1, 1, 2, 1, 1, 6, 1, 2, 4, 1, 3]
def baseStart_2798543 : Nat := 118140960795 + 2798543 * 2 ^ 59
def prefixEnd_2798543 : Nat := 4983230072969 + 3 ^ 40 * 2798543 * 2
def baseEnd_2798543 : Nat := 1436997691275549421342241

theorem tailTrace_2798543 : CollatzResearch.WordTrace tailWord_2798543 prefixEnd_2798543 1436997691275549421342241 := by
  unfold tailWord_2798543
  simp only [CollatzResearch.WordTrace]
  refine ⟨102071248700364138937720283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68047499133576092625146855 102071248700364138937720283)
  ·
    refine ⟨153106873050546208406580425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102071248700364138937720283 153106873050546208406580425)
    ·
      refine ⟨114830154787909656304935319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 153106873050546208406580425 114830154787909656304935319)
      ·
        refine ⟨172245232181864484457402979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114830154787909656304935319 172245232181864484457402979)
        ·
          refine ⟨258367848272796726686104469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 172245232181864484457402979 258367848272796726686104469)
          ·
            refine ⟨12110992887787346563411147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 258367848272796726686104469 12110992887787346563411147)
            ·
              refine ⟨18166489331681019845116721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12110992887787346563411147 18166489331681019845116721)
              ·
                refine ⟨13624866998760764883837541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18166489331681019845116721 13624866998760764883837541)
                ·
                  refine ⟨2554662562267643415719539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13624866998760764883837541 2554662562267643415719539)
                  ·
                    refine ⟨3831993843401465123579309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2554662562267643415719539 3831993843401465123579309)
                    ·
                      refine ⟨1436997691275549421342241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3831993843401465123579309 1436997691275549421342241)
                      ·
                        rfl

theorem cell23_2798543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 1, 2, 4, 1, 3].length) (baseStart_2798543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2798543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2798543 prefixEnd_2798543 := by exact prefixLift 2798543
  have htrace : WordTrace (prefixWord ++ tailWord_2798543) baseStart_2798543 baseEnd_2798543 := by
    simpa [prefixWord, tailWord_2798543, baseEnd_2798543] using wordTrace_append hprefix tailTrace_2798543
  have hstable : (prefixWord ++ tailWord_2798543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2798543).length < 2 ^ (prefixWord ++ tailWord_2798543).sum := by decide
  have hdescent : baseEnd_2798543 < baseStart_2798543 := by decide
  rcases family_descends (prefixWord ++ tailWord_2798543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2798577 : List Nat := [1, 2, 2, 2, 4, 1, 4, 1, 2, 1, 3]
def baseStart_2798577 : Nat := 118140960795 + 2798577 * 2 ^ 59
def prefixEnd_2798577 : Nat := 4983230072969 + 3 ^ 40 * 2798577 * 2
def baseEnd_2798577 : Nat := 1437015149617802288317085

theorem tailTrace_2798577 : CollatzResearch.WordTrace tailWord_2798577 prefixEnd_2798577 1437015149617802288317085 := by
  unfold tailWord_2798577
  simp only [CollatzResearch.WordTrace]
  refine ⟨102072488782240962744457985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68048325854827308496305323 102072488782240962744457985)
  ·
    refine ⟨76554366586680722058343489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102072488782240962744457985 76554366586680722058343489)
    ·
      refine ⟨57415774940010541543757617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76554366586680722058343489 57415774940010541543757617)
      ·
        refine ⟨43061831205007906157818213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57415774940010541543757617 43061831205007906157818213)
        ·
          refine ⟨8074093350938982404590915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 43061831205007906157818213 8074093350938982404590915)
          ·
            refine ⟨12111140026408473606886373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8074093350938982404590915 12111140026408473606886373)
            ·
              refine ⟨2270838754951588801291195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12111140026408473606886373 2270838754951588801291195)
              ·
                refine ⟨3406258132427383201936793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2270838754951588801291195 3406258132427383201936793)
                ·
                  refine ⟨2554693599320537401452595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3406258132427383201936793 2554693599320537401452595)
                  ·
                    refine ⟨3832040398980806102178893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2554693599320537401452595 3832040398980806102178893)
                    ·
                      refine ⟨1437015149617802288317085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3832040398980806102178893 1437015149617802288317085)
                      ·
                        rfl

theorem cell23_2798577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 4, 1, 2, 1, 3].length) (baseStart_2798577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2798577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2798577 prefixEnd_2798577 := by exact prefixLift 2798577
  have htrace : WordTrace (prefixWord ++ tailWord_2798577) baseStart_2798577 baseEnd_2798577 := by
    simpa [prefixWord, tailWord_2798577, baseEnd_2798577] using wordTrace_append hprefix tailTrace_2798577
  have hstable : (prefixWord ++ tailWord_2798577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2798577).length < 2 ^ (prefixWord ++ tailWord_2798577).sum := by decide
  have hdescent : baseEnd_2798577 < baseStart_2798577 := by decide
  rcases family_descends (prefixWord ++ tailWord_2798577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2798581 : List Nat := [1, 3, 5, 2, 2, 1, 1, 2, 1, 2, 3]
def baseStart_2798581 : Nat := 118140960795 + 2798581 * 2 ^ 59
def prefixEnd_2798581 : Nat := 4983230072969 + 3 ^ 40 * 2798581 * 2
def baseEnd_2798581 : Nat := 1437017203540420272667067

theorem tailTrace_2798581 : CollatzResearch.WordTrace tailWord_2798581 prefixEnd_2798581 1437017203540420272667067 := by
  unfold tailWord_2798581
  simp only [CollatzResearch.WordTrace]
  refine ⟨102072634674226471427603597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68048423116150980951735731 102072634674226471427603597)
  ·
    refine ⟨38277238002834926785351349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 102072634674226471427603597 38277238002834926785351349)
    ·
      refine ⟨3588491062765774386126689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 38277238002834926785351349 3588491062765774386126689)
      ·
        refine ⟨2691368297074330789595017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3588491062765774386126689 2691368297074330789595017)
        ·
          refine ⟨2018526222805748092196263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2691368297074330789595017 2018526222805748092196263)
          ·
            refine ⟨3027789334208622138294395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2018526222805748092196263 3027789334208622138294395)
            ·
              refine ⟨4541684001312933207441593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3027789334208622138294395 4541684001312933207441593)
              ·
                refine ⟨3406263000984699905581195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4541684001312933207441593 3406263000984699905581195)
                ·
                  refine ⟨5109394501477049858371793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3406263000984699905581195 5109394501477049858371793)
                  ·
                    refine ⟨3832045876107787393778845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5109394501477049858371793 3832045876107787393778845)
                    ·
                      refine ⟨1437017203540420272667067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3832045876107787393778845 1437017203540420272667067)
                      ·
                        rfl

theorem cell23_2798581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 2, 1, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 2, 1, 1, 2, 1, 2, 3].length) (baseStart_2798581 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2798581 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2798581 prefixEnd_2798581 := by exact prefixLift 2798581
  have htrace : WordTrace (prefixWord ++ tailWord_2798581) baseStart_2798581 baseEnd_2798581 := by
    simpa [prefixWord, tailWord_2798581, baseEnd_2798581] using wordTrace_append hprefix tailTrace_2798581
  have hstable : (prefixWord ++ tailWord_2798581).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2798581).length < 2 ^ (prefixWord ++ tailWord_2798581).sum := by decide
  have hdescent : baseEnd_2798581 < baseStart_2798581 := by decide
  rcases family_descends (prefixWord ++ tailWord_2798581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2798600 : List Nat := [2, 1, 3, 2, 1, 4, 1, 2, 1, 4, 2]
def baseStart_2798600 : Nat := 118140960795 + 2798600 * 2 ^ 59
def prefixEnd_2798600 : Nat := 4983230072969 + 3 ^ 40 * 2798600 * 2
def baseEnd_2798600 : Nat := 1437026959672855698329479

theorem tailTrace_2798600 : CollatzResearch.WordTrace tailWord_2798600 prefixEnd_2798600 1437026959672855698329479 := by
  unfold tailWord_2798600
  simp only [CollatzResearch.WordTrace]
  refine ⟨51036663830578818836272627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68048885107438425115030169 51036663830578818836272627)
  ·
    refine ⟨76554995745868228254408941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51036663830578818836272627 76554995745868228254408941)
    ·
      refine ⟨28708123404700585595403353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 76554995745868228254408941 28708123404700585595403353)
      ·
        refine ⟨21531092553525439196552515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28708123404700585595403353 21531092553525439196552515)
        ·
          refine ⟨32296638830288158794828773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21531092553525439196552515 32296638830288158794828773)
          ·
            refine ⟨6055619780679029774030395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 32296638830288158794828773 6055619780679029774030395)
            ·
              refine ⟨9083429671018544661045593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6055619780679029774030395 9083429671018544661045593)
              ·
                refine ⟨6812572253263908495784195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9083429671018544661045593 6812572253263908495784195)
                ·
                  refine ⟨10218858379895862743676293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6812572253263908495784195 10218858379895862743676293)
                  ·
                    refine ⟨1916035946230474264439305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10218858379895862743676293 1916035946230474264439305)
                    ·
                      refine ⟨1437026959672855698329479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1916035946230474264439305 1437026959672855698329479)
                      ·
                        rfl

theorem cell23_2798600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 4, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 4, 1, 2, 1, 4, 2].length) (baseStart_2798600 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2798600 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2798600 prefixEnd_2798600 := by exact prefixLift 2798600
  have htrace : WordTrace (prefixWord ++ tailWord_2798600) baseStart_2798600 baseEnd_2798600 := by
    simpa [prefixWord, tailWord_2798600, baseEnd_2798600] using wordTrace_append hprefix tailTrace_2798600
  have hstable : (prefixWord ++ tailWord_2798600).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2798600).length < 2 ^ (prefixWord ++ tailWord_2798600).sum := by decide
  have hdescent : baseEnd_2798600 < baseStart_2798600 := by decide
  rcases family_descends (prefixWord ++ tailWord_2798600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2798636 : List Nat := [2, 2, 1, 1, 1, 2, 4, 2, 1, 7]
def baseStart_2798636 : Nat := 118140960795 + 2798636 * 2 ^ 59
def prefixEnd_2798636 : Nat := 4983230072969 + 3 ^ 40 * 2798636 * 2
def baseEnd_2798636 : Nat := 479015148325472519159771

theorem tailTrace_2798636 : CollatzResearch.WordTrace tailWord_2798636 prefixEnd_2798636 479015148325472519159771 := by
  unfold tailWord_2798636
  simp only [CollatzResearch.WordTrace]
  refine ⟨51037320344513607910427881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68049760459351477213903841 51037320344513607910427881)
  ·
    refine ⟨38277990258385205932820911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51037320344513607910427881 38277990258385205932820911)
    ·
      refine ⟨57416985387577808899231367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38277990258385205932820911 57416985387577808899231367)
      ·
        refine ⟨86125478081366713348847051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57416985387577808899231367 86125478081366713348847051)
        ·
          refine ⟨129188217122050070023270577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86125478081366713348847051 129188217122050070023270577)
          ·
            refine ⟨96891162841537552517452933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 129188217122050070023270577 96891162841537552517452933)
            ·
              refine ⟨18167093032788291097022425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 96891162841537552517452933 18167093032788291097022425)
              ·
                refine ⟨13625319774591218322766819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18167093032788291097022425 13625319774591218322766819)
                ·
                  refine ⟨20437979661886827484150229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13625319774591218322766819 20437979661886827484150229)
                  ·
                    refine ⟨479015148325472519159771, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 20437979661886827484150229 479015148325472519159771)
                    ·
                      rfl

theorem cell23_2798636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 7].length) (baseStart_2798636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2798636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2798636 prefixEnd_2798636 := by exact prefixLift 2798636
  have htrace : WordTrace (prefixWord ++ tailWord_2798636) baseStart_2798636 baseEnd_2798636 := by
    simpa [prefixWord, tailWord_2798636, baseEnd_2798636] using wordTrace_append hprefix tailTrace_2798636
  have hstable : (prefixWord ++ tailWord_2798636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2798636).length < 2 ^ (prefixWord ++ tailWord_2798636).sum := by decide
  have hdescent : baseEnd_2798636 < baseStart_2798636 := by decide
  rcases family_descends (prefixWord ++ tailWord_2798636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2798643 : List Nat := [1, 1, 1, 2, 4, 1, 1, 1, 4, 5, 2]
def baseStart_2798643 : Nat := 118140960795 + 2798643 * 2 ^ 59
def prefixEnd_2798643 : Nat := 4983230072969 + 3 ^ 40 * 2798643 * 2
def baseEnd_2798643 : Nat := 1437049039340999030091781

theorem tailTrace_2798643 : CollatzResearch.WordTrace tailWord_2798643 prefixEnd_2798643 1437049039340999030091781 := by
  unfold tailWord_2798643
  simp only [CollatzResearch.WordTrace]
  refine ⟨102074896000001856016360583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68049930666667904010907055 102074896000001856016360583)
  ·
    refine ⟨153112344000002784024540875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102074896000001856016360583 153112344000002784024540875)
    ·
      refine ⟨229668516000004176036811313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 153112344000002784024540875 229668516000004176036811313)
      ·
        refine ⟨172251387000003132027608485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 229668516000004176036811313 172251387000003132027608485)
        ·
          refine ⟨32297135062500587255176591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 172251387000003132027608485 32297135062500587255176591)
          ·
            refine ⟨48445702593750880882764887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32297135062500587255176591 48445702593750880882764887)
            ·
              refine ⟨72668553890626321324147331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48445702593750880882764887 72668553890626321324147331)
              ·
                refine ⟨109002830835939481986220997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 72668553890626321324147331 109002830835939481986220997)
                ·
                  refine ⟨20438030781738652872416437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 109002830835939481986220997 20438030781738652872416437)
                  ·
                    refine ⟨1916065385787998706789041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 20438030781738652872416437 1916065385787998706789041)
                    ·
                      refine ⟨1437049039340999030091781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1916065385787998706789041 1437049039340999030091781)
                      ·
                        rfl

theorem cell23_2798643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 1, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 1, 4, 5, 2].length) (baseStart_2798643 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2798643 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2798643 prefixEnd_2798643 := by exact prefixLift 2798643
  have htrace : WordTrace (prefixWord ++ tailWord_2798643) baseStart_2798643 baseEnd_2798643 := by
    simpa [prefixWord, tailWord_2798643, baseEnd_2798643] using wordTrace_append hprefix tailTrace_2798643
  have hstable : (prefixWord ++ tailWord_2798643).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2798643).length < 2 ^ (prefixWord ++ tailWord_2798643).sum := by decide
  have hdescent : baseEnd_2798643 < baseStart_2798643 := by decide
  rcases family_descends (prefixWord ++ tailWord_2798643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2798653 : List Nat := [1, 4, 1, 3, 1, 3, 1, 1, 1, 7]
def baseStart_2798653 : Nat := 118140960795 + 2798653 * 2 ^ 59
def prefixEnd_2798653 : Nat := 4983230072969 + 3 ^ 40 * 2798653 * 2
def baseEnd_2798653 : Nat := 479018058049181330322245

theorem tailTrace_2798653 : CollatzResearch.WordTrace tailWord_2798653 prefixEnd_2798653 479018058049181330322245 := by
  unfold tailWord_2798653
  simp only [CollatzResearch.WordTrace]
  refine ⟨102075260729965627724224613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68050173819977085149483075 102075260729965627724224613)
  ·
    refine ⟨19139111386868555198292115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 102075260729965627724224613 19139111386868555198292115)
    ·
      refine ⟨28708667080302832797438173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19139111386868555198292115 28708667080302832797438173)
      ·
        refine ⟨10765750155113562299039315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28708667080302832797438173 10765750155113562299039315)
        ·
          refine ⟨16148625232670343448558973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10765750155113562299039315 16148625232670343448558973)
          ·
            refine ⟨6055734462251378793209615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16148625232670343448558973 6055734462251378793209615)
            ·
              refine ⟨9083601693377068189814423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6055734462251378793209615 9083601693377068189814423)
              ·
                refine ⟨13625402540065602284721635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9083601693377068189814423 13625402540065602284721635)
                ·
                  refine ⟨20438103810098403427082453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13625402540065602284721635 20438103810098403427082453)
                  ·
                    refine ⟨479018058049181330322245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 20438103810098403427082453 479018058049181330322245)
                    ·
                      rfl

theorem cell23_2798653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 3, 1, 1, 1, 7].length) (baseStart_2798653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2798653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2798653 prefixEnd_2798653 := by exact prefixLift 2798653
  have htrace : WordTrace (prefixWord ++ tailWord_2798653) baseStart_2798653 baseEnd_2798653 := by
    simpa [prefixWord, tailWord_2798653, baseEnd_2798653] using wordTrace_append hprefix tailTrace_2798653
  have hstable : (prefixWord ++ tailWord_2798653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2798653).length < 2 ^ (prefixWord ++ tailWord_2798653).sum := by decide
  have hdescent : baseEnd_2798653 < baseStart_2798653 := by decide
  rcases family_descends (prefixWord ++ tailWord_2798653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2798657 : List Nat := [1, 2, 5, 1, 3, 1, 2, 3, 5]
def baseStart_2798657 : Nat := 118140960795 + 2798657 * 2 ^ 59
def prefixEnd_2798657 : Nat := 4983230072969 + 3 ^ 40 * 2798657 * 2
def baseEnd_2798657 : Nat := 159672914230017997257413

theorem tailTrace_2798657 : CollatzResearch.WordTrace tailWord_2798657 prefixEnd_2798657 159672914230017997257413 := by
  unfold tailWord_2798657
  simp only [CollatzResearch.WordTrace]
  refine ⟨102075406621951136407370225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68050271081300757604913483 102075406621951136407370225)
  ·
    refine ⟨76556554966463352305527669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102075406621951136407370225 76556554966463352305527669)
    ·
      refine ⟨7177177028105939278643219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 76556554966463352305527669 7177177028105939278643219)
      ·
        refine ⟨10765765542158908917964829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7177177028105939278643219 10765765542158908917964829)
        ·
          refine ⟨4037162078309590844236811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10765765542158908917964829 4037162078309590844236811)
          ·
            refine ⟨6055743117464386266355217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4037162078309590844236811 6055743117464386266355217)
            ·
              refine ⟨4541807338098289699766413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6055743117464386266355217 4541807338098289699766413)
              ·
                refine ⟨1703177751786858637412405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4541807338098289699766413 1703177751786858637412405)
                ·
                  refine ⟨159672914230017997257413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1703177751786858637412405 159672914230017997257413)
                  ·
                    rfl

theorem cell23_2798657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 1, 2, 3, 5].length) (baseStart_2798657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2798657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2798657 prefixEnd_2798657 := by exact prefixLift 2798657
  have htrace : WordTrace (prefixWord ++ tailWord_2798657) baseStart_2798657 baseEnd_2798657 := by
    simpa [prefixWord, tailWord_2798657, baseEnd_2798657] using wordTrace_append hprefix tailTrace_2798657
  have hstable : (prefixWord ++ tailWord_2798657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2798657).length < 2 ^ (prefixWord ++ tailWord_2798657).sum := by decide
  have hdescent : baseEnd_2798657 < baseStart_2798657 := by decide
  rcases family_descends (prefixWord ++ tailWord_2798657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2798673 : List Nat := [1, 2, 2, 1, 3, 1, 2, 4, 2, 1, 4]
def baseStart_2798673 : Nat := 118140960795 + 2798673 * 2 ^ 59
def prefixEnd_2798673 : Nat := 4983230072969 + 3 ^ 40 * 2798673 * 2
def baseEnd_2798673 : Nat := 1437064443760633912716643

theorem tailTrace_2798673 : CollatzResearch.WordTrace tailWord_2798673 prefixEnd_2798673 1437064443760633912716643 := by
  unfold tailWord_2798673
  simp only [CollatzResearch.WordTrace]
  refine ⟨102075990189893171139952673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68050660126595447426635115 102075990189893171139952673)
  ·
    refine ⟨76556992642419878354964505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102075990189893171139952673 76556992642419878354964505)
    ·
      refine ⟨57417744481814908766223379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76556992642419878354964505 57417744481814908766223379)
      ·
        refine ⟨86126616722722363149335069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57417744481814908766223379 86126616722722363149335069)
        ·
          refine ⟨32297481271020886181000651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 86126616722722363149335069 32297481271020886181000651)
          ·
            refine ⟨48446221906531329271500977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32297481271020886181000651 48446221906531329271500977)
            ·
              refine ⟨36334666429898496953625733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48446221906531329271500977 36334666429898496953625733)
              ·
                refine ⟨6812749955605968178804825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 36334666429898496953625733 6812749955605968178804825)
                ·
                  refine ⟨5109562466704476134103619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6812749955605968178804825 5109562466704476134103619)
                  ·
                    refine ⟨7664343700056714201155429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5109562466704476134103619 7664343700056714201155429)
                    ·
                      refine ⟨1437064443760633912716643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7664343700056714201155429 1437064443760633912716643)
                      ·
                        rfl

theorem cell23_2798673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 2, 4, 2, 1, 4].length) (baseStart_2798673 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2798673 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2798673 prefixEnd_2798673 := by exact prefixLift 2798673
  have htrace : WordTrace (prefixWord ++ tailWord_2798673) baseStart_2798673 baseEnd_2798673 := by
    simpa [prefixWord, tailWord_2798673, baseEnd_2798673] using wordTrace_append hprefix tailTrace_2798673
  have hstable : (prefixWord ++ tailWord_2798673).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2798673).length < 2 ^ (prefixWord ++ tailWord_2798673).sum := by decide
  have hdescent : baseEnd_2798673 < baseStart_2798673 := by decide
  rcases family_descends (prefixWord ++ tailWord_2798673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2798690 : List Nat := [3, 3, 2, 2, 1, 1, 1, 2, 1, 3, 4]
def baseStart_2798690 : Nat := 118140960795 + 2798690 * 2 ^ 59
def prefixEnd_2798690 : Nat := 4983230072969 + 3 ^ 40 * 2798690 * 2
def baseEnd_2798690 : Nat := 1437073172931760346204065

theorem tailTrace_2798690 : CollatzResearch.WordTrace tailWord_2798690 prefixEnd_2798690 1437073172931760346204065 := by
  unfold tailWord_2798690
  simp only [CollatzResearch.WordTrace]
  refine ⟨25519152557707895760830381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68051073487221055362214349 25519152557707895760830381)
  ·
    refine ⟨9569682209140460910311393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25519152557707895760830381 9569682209140460910311393)
    ·
      refine ⟨7177261656855345682733545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9569682209140460910311393 7177261656855345682733545)
      ·
        refine ⟨5382946242641509262050159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7177261656855345682733545 5382946242641509262050159)
        ·
          refine ⟨8074419363962263893075239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5382946242641509262050159 8074419363962263893075239)
          ·
            refine ⟨12111629045943395839612859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8074419363962263893075239 12111629045943395839612859)
            ·
              refine ⟨18167443568915093759419289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12111629045943395839612859 18167443568915093759419289)
              ·
                refine ⟨13625582676686320319564467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18167443568915093759419289 13625582676686320319564467)
                ·
                  refine ⟨20438374015029480479346701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13625582676686320319564467 20438374015029480479346701)
                  ·
                    refine ⟨7664390255636055179755013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20438374015029480479346701 7664390255636055179755013)
                    ·
                      refine ⟨1437073172931760346204065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7664390255636055179755013 1437073172931760346204065)
                      ·
                        rfl

theorem cell23_2798690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 1, 2, 1, 3, 4].length) (baseStart_2798690 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2798690 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2798690 prefixEnd_2798690 := by exact prefixLift 2798690
  have htrace : WordTrace (prefixWord ++ tailWord_2798690) baseStart_2798690 baseEnd_2798690 := by
    simpa [prefixWord, tailWord_2798690, baseEnd_2798690] using wordTrace_append hprefix tailTrace_2798690
  have hstable : (prefixWord ++ tailWord_2798690).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2798690).length < 2 ^ (prefixWord ++ tailWord_2798690).sum := by decide
  have hdescent : baseEnd_2798690 < baseStart_2798690 := by decide
  rcases family_descends (prefixWord ++ tailWord_2798690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2798693 : List Nat := [1, 3, 1, 3, 2, 1, 1, 1, 3, 4, 3]
def baseStart_2798693 : Nat := 118140960795 + 2798693 * 2 ^ 59
def prefixEnd_2798693 : Nat := 4983230072969 + 3 ^ 40 * 2798693 * 2
def baseEnd_2798693 : Nat := 1437074713373723834466551

theorem tailTrace_2798693 : CollatzResearch.WordTrace tailWord_2798693 prefixEnd_2798693 1437074713373723834466551 := by
  unfold tailWord_2798693
  simp only [CollatzResearch.WordTrace]
  refine ⟨102076719649820714555680733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68051146433213809703787155 102076719649820714555680733)
  ·
    refine ⟨38278769868682767958380275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 102076719649820714555680733 38278769868682767958380275)
    ·
      refine ⟨57418154803024151937570413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38278769868682767958380275 57418154803024151937570413)
      ·
        refine ⟨21531808051134056976588905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 57418154803024151937570413 21531808051134056976588905)
        ·
          refine ⟨16148856038350542732441679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21531808051134056976588905 16148856038350542732441679)
          ·
            refine ⟨24223284057525814098662519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16148856038350542732441679 24223284057525814098662519)
            ·
              refine ⟨36334926086288721147993779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24223284057525814098662519 36334926086288721147993779)
              ·
                refine ⟨54502389129433081721990669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36334926086288721147993779 54502389129433081721990669)
                ·
                  refine ⟨20438395923537405645746501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 54502389129433081721990669 20438395923537405645746501)
                  ·
                    refine ⟨3832199235663263558577469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20438395923537405645746501 3832199235663263558577469)
                    ·
                      refine ⟨1437074713373723834466551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3832199235663263558577469 1437074713373723834466551)
                      ·
                        rfl

theorem cell23_2798693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 1, 1, 3, 4, 3].length) (baseStart_2798693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2798693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2798693 prefixEnd_2798693 := by exact prefixLift 2798693
  have htrace : WordTrace (prefixWord ++ tailWord_2798693) baseStart_2798693 baseEnd_2798693 := by
    simpa [prefixWord, tailWord_2798693, baseEnd_2798693] using wordTrace_append hprefix tailTrace_2798693
  have hstable : (prefixWord ++ tailWord_2798693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2798693).length < 2 ^ (prefixWord ++ tailWord_2798693).sum := by decide
  have hdescent : baseEnd_2798693 < baseStart_2798693 := by decide
  rcases family_descends (prefixWord ++ tailWord_2798693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2798710 : List Nat := [5, 1, 1, 2, 1, 1, 1, 3, 1, 4, 3]
def baseStart_2798710 : Nat := 118140960795 + 2798710 * 2 ^ 59
def prefixEnd_2798710 : Nat := 4983230072969 + 3 ^ 40 * 2798710 * 2
def baseEnd_2798710 : Nat := 1437083442544850267953973

theorem tailTrace_2798710 : CollatzResearch.WordTrace tailWord_2798710 prefixEnd_2798710 1437083442544850267953973 := by
  unfold tailWord_2798710
  simp only [CollatzResearch.WordTrace]
  refine ⟨6379833730672445403690599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 68051559793839417639366389 6379833730672445403690599)
  ·
    refine ⟨9569750596008668105535899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6379833730672445403690599 9569750596008668105535899)
    ·
      refine ⟨14354625894013002158303849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9569750596008668105535899 14354625894013002158303849)
      ·
        refine ⟨10765969420509751618727887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14354625894013002158303849 10765969420509751618727887)
        ·
          refine ⟨16148954130764627428091831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10765969420509751618727887 16148954130764627428091831)
          ·
            refine ⟨24223431196146941142137747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16148954130764627428091831 24223431196146941142137747)
            ·
              refine ⟨36335146794220411713206621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24223431196146941142137747 36335146794220411713206621)
              ·
                refine ⟨13625680047832654392452483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36335146794220411713206621 13625680047832654392452483)
                ·
                  refine ⟨20438520071748981588678725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13625680047832654392452483 20438520071748981588678725)
                  ·
                    refine ⟨3832222513452934047877261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20438520071748981588678725 3832222513452934047877261)
                    ·
                      refine ⟨1437083442544850267953973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3832222513452934047877261 1437083442544850267953973)
                      ·
                        rfl

theorem cell23_2798710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 1, 3, 1, 4, 3].length) (baseStart_2798710 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2798710 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2798710 prefixEnd_2798710 := by exact prefixLift 2798710
  have htrace : WordTrace (prefixWord ++ tailWord_2798710) baseStart_2798710 baseEnd_2798710 := by
    simpa [prefixWord, tailWord_2798710, baseEnd_2798710] using wordTrace_append hprefix tailTrace_2798710
  have hstable : (prefixWord ++ tailWord_2798710).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2798710).length < 2 ^ (prefixWord ++ tailWord_2798710).sum := by decide
  have hdescent : baseEnd_2798710 < baseStart_2798710 := by decide
  rcases family_descends (prefixWord ++ tailWord_2798710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2798777 : List Nat := [1, 2, 1, 4, 1, 4, 3, 1, 1, 5]
def baseStart_2798777 : Nat := 118140960795 + 2798777 * 2 ^ 59
def prefixEnd_2798777 : Nat := 4983230072969 + 3 ^ 40 * 2798777 * 2
def baseEnd_2798777 : Nat := 479039281916233835272055

theorem tailTrace_2798777 : CollatzResearch.WordTrace tailWord_2798777 prefixEnd_2798777 479039281916233835272055 := by
  unfold tailWord_2798777
  simp only [CollatzResearch.WordTrace]
  refine ⟨102079783381516396901738585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68053188921010931267825723 102079783381516396901738585)
  ·
    refine ⟨76559837536137297676303939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102079783381516396901738585 76559837536137297676303939)
    ·
      refine ⟨114839756304205946514455909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76559837536137297676303939 114839756304205946514455909)
      ·
        refine ⟨21532454307038614971460483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 114839756304205946514455909 21532454307038614971460483)
        ·
          refine ⟨32298681460557922457190725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21532454307038614971460483 32298681460557922457190725)
          ·
            refine ⟨6056002773854610460723261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 32298681460557922457190725 6056002773854610460723261)
            ·
              refine ⟨2271001040195478922771223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6056002773854610460723261 2271001040195478922771223)
              ·
                refine ⟨3406501560293218384156835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2271001040195478922771223 3406501560293218384156835)
                ·
                  refine ⟨5109752340439827576235253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3406501560293218384156835 5109752340439827576235253)
                  ·
                    refine ⟨479039281916233835272055, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5109752340439827576235253 479039281916233835272055)
                    ·
                      rfl

theorem cell23_2798777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 4, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 4, 3, 1, 1, 5].length) (baseStart_2798777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2798777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2798777 prefixEnd_2798777 := by exact prefixLift 2798777
  have htrace : WordTrace (prefixWord ++ tailWord_2798777) baseStart_2798777 baseEnd_2798777 := by
    simpa [prefixWord, tailWord_2798777, baseEnd_2798777] using wordTrace_append hprefix tailTrace_2798777
  have hstable : (prefixWord ++ tailWord_2798777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2798777).length < 2 ^ (prefixWord ++ tailWord_2798777).sum := by decide
  have hdescent : baseEnd_2798777 < baseStart_2798777 := by decide
  rcases family_descends (prefixWord ++ tailWord_2798777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2798831 : List Nat := [1, 1, 2, 1, 8, 1, 2, 1, 1, 1, 4]
def baseStart_2798831 : Nat := 118140960795 + 2798831 * 2 ^ 59
def prefixEnd_2798831 : Nat := 4983230072969 + 3 ^ 40 * 2798831 * 2
def baseEnd_2798831 : Nat := 1437145573704044294540917

theorem tailTrace_2798831 : CollatzResearch.WordTrace tailWord_2798831 prefixEnd_2798831 1437145573704044294540917 := by
  unfold tailWord_2798831
  simp only [CollatzResearch.WordTrace]
  refine ⟨102081752923320764124204347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68054501948880509416136231 102081752923320764124204347)
  ·
    refine ⟨153122629384981146186306521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102081752923320764124204347 153122629384981146186306521)
    ·
      refine ⟨114841972038735859639729891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 153122629384981146186306521 114841972038735859639729891)
      ·
        refine ⟨172262958058103789459594837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114841972038735859639729891 172262958058103789459594837)
        ·
          refine ⟨2018706539743403782729627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 172262958058103789459594837 2018706539743403782729627)
          ·
            refine ⟨3028059809615105674094441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2018706539743403782729627 3028059809615105674094441)
            ·
              refine ⟨2271044857211329255570831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3028059809615105674094441 2271044857211329255570831)
              ·
                refine ⟨3406567285816993883356247, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2271044857211329255570831 3406567285816993883356247)
                ·
                  refine ⟨5109850928725490825034371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3406567285816993883356247 5109850928725490825034371)
                  ·
                    refine ⟨7664776393088236237551557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5109850928725490825034371 7664776393088236237551557)
                    ·
                      refine ⟨1437145573704044294540917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7664776393088236237551557 1437145573704044294540917)
                      ·
                        rfl

theorem cell23_2798831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 8, 1, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 8, 1, 2, 1, 1, 1, 4].length) (baseStart_2798831 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2798831 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2798831 prefixEnd_2798831 := by exact prefixLift 2798831
  have htrace : WordTrace (prefixWord ++ tailWord_2798831) baseStart_2798831 baseEnd_2798831 := by
    simpa [prefixWord, tailWord_2798831, baseEnd_2798831] using wordTrace_append hprefix tailTrace_2798831
  have hstable : (prefixWord ++ tailWord_2798831).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2798831).length < 2 ^ (prefixWord ++ tailWord_2798831).sum := by decide
  have hdescent : baseEnd_2798831 < baseStart_2798831 := by decide
  rcases family_descends (prefixWord ++ tailWord_2798831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2798834 : List Nat := [3, 2, 1, 3, 3, 1, 1, 3, 1, 2, 3]
def baseStart_2798834 : Nat := 118140960795 + 2798834 * 2 ^ 59
def prefixEnd_2798834 : Nat := 4983230072969 + 3 ^ 40 * 2798834 * 2
def baseEnd_2798834 : Nat := 1437147114146007782803403

theorem tailTrace_2798834 : CollatzResearch.WordTrace tailWord_2798834 prefixEnd_2798834 1437147114146007782803403 := by
  unfold tailWord_2798834
  simp only [CollatzResearch.WordTrace]
  refine ⟨25520465585577473909140889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68054574894873263757709037 25520465585577473909140889)
  ·
    refine ⟨19140349189183105431855667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25520465585577473909140889 19140349189183105431855667)
    ·
      refine ⟨28710523783774658147783501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19140349189183105431855667 28710523783774658147783501)
      ·
        refine ⟨10766446418915496805418813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28710523783774658147783501 10766446418915496805418813)
        ·
          refine ⟨4037417407093311302032055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10766446418915496805418813 4037417407093311302032055)
          ·
            refine ⟨6056126110639966953048083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4037417407093311302032055 6056126110639966953048083)
            ·
              refine ⟨9084189165959950429572125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6056126110639966953048083 9084189165959950429572125)
              ·
                refine ⟨3406570937234981411089547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9084189165959950429572125 3406570937234981411089547)
                ·
                  refine ⟨5109856405852472116634321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3406570937234981411089547 5109856405852472116634321)
                  ·
                    refine ⟨3832392304389354087475741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5109856405852472116634321 3832392304389354087475741)
                    ·
                      refine ⟨1437147114146007782803403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3832392304389354087475741 1437147114146007782803403)
                      ·
                        rfl

theorem cell23_2798834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 1, 1, 3, 1, 2, 3].length) (baseStart_2798834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2798834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2798834 prefixEnd_2798834 := by exact prefixLift 2798834
  have htrace : WordTrace (prefixWord ++ tailWord_2798834) baseStart_2798834 baseEnd_2798834 := by
    simpa [prefixWord, tailWord_2798834, baseEnd_2798834] using wordTrace_append hprefix tailTrace_2798834
  have hstable : (prefixWord ++ tailWord_2798834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2798834).length < 2 ^ (prefixWord ++ tailWord_2798834).sum := by decide
  have hdescent : baseEnd_2798834 < baseStart_2798834 := by decide
  rcases family_descends (prefixWord ++ tailWord_2798834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2798847 : List Nat := [1, 1, 2, 2, 1, 6, 1, 1, 4, 1, 3]
def baseStart_2798847 : Nat := 118140960795 + 2798847 * 2 ^ 59
def prefixEnd_2798847 : Nat := 4983230072969 + 3 ^ 40 * 2798847 * 2
def baseEnd_2798847 : Nat := 1437153789394516231940843

theorem tailTrace_2798847 : CollatzResearch.WordTrace tailWord_2798847 prefixEnd_2798847 1437153789394516231940843 := by
  unfold tailWord_2798847
  simp only [CollatzResearch.WordTrace]
  refine ⟨102082336491262798856786795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68054890994175199237857863 102082336491262798856786795)
  ·
    refine ⟨153123504736894198285180193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102082336491262798856786795 153123504736894198285180193)
    ·
      refine ⟨114842628552670648713885145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 153123504736894198285180193 114842628552670648713885145)
      ·
        refine ⟨86131971414502986535413859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 114842628552670648713885145 86131971414502986535413859)
        ·
          refine ⟨129197957121754479803120789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86131971414502986535413859 129197957121754479803120789)
          ·
            refine ⟨6056154240082241240771287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 129197957121754479803120789 6056154240082241240771287)
            ·
              refine ⟨9084231360123361861156931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6056154240082241240771287 9084231360123361861156931)
              ·
                refine ⟨13626347040185042791735397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9084231360123361861156931 13626347040185042791735397)
                ·
                  refine ⟨2554940070034695523450387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13626347040185042791735397 2554940070034695523450387)
                  ·
                    refine ⟨3832410105052043285175581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2554940070034695523450387 3832410105052043285175581)
                    ·
                      refine ⟨1437153789394516231940843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3832410105052043285175581 1437153789394516231940843)
                      ·
                        rfl

theorem cell23_2798847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 6, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 6, 1, 1, 4, 1, 3].length) (baseStart_2798847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2798847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2798847 prefixEnd_2798847 := by exact prefixLift 2798847
  have htrace : WordTrace (prefixWord ++ tailWord_2798847) baseStart_2798847 baseEnd_2798847 := by
    simpa [prefixWord, tailWord_2798847, baseEnd_2798847] using wordTrace_append hprefix tailTrace_2798847
  have hstable : (prefixWord ++ tailWord_2798847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2798847).length < 2 ^ (prefixWord ++ tailWord_2798847).sum := by decide
  have hdescent : baseEnd_2798847 < baseStart_2798847 := by decide
  rcases family_descends (prefixWord ++ tailWord_2798847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2798873 : List Nat := [1, 2, 1, 2, 1, 1, 1, 1, 5, 3, 5]
def baseStart_2798873 : Nat := 118140960795 + 2798873 * 2 ^ 59
def prefixEnd_2798873 : Nat := 4983230072969 + 3 ^ 40 * 2798873 * 2
def baseEnd_2798873 : Nat := 1437167139891533130215723

theorem tailTrace_2798873 : CollatzResearch.WordTrace tailWord_2798873 prefixEnd_2798873 1437167139891533130215723 := by
  unfold tailWord_2798873
  simp only [CollatzResearch.WordTrace]
  refine ⟨102083284789168605297233273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68055523192779070198155515 102083284789168605297233273)
  ·
    refine ⟨76562463591876453972924955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102083284789168605297233273 76562463591876453972924955)
    ·
      refine ⟨114843695387814680959387433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76562463591876453972924955 114843695387814680959387433)
      ·
        refine ⟨86132771540861010719540575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 114843695387814680959387433 86132771540861010719540575)
        ·
          refine ⟨129199157311291516079310863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86132771540861010719540575 129199157311291516079310863)
          ·
            refine ⟨193798735966937274118966295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 129199157311291516079310863 193798735966937274118966295)
            ·
              refine ⟨290698103950405911178449443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 193798735966937274118966295 290698103950405911178449443)
              ·
                refine ⟨436047155925608866767674165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 290698103950405911178449443 436047155925608866767674165)
                ·
                  refine ⟨40879420868025831259469453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 436047155925608866767674165 40879420868025831259469453)
                  ·
                    refine ⟨15329782825509686722301045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 40879420868025831259469453 15329782825509686722301045)
                    ·
                      refine ⟨1437167139891533130215723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15329782825509686722301045 1437167139891533130215723)
                      ·
                        rfl

theorem cell23_2798873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 1, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 1, 5, 3, 5].length) (baseStart_2798873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2798873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2798873 prefixEnd_2798873 := by exact prefixLift 2798873
  have htrace : WordTrace (prefixWord ++ tailWord_2798873) baseStart_2798873 baseEnd_2798873 := by
    simpa [prefixWord, tailWord_2798873, baseEnd_2798873] using wordTrace_append hprefix tailTrace_2798873
  have hstable : (prefixWord ++ tailWord_2798873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2798873).length < 2 ^ (prefixWord ++ tailWord_2798873).sum := by decide
  have hdescent : baseEnd_2798873 < baseStart_2798873 := by decide
  rcases family_descends (prefixWord ++ tailWord_2798873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2798874 : List Nat := [3, 1, 1, 3, 3, 1, 1, 4, 1, 3, 2]
def baseStart_2798874 : Nat := 118140960795 + 2798874 * 2 ^ 59
def prefixEnd_2798874 : Nat := 4983230072969 + 3 ^ 40 * 2798874 * 2
def baseEnd_2798874 : Nat := 1437167653372187626303219

theorem tailTrace_2798874 : CollatzResearch.WordTrace tailWord_2798874 prefixEnd_2798874 1437167653372187626303219 := by
  unfold tailWord_2798874
  simp only [CollatzResearch.WordTrace]
  refine ⟨25520830315541245617004919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68055547508109988312013117 25520830315541245617004919)
  ·
    refine ⟨38281245473311868425507379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25520830315541245617004919 38281245473311868425507379)
    ·
      refine ⟨57421868209967802638261069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38281245473311868425507379 57421868209967802638261069)
      ·
        refine ⟨21533200578737925989347901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 57421868209967802638261069 21533200578737925989347901)
        ·
          refine ⟨8074950217026722246005463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21533200578737925989347901 8074950217026722246005463)
          ·
            refine ⟨12112425325540083369008195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8074950217026722246005463 12112425325540083369008195)
            ·
              refine ⟨18168637988310125053512293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12112425325540083369008195 18168637988310125053512293)
              ·
                refine ⟨3406619622808148447533555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18168637988310125053512293 3406619622808148447533555)
                ·
                  refine ⟨5109929434212222671300333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3406619622808148447533555 5109929434212222671300333)
                  ·
                    refine ⟨1916223537829583501737625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5109929434212222671300333 1916223537829583501737625)
                    ·
                      refine ⟨1437167653372187626303219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1916223537829583501737625 1437167653372187626303219)
                      ·
                        rfl

theorem cell23_2798874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 1, 4, 1, 3, 2].length) (baseStart_2798874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2798874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2798874 prefixEnd_2798874 := by exact prefixLift 2798874
  have htrace : WordTrace (prefixWord ++ tailWord_2798874) baseStart_2798874 baseEnd_2798874 := by
    simpa [prefixWord, tailWord_2798874, baseEnd_2798874] using wordTrace_append hprefix tailTrace_2798874
  have hstable : (prefixWord ++ tailWord_2798874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2798874).length < 2 ^ (prefixWord ++ tailWord_2798874).sum := by decide
  have hdescent : baseEnd_2798874 < baseStart_2798874 := by decide
  rcases family_descends (prefixWord ++ tailWord_2798874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2798904 : List Nat := [2, 1, 2, 1, 3, 1, 1, 6, 2, 2, 2]
def baseStart_2798904 : Nat := 118140960795 + 2798904 * 2 ^ 59
def prefixEnd_2798904 : Nat := 4983230072969 + 3 ^ 40 * 2798904 * 2
def baseEnd_2798904 : Nat := 1437183057791822508928081

theorem tailTrace_2798904 : CollatzResearch.WordTrace tailWord_2798904 prefixEnd_2798904 1437183057791822508928081 := by
  unfold tailWord_2798904
  simp only [CollatzResearch.WordTrace]
  refine ⟨51042207726028148795805883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68056276968037531727741177 51042207726028148795805883)
  ·
    refine ⟨76563311589042223193708825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51042207726028148795805883 76563311589042223193708825)
    ·
      refine ⟨57422483691781667395281619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76563311589042223193708825 57422483691781667395281619)
      ·
        refine ⟨86133725537672501092922429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57422483691781667395281619 86133725537672501092922429)
        ·
          refine ⟨32300147076627187909845911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 86133725537672501092922429 32300147076627187909845911)
          ·
            refine ⟨48450220614940781864768867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32300147076627187909845911 48450220614940781864768867)
            ·
              refine ⟨72675330922411172797153301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48450220614940781864768867 72675330922411172797153301)
              ·
                refine ⟨3406656136988023724866561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 72675330922411172797153301 3406656136988023724866561)
                ·
                  refine ⟨2554992102741017793649921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3406656136988023724866561 2554992102741017793649921)
                  ·
                    refine ⟨1916244077055763345237441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2554992102741017793649921 1916244077055763345237441)
                    ·
                      refine ⟨1437183057791822508928081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1916244077055763345237441 1437183057791822508928081)
                      ·
                        rfl

theorem cell23_2798904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 6, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 6, 2, 2, 2].length) (baseStart_2798904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2798904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2798904 prefixEnd_2798904 := by exact prefixLift 2798904
  have htrace : WordTrace (prefixWord ++ tailWord_2798904) baseStart_2798904 baseEnd_2798904 := by
    simpa [prefixWord, tailWord_2798904, baseEnd_2798904] using wordTrace_append hprefix tailTrace_2798904
  have hstable : (prefixWord ++ tailWord_2798904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2798904).length < 2 ^ (prefixWord ++ tailWord_2798904).sum := by decide
  have hdescent : baseEnd_2798904 < baseStart_2798904 := by decide
  rcases family_descends (prefixWord ++ tailWord_2798904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2798920 : List Nat := [2, 1, 3, 1, 1, 2, 1, 3, 1, 5, 3]
def baseStart_2798920 : Nat := 118140960795 + 2798920 * 2 ^ 59
def prefixEnd_2798920 : Nat := 4983230072969 + 3 ^ 40 * 2798920 * 2
def baseEnd_2798920 : Nat := 1437191273482294446328007

theorem tailTrace_2798920 : CollatzResearch.WordTrace tailWord_2798920 prefixEnd_2798920 1437191273482294446328007 := by
  unfold tailWord_2798920
  simp only [CollatzResearch.WordTrace]
  refine ⟨51042499509999166162097107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68056666013332221549462809 51042499509999166162097107)
  ·
    refine ⟨76563749264998749243145661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51042499509999166162097107 76563749264998749243145661)
    ·
      refine ⟨28711405974374530966179623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 76563749264998749243145661 28711405974374530966179623)
      ·
        refine ⟨43067108961561796449269435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28711405974374530966179623 43067108961561796449269435)
        ·
          refine ⟨64600663442342694673904153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43067108961561796449269435 64600663442342694673904153)
          ·
            refine ⟨48450497581757021005428115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64600663442342694673904153 48450497581757021005428115)
            ·
              refine ⟨72675746372635531508142173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48450497581757021005428115 72675746372635531508142173)
              ·
                refine ⟨27253404889738324315553315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 72675746372635531508142173 27253404889738324315553315)
                ·
                  refine ⟨40880107334607486473329973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27253404889738324315553315 40880107334607486473329973)
                  ·
                    refine ⟨3832510062619451856874685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 40880107334607486473329973 3832510062619451856874685)
                    ·
                      refine ⟨1437191273482294446328007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3832510062619451856874685 1437191273482294446328007)
                      ·
                        rfl

theorem cell23_2798920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 3, 1, 5, 3].length) (baseStart_2798920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2798920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2798920 prefixEnd_2798920 := by exact prefixLift 2798920
  have htrace : WordTrace (prefixWord ++ tailWord_2798920) baseStart_2798920 baseEnd_2798920 := by
    simpa [prefixWord, tailWord_2798920, baseEnd_2798920] using wordTrace_append hprefix tailTrace_2798920
  have hstable : (prefixWord ++ tailWord_2798920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2798920).length < 2 ^ (prefixWord ++ tailWord_2798920).sum := by decide
  have hdescent : baseEnd_2798920 < baseStart_2798920 := by decide
  rcases family_descends (prefixWord ++ tailWord_2798920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2798921 : List Nat := [1, 2, 1, 1, 2, 3, 6, 1, 2, 2, 2]
def baseStart_2798921 : Nat := 118140960795 + 2798921 * 2 ^ 59
def prefixEnd_2798921 : Nat := 4983230072969 + 3 ^ 40 * 2798921 * 2
def baseEnd_2798921 : Nat := 1437191786962948942415503

theorem tailTrace_2798921 : CollatzResearch.WordTrace tailWord_2798921 prefixEnd_2798921 1437191786962948942415503 := by
  unfold tailWord_2798921
  simp only [CollatzResearch.WordTrace]
  refine ⟨102085035492994709494980617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68056690328663139663320411 102085035492994709494980617)
  ·
    refine ⟨76563776619746032121235463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102085035492994709494980617 76563776619746032121235463)
    ·
      refine ⟨114845664929619048181853195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76563776619746032121235463 114845664929619048181853195)
      ·
        refine ⟨172268497394428572272779793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114845664929619048181853195 172268497394428572272779793)
        ·
          refine ⟨129201373045821429204584845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 172268497394428572272779793 129201373045821429204584845)
          ·
            refine ⟨48450514892183035951719317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 129201373045821429204584845 48450514892183035951719317)
            ·
              refine ⟨2271117885571079810236843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 48450514892183035951719317 2271117885571079810236843)
              ·
                refine ⟨3406676828356619715355265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2271117885571079810236843 3406676828356619715355265)
                ·
                  refine ⟨2555007621267464786516449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3406676828356619715355265 2555007621267464786516449)
                  ·
                    refine ⟨1916255715950598589887337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2555007621267464786516449 1916255715950598589887337)
                    ·
                      refine ⟨1437191786962948942415503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1916255715950598589887337 1437191786962948942415503)
                      ·
                        rfl

theorem cell23_2798921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 6, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 6, 1, 2, 2, 2].length) (baseStart_2798921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2798921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2798921 prefixEnd_2798921 := by exact prefixLift 2798921
  have htrace : WordTrace (prefixWord ++ tailWord_2798921) baseStart_2798921 baseEnd_2798921 := by
    simpa [prefixWord, tailWord_2798921, baseEnd_2798921] using wordTrace_append hprefix tailTrace_2798921
  have hstable : (prefixWord ++ tailWord_2798921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2798921).length < 2 ^ (prefixWord ++ tailWord_2798921).sum := by decide
  have hdescent : baseEnd_2798921 < baseStart_2798921 := by decide
  rcases family_descends (prefixWord ++ tailWord_2798921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2798925 : List Nat := [1, 6, 1, 3, 1, 2, 1, 2, 1, 3, 2]
def baseStart_2798925 : Nat := 118140960795 + 2798925 * 2 ^ 59
def prefixEnd_2798925 : Nat := 4983230072969 + 3 ^ 40 * 2798925 * 2
def baseEnd_2798925 : Nat := 1437193840885566926765485

theorem tailTrace_2798925 : CollatzResearch.WordTrace tailWord_2798925 prefixEnd_2798925 1437193840885566926765485 := by
  unfold tailWord_2798925
  simp only [CollatzResearch.WordTrace]
  refine ⟨102085181384980218178126229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68056787589986812118750819 102085181384980218178126229)
  ·
    refine ⟨4785242877420947727099667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 102085181384980218178126229 4785242877420947727099667)
    ·
      refine ⟨7177864316131421590649501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4785242877420947727099667 7177864316131421590649501)
      ·
        refine ⟨2691699118549283096493563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7177864316131421590649501 2691699118549283096493563)
        ·
          refine ⟨4037548677823924644740345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2691699118549283096493563 4037548677823924644740345)
          ·
            refine ⟨3028161508367943483555259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4037548677823924644740345 3028161508367943483555259)
            ·
              refine ⟨4542242262551915225332889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3028161508367943483555259 4542242262551915225332889)
              ·
                refine ⟨3406681696913936418999667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4542242262551915225332889 3406681696913936418999667)
                ·
                  refine ⟨5110022545370904628499501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3406681696913936418999667 5110022545370904628499501)
                  ·
                    refine ⟨1916258454514089235687313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5110022545370904628499501 1916258454514089235687313)
                    ·
                      refine ⟨1437193840885566926765485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1916258454514089235687313 1437193840885566926765485)
                      ·
                        rfl

theorem cell23_2798925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 2, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 2, 1, 2, 1, 3, 2].length) (baseStart_2798925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2798925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2798925 prefixEnd_2798925 := by exact prefixLift 2798925
  have htrace : WordTrace (prefixWord ++ tailWord_2798925) baseStart_2798925 baseEnd_2798925 := by
    simpa [prefixWord, tailWord_2798925, baseEnd_2798925] using wordTrace_append hprefix tailTrace_2798925
  have hstable : (prefixWord ++ tailWord_2798925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2798925).length < 2 ^ (prefixWord ++ tailWord_2798925).sum := by decide
  have hdescent : baseEnd_2798925 < baseStart_2798925 := by decide
  rcases family_descends (prefixWord ++ tailWord_2798925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2798957 : List Nat := [1, 5, 1, 1, 1, 3, 2, 2, 2, 5]
def baseStart_2798957 : Nat := 118140960795 + 2798957 * 2 ^ 59
def prefixEnd_2798957 : Nat := 4983230072969 + 3 ^ 40 * 2798957 * 2
def baseEnd_2798957 : Nat := 479070090755503600521779

theorem tailTrace_2798957 : CollatzResearch.WordTrace tailWord_2798957 prefixEnd_2798957 479070090755503600521779 := by
  unfold tailWord_2798957
  simp only [CollatzResearch.WordTrace]
  refine ⟨102086348520864287643291125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68057565680576191762194083 102086348520864287643291125)
  ·
    refine ⟨9570595173831026966558543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 102086348520864287643291125 9570595173831026966558543)
    ·
      refine ⟨14355892760746540449837815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9570595173831026966558543 14355892760746540449837815)
      ·
        refine ⟨21533839141119810674756723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14355892760746540449837815 21533839141119810674756723)
        ·
          refine ⟨32300758711679716012135085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21533839141119810674756723 32300758711679716012135085)
          ·
            refine ⟨12112784516879893504550657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32300758711679716012135085 12112784516879893504550657)
            ·
              refine ⟨9084588387659920128412993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12112784516879893504550657 9084588387659920128412993)
              ·
                refine ⟨6813441290744940096309745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9084588387659920128412993 6813441290744940096309745)
                ·
                  refine ⟨5110080968058705072232309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6813441290744940096309745 5110080968058705072232309)
                  ·
                    refine ⟨479070090755503600521779, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5110080968058705072232309 479070090755503600521779)
                    ·
                      rfl

theorem cell23_2798957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 2, 2, 2, 5].length) (baseStart_2798957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2798957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2798957 prefixEnd_2798957 := by exact prefixLift 2798957
  have htrace : WordTrace (prefixWord ++ tailWord_2798957) baseStart_2798957 baseEnd_2798957 := by
    simpa [prefixWord, tailWord_2798957, baseEnd_2798957] using wordTrace_append hprefix tailTrace_2798957
  have hstable : (prefixWord ++ tailWord_2798957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2798957).length < 2 ^ (prefixWord ++ tailWord_2798957).sum := by decide
  have hdescent : baseEnd_2798957 < baseStart_2798957 := by decide
  rcases family_descends (prefixWord ++ tailWord_2798957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2798987 : List Nat := [1, 1, 1, 1, 4, 3, 3, 2, 3, 4]
def baseStart_2798987 : Nat := 118140960795 + 2798987 * 2 ^ 59
def prefixEnd_2798987 : Nat := 4983230072969 + 3 ^ 40 * 2798987 * 2
def baseEnd_2798987 : Nat := 479075225562048561396733

theorem tailTrace_2798987 : CollatzResearch.WordTrace tailWord_2798987 prefixEnd_2798987 479075225562048561396733 := by
  unfold tailWord_2798987
  simp only [CollatzResearch.WordTrace]
  refine ⟨102087442710755602766883215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68058295140503735177922143 102087442710755602766883215)
  ·
    refine ⟨153131164066133404150324823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102087442710755602766883215 153131164066133404150324823)
    ·
      refine ⟨229696746099200106225487235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 153131164066133404150324823 229696746099200106225487235)
      ·
        refine ⟨344545119148800159338230853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 229696746099200106225487235 344545119148800159338230853)
        ·
          refine ⟨64602209840400029875918285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 344545119148800159338230853 64602209840400029875918285)
          ·
            refine ⟨24225828690150011203469357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 64602209840400029875918285 24225828690150011203469357)
            ·
              refine ⟨9084685758806254201301009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24225828690150011203469357 9084685758806254201301009)
              ·
                refine ⟨6813514319104690650975757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9084685758806254201301009 6813514319104690650975757)
                ·
                  refine ⟨2555067869664258994115909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6813514319104690650975757 2555067869664258994115909)
                  ·
                    refine ⟨479075225562048561396733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2555067869664258994115909 479075225562048561396733)
                    ·
                      rfl

theorem cell23_2798987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 3, 2, 3, 4].length) (baseStart_2798987 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2798987 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2798987 prefixEnd_2798987 := by exact prefixLift 2798987
  have htrace : WordTrace (prefixWord ++ tailWord_2798987) baseStart_2798987 baseEnd_2798987 := by
    simpa [prefixWord, tailWord_2798987, baseEnd_2798987] using wordTrace_append hprefix tailTrace_2798987
  have hstable : (prefixWord ++ tailWord_2798987).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2798987).length < 2 ^ (prefixWord ++ tailWord_2798987).sum := by decide
  have hdescent : baseEnd_2798987 < baseStart_2798987 := by decide
  rcases family_descends (prefixWord ++ tailWord_2798987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2799020 : List Nat := [2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 6]
def baseStart_2799020 : Nat := 118140960795 + 2799020 * 2 ^ 59
def prefixEnd_2799020 : Nat := 4983230072969 + 3 ^ 40 * 2799020 * 2
def baseEnd_2799020 : Nat := 1437242621547744055077547

theorem tailTrace_2799020 : CollatzResearch.WordTrace tailWord_2799020 prefixEnd_2799020 1437242621547744055077547 := by
  unfold tailWord_2799020
  simp only [CollatzResearch.WordTrace]
  refine ⟨51044323159818024701417257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68059097546424032935223009 51044323159818024701417257)
  ·
    refine ⟨38283242369863518526062943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51044323159818024701417257 38283242369863518526062943)
    ·
      refine ⟨57424863554795277789094415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38283242369863518526062943 57424863554795277789094415)
      ·
        refine ⟨86137295332192916683641623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57424863554795277789094415 86137295332192916683641623)
        ·
          refine ⟨129205942998289375025462435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86137295332192916683641623 129205942998289375025462435)
          ·
            refine ⟨193808914497434062538193653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 129205942998289375025462435 193808914497434062538193653)
            ·
              refine ⟨18169585734134443362955655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 193808914497434062538193653 18169585734134443362955655)
              ·
                refine ⟨27254378601201665044433483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18169585734134443362955655 27254378601201665044433483)
                ·
                  refine ⟨40881567901802497566650225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27254378601201665044433483 40881567901802497566650225)
                  ·
                    refine ⟨30661175926351873174987669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 40881567901802497566650225 30661175926351873174987669)
                    ·
                      refine ⟨1437242621547744055077547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 30661175926351873174987669 1437242621547744055077547)
                      ·
                        rfl

theorem cell23_2799020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 6].length) (baseStart_2799020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2799020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2799020 prefixEnd_2799020 := by exact prefixLift 2799020
  have htrace : WordTrace (prefixWord ++ tailWord_2799020) baseStart_2799020 baseEnd_2799020 := by
    simpa [prefixWord, tailWord_2799020, baseEnd_2799020] using wordTrace_append hprefix tailTrace_2799020
  have hstable : (prefixWord ++ tailWord_2799020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2799020).length < 2 ^ (prefixWord ++ tailWord_2799020).sum := by decide
  have hdescent : baseEnd_2799020 < baseStart_2799020 := by decide
  rcases family_descends (prefixWord ++ tailWord_2799020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2799021 : List Nat := [1, 5, 2, 2, 1, 2, 2, 1, 3, 4]
def baseStart_2799021 : Nat := 118140960795 + 2799021 * 2 ^ 59
def prefixEnd_2799021 : Nat := 4983230072969 + 3 ^ 40 * 2799021 * 2
def baseEnd_2799021 : Nat := 479081045009466183721681

theorem tailTrace_2799021 : CollatzResearch.WordTrace tailWord_2799021 prefixEnd_2799021 479081045009466183721681 := by
  unfold tailWord_2799021
  simp only [CollatzResearch.WordTrace]
  refine ⟨102088682792632426573620917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68059121861754951049080611 102088682792632426573620917)
  ·
    refine ⟨9570814011809289991276961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 102088682792632426573620917 9570814011809289991276961)
    ·
      refine ⟨7178110508856967493457721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9570814011809289991276961 7178110508856967493457721)
      ·
        refine ⟨5383582881642725620093291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7178110508856967493457721 5383582881642725620093291)
        ·
          refine ⟨8075374322464088430139937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5383582881642725620093291 8075374322464088430139937)
          ·
            refine ⟨6056530741848066322604953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8075374322464088430139937 6056530741848066322604953)
            ·
              refine ⟨4542398056386049741953715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6056530741848066322604953 4542398056386049741953715)
              ·
                refine ⟨6813597084579074612930573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4542398056386049741953715 6813597084579074612930573)
                ·
                  refine ⟨2555098906717152979848965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6813597084579074612930573 2555098906717152979848965)
                  ·
                    refine ⟨479081045009466183721681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2555098906717152979848965 479081045009466183721681)
                    ·
                      rfl

theorem cell23_2799021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 2, 2, 1, 3, 4].length) (baseStart_2799021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2799021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2799021 prefixEnd_2799021 := by exact prefixLift 2799021
  have htrace : WordTrace (prefixWord ++ tailWord_2799021) baseStart_2799021 baseEnd_2799021 := by
    simpa [prefixWord, tailWord_2799021, baseEnd_2799021] using wordTrace_append hprefix tailTrace_2799021
  have hstable : (prefixWord ++ tailWord_2799021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2799021).length < 2 ^ (prefixWord ++ tailWord_2799021).sum := by decide
  have hdescent : baseEnd_2799021 < baseStart_2799021 := by decide
  rcases family_descends (prefixWord ++ tailWord_2799021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2799040 : List Nat := [2, 1, 1, 2, 3, 1, 2, 1, 2, 1, 7]
def baseStart_2799040 : Nat := 118140960795 + 2799040 * 2 ^ 59
def prefixEnd_2799040 : Nat := 4983230072969 + 3 ^ 40 * 2799040 * 2
def baseEnd_2799040 : Nat := 1437252891160833976827455

theorem tailTrace_2799040 : CollatzResearch.WordTrace tailWord_2799040 prefixEnd_2799040 1437252891160833976827455 := by
  unfold tailWord_2799040
  simp only [CollatzResearch.WordTrace]
  refine ⟨51044687889781796409281287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68059583853042395212375049 51044687889781796409281287)
  ·
    refine ⟨76567031834672694613921931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51044687889781796409281287 76567031834672694613921931)
    ·
      refine ⟨114850547752009041920882897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76567031834672694613921931 114850547752009041920882897)
      ·
        refine ⟨86137910814006781440662173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 114850547752009041920882897 86137910814006781440662173)
        ·
          refine ⟨32301716555252543040248315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 86137910814006781440662173 32301716555252543040248315)
          ·
            refine ⟨48452574832878814560372473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32301716555252543040248315 48452574832878814560372473)
            ·
              refine ⟨36339431124659110920279355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48452574832878814560372473 36339431124659110920279355)
              ·
                refine ⟨54509146686988666380419033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36339431124659110920279355 54509146686988666380419033)
                ·
                  refine ⟨40881860015241499785314275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 54509146686988666380419033 40881860015241499785314275)
                  ·
                    refine ⟨61322790022862249677971413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 40881860015241499785314275 61322790022862249677971413)
                    ·
                      refine ⟨1437252891160833976827455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 61322790022862249677971413 1437252891160833976827455)
                      ·
                        rfl

theorem cell23_2799040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 2, 1, 2, 1, 7].length) (baseStart_2799040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2799040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2799040 prefixEnd_2799040 := by exact prefixLift 2799040
  have htrace : WordTrace (prefixWord ++ tailWord_2799040) baseStart_2799040 baseEnd_2799040 := by
    simpa [prefixWord, tailWord_2799040, baseEnd_2799040] using wordTrace_append hprefix tailTrace_2799040
  have hstable : (prefixWord ++ tailWord_2799040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2799040).length < 2 ^ (prefixWord ++ tailWord_2799040).sum := by decide
  have hdescent : baseEnd_2799040 < baseStart_2799040 := by decide
  rcases family_descends (prefixWord ++ tailWord_2799040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2799054 : List Nat := [4, 1, 1, 1, 2, 1, 4, 1, 1, 5, 2]
def baseStart_2799054 : Nat := 118140960795 + 2799054 * 2 ^ 59
def prefixEnd_2799054 : Nat := 4983230072969 + 3 ^ 40 * 2799054 * 2
def baseEnd_2799054 : Nat := 1437260079889996922052391

theorem tailTrace_2799054 : CollatzResearch.WordTrace tailWord_2799054 prefixEnd_2799054 1437260079889996922052391 := by
  unfold tailWord_2799054
  simp only [CollatzResearch.WordTrace]
  refine ⟨12761235800189109151196527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 68059924267675248806381477 12761235800189109151196527)
  ·
    refine ⟨19141853700283663726794791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12761235800189109151196527 19141853700283663726794791)
    ·
      refine ⟨28712780550425495590192187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19141853700283663726794791 28712780550425495590192187)
      ·
        refine ⟨43069170825638243385288281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28712780550425495590192187 43069170825638243385288281)
        ·
          refine ⟨32301878119228682538966211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43069170825638243385288281 32301878119228682538966211)
          ·
            refine ⟨48452817178843023808449317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32301878119228682538966211 48452817178843023808449317)
            ·
              refine ⟨9084903221033066964084247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 48452817178843023808449317 9084903221033066964084247)
              ·
                refine ⟨13627354831549600446126371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9084903221033066964084247 13627354831549600446126371)
                ·
                  refine ⟨20441032247324400669189557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13627354831549600446126371 20441032247324400669189557)
                  ·
                    refine ⟨1916346773186662562736521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 20441032247324400669189557 1916346773186662562736521)
                    ·
                      refine ⟨1437260079889996922052391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1916346773186662562736521 1437260079889996922052391)
                      ·
                        rfl

theorem cell23_2799054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 4, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 4, 1, 1, 5, 2].length) (baseStart_2799054 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2799054 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2799054 prefixEnd_2799054 := by exact prefixLift 2799054
  have htrace : WordTrace (prefixWord ++ tailWord_2799054) baseStart_2799054 baseEnd_2799054 := by
    simpa [prefixWord, tailWord_2799054, baseEnd_2799054] using wordTrace_append hprefix tailTrace_2799054
  have hstable : (prefixWord ++ tailWord_2799054).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2799054).length < 2 ^ (prefixWord ++ tailWord_2799054).sum := by decide
  have hdescent : baseEnd_2799054 < baseStart_2799054 := by decide
  rcases family_descends (prefixWord ++ tailWord_2799054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2799087 : List Nat := [1, 1, 2, 1, 4, 1, 4, 2, 1, 1, 5]
def baseStart_2799087 : Nat := 118140960795 + 2799087 * 2 ^ 59
def prefixEnd_2799087 : Nat := 4983230072969 + 3 ^ 40 * 2799087 * 2
def baseEnd_2799087 : Nat := 1437277024751595292939739

theorem tailTrace_2799087 : CollatzResearch.WordTrace tailWord_2799087 prefixEnd_2799087 1437277024751595292939739 := by
  unfold tailWord_2799087
  simp only [CollatzResearch.WordTrace]
  refine ⟨102091090010393319845523515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68060726673595546563682343 102091090010393319845523515)
  ·
    refine ⟨153136635015589979768285273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102091090010393319845523515 153136635015589979768285273)
    ·
      refine ⟨114852476261692484826213955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 153136635015589979768285273 114852476261692484826213955)
      ·
        refine ⟨172278714392538727239320933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114852476261692484826213955 172278714392538727239320933)
        ·
          refine ⟨32302258948601011357372675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 172278714392538727239320933 32302258948601011357372675)
          ·
            refine ⟨48453388422901517036059013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32302258948601011357372675 48453388422901517036059013)
            ·
              refine ⟨9085010329294034444261065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 48453388422901517036059013 9085010329294034444261065)
              ·
                refine ⟨6813757746970525833195799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9085010329294034444261065 6813757746970525833195799)
                ·
                  refine ⟨10220636620455788749793699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6813757746970525833195799 10220636620455788749793699)
                  ·
                    refine ⟨15330954930683683124690549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10220636620455788749793699 15330954930683683124690549)
                    ·
                      refine ⟨1437277024751595292939739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15330954930683683124690549 1437277024751595292939739)
                      ·
                        rfl

theorem cell23_2799087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 4, 2, 1, 1, 5].length) (baseStart_2799087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2799087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2799087 prefixEnd_2799087 := by exact prefixLift 2799087
  have htrace : WordTrace (prefixWord ++ tailWord_2799087) baseStart_2799087 baseEnd_2799087 := by
    simpa [prefixWord, tailWord_2799087, baseEnd_2799087] using wordTrace_append hprefix tailTrace_2799087
  have hstable : (prefixWord ++ tailWord_2799087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2799087).length < 2 ^ (prefixWord ++ tailWord_2799087).sum := by decide
  have hdescent : baseEnd_2799087 < baseStart_2799087 := by decide
  rcases family_descends (prefixWord ++ tailWord_2799087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2799097 : List Nat := [1, 2, 1, 3, 1, 2, 1, 5, 1, 2, 4]
def baseStart_2799097 : Nat := 118140960795 + 2799097 * 2 ^ 59
def prefixEnd_2799097 : Nat := 4983230072969 + 3 ^ 40 * 2799097 * 2
def baseEnd_2799097 : Nat := 1437282159558140253814693

theorem tailTrace_2799097 : CollatzResearch.WordTrace tailWord_2799097 prefixEnd_2799097 1437282159558140253814693 := by
  unfold tailWord_2799097
  simp only [CollatzResearch.WordTrace]
  refine ⟨102091454740357091553387545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68060969826904727702258363 102091454740357091553387545)
  ·
    refine ⟨76568591055267818665040659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102091454740357091553387545 76568591055267818665040659)
    ·
      refine ⟨114852886582901727997560989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76568591055267818665040659 114852886582901727997560989)
      ·
        refine ⟨43069832468588147999085371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 114852886582901727997560989 43069832468588147999085371)
        ·
          refine ⟨64604748702882221998628057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43069832468588147999085371 64604748702882221998628057)
          ·
            refine ⟨48453561527161666498971043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64604748702882221998628057 48453561527161666498971043)
            ·
              refine ⟨72680342290742499748456565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48453561527161666498971043 72680342290742499748456565)
              ·
                refine ⟨6813782089757109351417803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 72680342290742499748456565 6813782089757109351417803)
                ·
                  refine ⟨10220673134635664027126705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6813782089757109351417803 10220673134635664027126705)
                  ·
                    refine ⟨7665504850976748020345029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10220673134635664027126705 7665504850976748020345029)
                    ·
                      refine ⟨1437282159558140253814693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7665504850976748020345029 1437282159558140253814693)
                      ·
                        rfl

theorem cell23_2799097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 5, 1, 2, 4].length) (baseStart_2799097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2799097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2799097 prefixEnd_2799097 := by exact prefixLift 2799097
  have htrace : WordTrace (prefixWord ++ tailWord_2799097) baseStart_2799097 baseEnd_2799097 := by
    simpa [prefixWord, tailWord_2799097, baseEnd_2799097] using wordTrace_append hprefix tailTrace_2799097
  have hstable : (prefixWord ++ tailWord_2799097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2799097).length < 2 ^ (prefixWord ++ tailWord_2799097).sum := by decide
  have hdescent : baseEnd_2799097 < baseStart_2799097 := by decide
  rcases family_descends (prefixWord ++ tailWord_2799097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2799101 : List Nat := [1, 4, 1, 1, 1, 6, 1, 2, 1, 1, 4]
def baseStart_2799101 : Nat := 118140960795 + 2799101 * 2 ^ 59
def prefixEnd_2799101 : Nat := 4983230072969 + 3 ^ 40 * 2799101 * 2
def baseEnd_2799101 : Nat := 1437284213480758238164675

theorem tailTrace_2799101 : CollatzResearch.WordTrace tailWord_2799101 prefixEnd_2799101 1437284213480758238164675 := by
  unfold tailWord_2799101
  simp only [CollatzResearch.WordTrace]
  refine ⟨102091600632342600236533157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68061067088228400157688771 102091600632342600236533157)
  ·
    refine ⟨19142175118564237544349967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 102091600632342600236533157 19142175118564237544349967)
    ·
      refine ⟨28713262677846356316524951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19142175118564237544349967 28713262677846356316524951)
      ·
        refine ⟨43069894016769534474787427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28713262677846356316524951 43069894016769534474787427)
        ·
          refine ⟨64604841025154301712181141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43069894016769534474787427 64604841025154301712181141)
          ·
            refine ⟨3028351923054107892758491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 64604841025154301712181141 3028351923054107892758491)
            ·
              refine ⟨4542527884581161839137737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3028351923054107892758491 4542527884581161839137737)
              ·
                refine ⟨3406895913435871379353303, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4542527884581161839137737 3406895913435871379353303)
                ·
                  refine ⟨5110343870153807069029955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3406895913435871379353303 5110343870153807069029955)
                  ·
                    refine ⟨7665515805230710603544933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5110343870153807069029955 7665515805230710603544933)
                    ·
                      refine ⟨1437284213480758238164675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7665515805230710603544933 1437284213480758238164675)
                      ·
                        rfl

theorem cell23_2799101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 6, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 6, 1, 2, 1, 1, 4].length) (baseStart_2799101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2799101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2799101 prefixEnd_2799101 := by exact prefixLift 2799101
  have htrace : WordTrace (prefixWord ++ tailWord_2799101) baseStart_2799101 baseEnd_2799101 := by
    simpa [prefixWord, tailWord_2799101, baseEnd_2799101] using wordTrace_append hprefix tailTrace_2799101
  have hstable : (prefixWord ++ tailWord_2799101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2799101).length < 2 ^ (prefixWord ++ tailWord_2799101).sum := by decide
  have hdescent : baseEnd_2799101 < baseStart_2799101 := by decide
  rcases family_descends (prefixWord ++ tailWord_2799101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2799114 : List Nat := [3, 1, 2, 2, 2, 3, 1, 2, 1, 2, 4]
def baseStart_2799114 : Nat := 118140960795 + 2799114 * 2 ^ 59
def prefixEnd_2799114 : Nat := 4983230072969 + 3 ^ 40 * 2799114 * 2
def baseEnd_2799114 : Nat := 1437290888729266687302115

theorem tailTrace_2799114 : CollatzResearch.WordTrace tailWord_2799114 prefixEnd_2799114 1437290888729266687302115 := by
  unfold tailWord_2799114
  simp only [CollatzResearch.WordTrace]
  refine ⟨25523018695323875864189099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68061383187530335637837597 25523018695323875864189099)
  ·
    refine ⟨38284528042985813796283649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25523018695323875864189099 38284528042985813796283649)
    ·
      refine ⟨28713396032239360347212737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38284528042985813796283649 28713396032239360347212737)
      ·
        refine ⟨21535047024179520260409553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28713396032239360347212737 21535047024179520260409553)
        ·
          refine ⟨16151285268134640195307165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21535047024179520260409553 16151285268134640195307165)
          ·
            refine ⟨6056731975550490073240187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16151285268134640195307165 6056731975550490073240187)
            ·
              refine ⟨9085097963325735109860281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6056731975550490073240187 9085097963325735109860281)
              ·
                refine ⟨6813823472494301332395211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9085097963325735109860281 6813823472494301332395211)
                ·
                  refine ⟨10220735208741451998592817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6813823472494301332395211 10220735208741451998592817)
                  ·
                    refine ⟨7665551406556088998944613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10220735208741451998592817 7665551406556088998944613)
                    ·
                      refine ⟨1437290888729266687302115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7665551406556088998944613 1437290888729266687302115)
                      ·
                        rfl

theorem cell23_2799114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 3, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 3, 1, 2, 1, 2, 4].length) (baseStart_2799114 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2799114 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2799114 prefixEnd_2799114 := by exact prefixLift 2799114
  have htrace : WordTrace (prefixWord ++ tailWord_2799114) baseStart_2799114 baseEnd_2799114 := by
    simpa [prefixWord, tailWord_2799114, baseEnd_2799114] using wordTrace_append hprefix tailTrace_2799114
  have hstable : (prefixWord ++ tailWord_2799114).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2799114).length < 2 ^ (prefixWord ++ tailWord_2799114).sum := by decide
  have hdescent : baseEnd_2799114 < baseStart_2799114 := by decide
  rcases family_descends (prefixWord ++ tailWord_2799114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2799118 : List Nat := [4, 1, 1, 2, 4, 1, 3, 1, 1, 1, 4]
def baseStart_2799118 : Nat := 118140960795 + 2799118 * 2 ^ 59
def prefixEnd_2799118 : Nat := 4983230072969 + 3 ^ 40 * 2799118 * 2
def baseEnd_2799118 : Nat := 1437292942651884671652097

theorem tailTrace_2799118 : CollatzResearch.WordTrace tailWord_2799118 prefixEnd_2799118 1437292942651884671652097 := by
  unfold tailWord_2799118
  simp only [CollatzResearch.WordTrace]
  refine ⟨12761527584160126517487751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 68061480448854008093268005 12761527584160126517487751)
  ·
    refine ⟨19142291376240189776231627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12761527584160126517487751 19142291376240189776231627)
    ·
      refine ⟨28713437064360284664347441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19142291376240189776231627 28713437064360284664347441)
      ·
        refine ⟨21535077798270213498260581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28713437064360284664347441 21535077798270213498260581)
        ·
          refine ⟨4037827087175665030923859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21535077798270213498260581 4037827087175665030923859)
          ·
            refine ⟨6056740630763497546385789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4037827087175665030923859 6056740630763497546385789)
            ·
              refine ⟨2271277736536311579894671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6056740630763497546385789 2271277736536311579894671)
              ·
                refine ⟨3406916604804467369842007, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2271277736536311579894671 3406916604804467369842007)
                ·
                  refine ⟨5110374907206701054763011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3406916604804467369842007 5110374907206701054763011)
                  ·
                    refine ⟨7665562360810051582144517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5110374907206701054763011 7665562360810051582144517)
                    ·
                      refine ⟨1437292942651884671652097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7665562360810051582144517 1437292942651884671652097)
                      ·
                        rfl

theorem cell23_2799118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 1, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 1, 3, 1, 1, 1, 4].length) (baseStart_2799118 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2799118 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2799118 prefixEnd_2799118 := by exact prefixLift 2799118
  have htrace : WordTrace (prefixWord ++ tailWord_2799118) baseStart_2799118 baseEnd_2799118 := by
    simpa [prefixWord, tailWord_2799118, baseEnd_2799118] using wordTrace_append hprefix tailTrace_2799118
  have hstable : (prefixWord ++ tailWord_2799118).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2799118).length < 2 ^ (prefixWord ++ tailWord_2799118).sum := by decide
  have hdescent : baseEnd_2799118 < baseStart_2799118 := by decide
  rcases family_descends (prefixWord ++ tailWord_2799118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2799121 : List Nat := [1, 2, 2, 1, 1, 2, 7, 1, 1, 2, 3]
def baseStart_2799121 : Nat := 118140960795 + 2799121 * 2 ^ 59
def prefixEnd_2799121 : Nat := 4983230072969 + 3 ^ 40 * 2799121 * 2
def baseEnd_2799121 : Nat := 1437294483093848159914583

theorem tailTrace_2799121 : CollatzResearch.WordTrace tailWord_2799121 prefixEnd_2799121 1437294483093848159914583 := by
  unfold tailWord_2799121
  simp only [CollatzResearch.WordTrace]
  refine ⟨102092330092270143652261217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68061553394846762434840811 102092330092270143652261217)
  ·
    refine ⟨76569247569202607739195913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102092330092270143652261217 76569247569202607739195913)
    ·
      refine ⟨57426935676901955804396935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76569247569202607739195913 57426935676901955804396935)
      ·
        refine ⟨86140403515352933706595403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57426935676901955804396935 86140403515352933706595403)
        ·
          refine ⟨129210605273029400559893105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86140403515352933706595403 129210605273029400559893105)
          ·
            refine ⟨96907953954772050419919829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 129210605273029400559893105 96907953954772050419919829)
            ·
              refine ⟨2271280170814969931716871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 96907953954772050419919829 2271280170814969931716871)
              ·
                refine ⟨3406920256222454897575307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2271280170814969931716871 3406920256222454897575307)
                ·
                  refine ⟨5110380384333682346362961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3406920256222454897575307 5110380384333682346362961)
                  ·
                    refine ⟨3832785288250261759772221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5110380384333682346362961 3832785288250261759772221)
                    ·
                      refine ⟨1437294483093848159914583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3832785288250261759772221 1437294483093848159914583)
                      ·
                        rfl

theorem cell23_2799121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 7, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 7, 1, 1, 2, 3].length) (baseStart_2799121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2799121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2799121 prefixEnd_2799121 := by exact prefixLift 2799121
  have htrace : WordTrace (prefixWord ++ tailWord_2799121) baseStart_2799121 baseEnd_2799121 := by
    simpa [prefixWord, tailWord_2799121, baseEnd_2799121] using wordTrace_append hprefix tailTrace_2799121
  have hstable : (prefixWord ++ tailWord_2799121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2799121).length < 2 ^ (prefixWord ++ tailWord_2799121).sum := by decide
  have hdescent : baseEnd_2799121 < baseStart_2799121 := by decide
  rcases family_descends (prefixWord ++ tailWord_2799121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2799124 : List Nat := [2, 4, 3, 1, 2, 11]
def baseStart_2799124 : Nat := 118140960795 + 2799124 * 2 ^ 59
def prefixEnd_2799124 : Nat := 4983230072969 + 3 ^ 40 * 2799124 * 2
def baseEnd_2799124 : Nat := 5914798450764656988383

theorem tailTrace_2799124 : CollatzResearch.WordTrace tailWord_2799124 prefixEnd_2799124 5914798450764656988383 := by
  unfold tailWord_2799124
  simp only [CollatzResearch.WordTrace]
  refine ⟨51046219755629637582310213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68061626340839516776413617 51046219755629637582310213)
  ·
    refine ⟨9571166204180557046683165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 51046219755629637582310213 9571166204180557046683165)
    ·
      refine ⟨3589187326567708892506187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9571166204180557046683165 3589187326567708892506187)
      ·
        refine ⟨5383780989851563338759281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3589187326567708892506187 5383780989851563338759281)
        ·
          refine ⟨4037835742388672504069461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5383780989851563338759281 4037835742388672504069461)
          ·
            refine ⟨5914798450764656988383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 4037835742388672504069461 5914798450764656988383)
            ·
              rfl

theorem cell23_2799124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 11].length) (baseStart_2799124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2799124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2799124 prefixEnd_2799124 := by exact prefixLift 2799124
  have htrace : WordTrace (prefixWord ++ tailWord_2799124) baseStart_2799124 baseEnd_2799124 := by
    simpa [prefixWord, tailWord_2799124, baseEnd_2799124] using wordTrace_append hprefix tailTrace_2799124
  have hstable : (prefixWord ++ tailWord_2799124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2799124).length < 2 ^ (prefixWord ++ tailWord_2799124).sum := by decide
  have hdescent : baseEnd_2799124 < baseStart_2799124 := by decide
  rcases family_descends (prefixWord ++ tailWord_2799124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2799135 : List Nat := [1, 1, 2, 4, 1, 1, 6, 2, 1, 2, 2]
def baseStart_2799135 : Nat := 118140960795 + 2799135 * 2 ^ 59
def prefixEnd_2799135 : Nat := 4983230072969 + 3 ^ 40 * 2799135 * 2
def baseEnd_2799135 : Nat := 1437301671823011105139519

theorem tailTrace_2799135 : CollatzResearch.WordTrace tailWord_2799135 prefixEnd_2799135 1437301671823011105139519 := by
  unfold tailWord_2799135
  simp only [CollatzResearch.WordTrace]
  refine ⟨102092840714219424043270859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68061893809479616028847239 102092840714219424043270859)
  ·
    refine ⟨153139261071329136064906289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102092840714219424043270859 153139261071329136064906289)
    ·
      refine ⟨114854445803496852048679717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 153139261071329136064906289 114854445803496852048679717)
      ·
        refine ⟨21535208588155659759127447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 114854445803496852048679717 21535208588155659759127447)
        ·
          refine ⟨32302812882233489638691171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21535208588155659759127447 32302812882233489638691171)
          ·
            refine ⟨48454219323350234458036757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32302812882233489638691171 48454219323350234458036757)
            ·
              refine ⟨2271291530782042240220473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 48454219323350234458036757 2271291530782042240220473)
              ·
                refine ⟨1703468648086531680165355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2271291530782042240220473 1703468648086531680165355)
                ·
                  refine ⟨2555202972129797520248033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1703468648086531680165355 2555202972129797520248033)
                  ·
                    refine ⟨1916402229097348140186025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2555202972129797520248033 1916402229097348140186025)
                    ·
                      refine ⟨1437301671823011105139519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1916402229097348140186025 1437301671823011105139519)
                      ·
                        rfl

theorem cell23_2799135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 6, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 6, 2, 1, 2, 2].length) (baseStart_2799135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2799135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2799135 prefixEnd_2799135 := by exact prefixLift 2799135
  have htrace : WordTrace (prefixWord ++ tailWord_2799135) baseStart_2799135 baseEnd_2799135 := by
    simpa [prefixWord, tailWord_2799135, baseEnd_2799135] using wordTrace_append hprefix tailTrace_2799135
  have hstable : (prefixWord ++ tailWord_2799135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2799135).length < 2 ^ (prefixWord ++ tailWord_2799135).sum := by decide
  have hdescent : baseEnd_2799135 < baseStart_2799135 := by decide
  rcases family_descends (prefixWord ++ tailWord_2799135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2799137 : List Nat := [1, 2, 3, 2, 2, 2, 1, 1, 2, 7]
def baseStart_2799137 : Nat := 118140960795 + 2799137 * 2 ^ 59
def prefixEnd_2799137 : Nat := 4983230072969 + 3 ^ 40 * 2799137 * 2
def baseEnd_2799137 : Nat := 479100899594773365771503

theorem tailTrace_2799137 : CollatzResearch.WordTrace tailWord_2799137 prefixEnd_2799137 479100899594773365771503 := by
  unfold tailWord_2799137
  simp only [CollatzResearch.WordTrace]
  refine ⟨102092913660212178384843665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68061942440141452256562443 102092913660212178384843665)
  ·
    refine ⟨76569685245159133788632749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102092913660212178384843665 76569685245159133788632749)
    ·
      refine ⟨28713631966934675170737281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 76569685245159133788632749 28713631966934675170737281)
      ·
        refine ⟨21535223975201006378052961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28713631966934675170737281 21535223975201006378052961)
        ·
          refine ⟨16151417981400754783539721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21535223975201006378052961 16151417981400754783539721)
          ·
            refine ⟨12113563486050566087654791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16151417981400754783539721 12113563486050566087654791)
            ·
              refine ⟨18170345229075849131482187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12113563486050566087654791 18170345229075849131482187)
              ·
                refine ⟨27255517843613773697223281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18170345229075849131482187 27255517843613773697223281)
                ·
                  refine ⟨20441638382710330272917461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27255517843613773697223281 20441638382710330272917461)
                  ·
                    refine ⟨479100899594773365771503, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 20441638382710330272917461 479100899594773365771503)
                    ·
                      rfl

theorem cell23_2799137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 1, 1, 2, 7].length) (baseStart_2799137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2799137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2799137 prefixEnd_2799137 := by exact prefixLift 2799137
  have htrace : WordTrace (prefixWord ++ tailWord_2799137) baseStart_2799137 baseEnd_2799137 := by
    simpa [prefixWord, tailWord_2799137, baseEnd_2799137] using wordTrace_append hprefix tailTrace_2799137
  have hstable : (prefixWord ++ tailWord_2799137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2799137).length < 2 ^ (prefixWord ++ tailWord_2799137).sum := by decide
  have hdescent : baseEnd_2799137 < baseStart_2799137 := by decide
  rcases family_descends (prefixWord ++ tailWord_2799137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2799161 : List Nat := [1, 2, 1, 5, 1, 2, 2, 1, 3, 3, 2]
def baseStart_2799161 : Nat := 118140960795 + 2799161 * 2 ^ 59
def prefixEnd_2799161 : Nat := 4983230072969 + 3 ^ 40 * 2799161 * 2
def baseEnd_2799161 : Nat := 1437315022320028003414399

theorem tailTrace_2799161 : CollatzResearch.WordTrace tailWord_2799161 prefixEnd_2799161 1437315022320028003414399 := by
  unfold tailWord_2799161
  simp only [CollatzResearch.WordTrace]
  refine ⟨102093789012125230483717337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68062526008083486989144891 102093789012125230483717337)
  ·
    refine ⟨76570341759093922862788003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102093789012125230483717337 76570341759093922862788003)
    ·
      refine ⟨114855512638640884294182005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76570341759093922862788003 114855512638640884294182005)
      ·
        refine ⟨10767704309872582902579563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 114855512638640884294182005 10767704309872582902579563)
        ·
          refine ⟨16151556464808874353869345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10767704309872582902579563 16151556464808874353869345)
          ·
            refine ⟨12113667348606655765402009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16151556464808874353869345 12113667348606655765402009)
            ·
              refine ⟨9085250511454991824051507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12113667348606655765402009 9085250511454991824051507)
              ·
                refine ⟨13627875767182487736077261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9085250511454991824051507 13627875767182487736077261)
                ·
                  refine ⟨5110453412693432901028973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13627875767182487736077261 5110453412693432901028973)
                  ·
                    refine ⟨1916420029760037337885865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5110453412693432901028973 1916420029760037337885865)
                    ·
                      refine ⟨1437315022320028003414399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1916420029760037337885865 1437315022320028003414399)
                      ·
                        rfl

theorem cell23_2799161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 2, 1, 3, 3, 2].length) (baseStart_2799161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2799161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2799161 prefixEnd_2799161 := by exact prefixLift 2799161
  have htrace : WordTrace (prefixWord ++ tailWord_2799161) baseStart_2799161 baseEnd_2799161 := by
    simpa [prefixWord, tailWord_2799161, baseEnd_2799161] using wordTrace_append hprefix tailTrace_2799161
  have hstable : (prefixWord ++ tailWord_2799161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2799161).length < 2 ^ (prefixWord ++ tailWord_2799161).sum := by decide
  have hdescent : baseEnd_2799161 < baseStart_2799161 := by decide
  rcases family_descends (prefixWord ++ tailWord_2799161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2799177 : List Nat := [1, 2, 1, 1, 2, 2, 1, 5, 2, 1, 5]
def baseStart_2799177 : Nat := 118140960795 + 2799177 * 2 ^ 59
def prefixEnd_2799177 : Nat := 4983230072969 + 3 ^ 40 * 2799177 * 2
def baseEnd_2799177 : Nat := 1437323238010499940814325

theorem tailTrace_2799177 : CollatzResearch.WordTrace tailWord_2799177 prefixEnd_2799177 1437323238010499940814325 := by
  unfold tailWord_2799177
  simp only [CollatzResearch.WordTrace]
  refine ⟨102094372580067265216299785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68062915053378176810866523 102094372580067265216299785)
  ·
    refine ⟨76570779435050448912224839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102094372580067265216299785 76570779435050448912224839)
    ·
      refine ⟨114856169152575673368337259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76570779435050448912224839 114856169152575673368337259)
      ·
        refine ⟨172284253728863510052505889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114856169152575673368337259 172284253728863510052505889)
        ·
          refine ⟨129213190296647632539379417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 172284253728863510052505889 129213190296647632539379417)
          ·
            refine ⟨96909892722485724404534563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 129213190296647632539379417 96909892722485724404534563)
            ·
              refine ⟨145364839083728586606801845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 96909892722485724404534563 145364839083728586606801845)
              ·
                refine ⟨13627953664099554994387673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 145364839083728586606801845 13627953664099554994387673)
                ·
                  refine ⟨10220965248074666245790755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13627953664099554994387673 10220965248074666245790755)
                  ·
                    refine ⟨15331447872111999368686133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10220965248074666245790755 15331447872111999368686133)
                    ·
                      refine ⟨1437323238010499940814325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15331447872111999368686133 1437323238010499940814325)
                      ·
                        rfl

theorem cell23_2799177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 5, 2, 1, 5].length) (baseStart_2799177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2799177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2799177 prefixEnd_2799177 := by exact prefixLift 2799177
  have htrace : WordTrace (prefixWord ++ tailWord_2799177) baseStart_2799177 baseEnd_2799177 := by
    simpa [prefixWord, tailWord_2799177, baseEnd_2799177] using wordTrace_append hprefix tailTrace_2799177
  have hstable : (prefixWord ++ tailWord_2799177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2799177).length < 2 ^ (prefixWord ++ tailWord_2799177).sum := by decide
  have hdescent : baseEnd_2799177 < baseStart_2799177 := by decide
  rcases family_descends (prefixWord ++ tailWord_2799177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2799204 : List Nat := [2, 3, 1, 1, 2, 3, 2, 1, 2, 2, 4]
def baseStart_2799204 : Nat := 118140960795 + 2799204 * 2 ^ 59
def prefixEnd_2799204 : Nat := 4983230072969 + 3 ^ 40 * 2799204 * 2
def baseEnd_2799204 : Nat := 1437337101988171335176701

theorem tailTrace_2799204 : CollatzResearch.WordTrace tailWord_2799204 prefixEnd_2799204 1437337101988171335176701 := by
  unfold tailWord_2799204
  simp only [CollatzResearch.WordTrace]
  refine ⟨51047678675484724413766333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68063571567312965885021777 51047678675484724413766333)
  ·
    refine ⟨19142879503306771655162375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51047678675484724413766333 19142879503306771655162375)
    ·
      refine ⟨28714319254960157482743563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19142879503306771655162375 28714319254960157482743563)
      ·
        refine ⟨43071478882440236224115345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28714319254960157482743563 43071478882440236224115345)
        ·
          refine ⟨32303609161830177168086509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43071478882440236224115345 32303609161830177168086509)
          ·
            refine ⟨12113853435686316438032441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32303609161830177168086509 12113853435686316438032441)
            ·
              refine ⟨9085390076764737328524331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12113853435686316438032441 9085390076764737328524331)
              ·
                refine ⟨13628085115147105992786497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9085390076764737328524331 13628085115147105992786497)
                ·
                  refine ⟨10221063836360329494589873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13628085115147105992786497 10221063836360329494589873)
                  ·
                    refine ⟨7665797877270247120942405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10221063836360329494589873 7665797877270247120942405)
                    ·
                      refine ⟨1437337101988171335176701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7665797877270247120942405 1437337101988171335176701)
                      ·
                        rfl

theorem cell23_2799204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 2, 1, 2, 2, 4].length) (baseStart_2799204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2799204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2799204 prefixEnd_2799204 := by exact prefixLift 2799204
  have htrace : WordTrace (prefixWord ++ tailWord_2799204) baseStart_2799204 baseEnd_2799204 := by
    simpa [prefixWord, tailWord_2799204, baseEnd_2799204] using wordTrace_append hprefix tailTrace_2799204
  have hstable : (prefixWord ++ tailWord_2799204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2799204).length < 2 ^ (prefixWord ++ tailWord_2799204).sum := by decide
  have hdescent : baseEnd_2799204 < baseStart_2799204 := by decide
  rcases family_descends (prefixWord ++ tailWord_2799204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2799208 : List Nat := [2, 1, 4, 3, 1, 1, 3, 1, 1, 4, 2]
def baseStart_2799208 : Nat := 118140960795 + 2799208 * 2 ^ 59
def prefixEnd_2799208 : Nat := 4983230072969 + 3 ^ 40 * 2799208 * 2
def baseEnd_2799208 : Nat := 1437339155910789319526683

theorem tailTrace_2799208 : CollatzResearch.WordTrace tailWord_2799208 prefixEnd_2799208 1437339155910789319526683 := by
  unfold tailWord_2799208
  simp only [CollatzResearch.WordTrace]
  refine ⟨51047751621477478755339139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68063668828636638340452185 51047751621477478755339139)
  ·
    refine ⟨76571627432216218133008709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51047751621477478755339139 76571627432216218133008709)
    ·
      refine ⟨14357180143540540899939133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 76571627432216218133008709 14357180143540540899939133)
      ·
        refine ⟨5383942553827702837477175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14357180143540540899939133 5383942553827702837477175)
        ·
          refine ⟨8075913830741554256215763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5383942553827702837477175 8075913830741554256215763)
          ·
            refine ⟨12113870746112331384323645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8075913830741554256215763 12113870746112331384323645)
            ·
              refine ⟨4542701529792124269121367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12113870746112331384323645 4542701529792124269121367)
              ·
                refine ⟨6814052294688186403682051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4542701529792124269121367 6814052294688186403682051)
                ·
                  refine ⟨10221078442032279605523077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6814052294688186403682051 10221078442032279605523077)
                  ·
                    refine ⟨1916452207881052426035577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10221078442032279605523077 1916452207881052426035577)
                    ·
                      refine ⟨1437339155910789319526683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1916452207881052426035577 1437339155910789319526683)
                      ·
                        rfl

theorem cell23_2799208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 3, 1, 1, 4, 2].length) (baseStart_2799208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2799208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2799208 prefixEnd_2799208 := by exact prefixLift 2799208
  have htrace : WordTrace (prefixWord ++ tailWord_2799208) baseStart_2799208 baseEnd_2799208 := by
    simpa [prefixWord, tailWord_2799208, baseEnd_2799208] using wordTrace_append hprefix tailTrace_2799208
  have hstable : (prefixWord ++ tailWord_2799208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2799208).length < 2 ^ (prefixWord ++ tailWord_2799208).sum := by decide
  have hdescent : baseEnd_2799208 < baseStart_2799208 := by decide
  rcases family_descends (prefixWord ++ tailWord_2799208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2799227 : List Nat := [1, 1, 1, 1, 1, 4, 3, 3, 1, 7]
def baseStart_2799227 : Nat := 118140960795 + 2799227 * 2 ^ 59
def prefixEnd_2799227 : Nat := 4983230072969 + 3 ^ 40 * 2799227 * 2
def baseEnd_2799227 : Nat := 479116304014408248396365

theorem tailTrace_2799227 : CollatzResearch.WordTrace tailWord_2799227 prefixEnd_2799227 479116304014408248396365 := by
  unfold tailWord_2799227
  simp only [CollatzResearch.WordTrace]
  refine ⟨102096196229886123755619935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68064130819924082503746623 102096196229886123755619935)
  ·
    refine ⟨153144294344829185633429903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102096196229886123755619935 153144294344829185633429903)
    ·
      refine ⟨229716441517243778450144855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 153144294344829185633429903 229716441517243778450144855)
      ·
        refine ⟨344574662275865667675217283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 229716441517243778450144855 344574662275865667675217283)
        ·
          refine ⟨516861993413798501512825925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 344574662275865667675217283 516861993413798501512825925)
          ·
            refine ⟨96911623765087219033654861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 516861993413798501512825925 96911623765087219033654861)
            ·
              refine ⟨36341858911907707137620573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 96911623765087219033654861 36341858911907707137620573)
              ·
                refine ⟨13628197091965390176607715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36341858911907707137620573 13628197091965390176607715)
                ·
                  refine ⟨20442295637948085264911573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13628197091965390176607715 20442295637948085264911573)
                  ·
                    refine ⟨479116304014408248396365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 20442295637948085264911573 479116304014408248396365)
                    ·
                      rfl

theorem cell23_2799227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 3, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 3, 3, 1, 7].length) (baseStart_2799227 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2799227 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2799227 prefixEnd_2799227 := by exact prefixLift 2799227
  have htrace : WordTrace (prefixWord ++ tailWord_2799227) baseStart_2799227 baseEnd_2799227 := by
    simpa [prefixWord, tailWord_2799227, baseEnd_2799227] using wordTrace_append hprefix tailTrace_2799227
  have hstable : (prefixWord ++ tailWord_2799227).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2799227).length < 2 ^ (prefixWord ++ tailWord_2799227).sum := by decide
  have hdescent : baseEnd_2799227 < baseStart_2799227 := by decide
  rcases family_descends (prefixWord ++ tailWord_2799227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2799244 : List Nat := [2, 2, 1, 2, 1, 1, 5, 2, 2, 5]
def baseStart_2799244 : Nat := 118140960795 + 2799244 * 2 ^ 59
def prefixEnd_2799244 : Nat := 4983230072969 + 3 ^ 40 * 2799244 * 2
def baseEnd_2799244 : Nat := 479119213738117059558839

theorem tailTrace_2799244 : CollatzResearch.WordTrace tailWord_2799244 prefixEnd_2799244 479119213738117059558839 := by
  unfold tailWord_2799244
  simp only [CollatzResearch.WordTrace]
  refine ⟨51048408135412267829494393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68064544180549690439325857 51048408135412267829494393)
  ·
    refine ⟨38286306101559200872120795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51048408135412267829494393 38286306101559200872120795)
    ·
      refine ⟨57429459152338801308181193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38286306101559200872120795 57429459152338801308181193)
      ·
        refine ⟨43072094364254100981135895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57429459152338801308181193 43072094364254100981135895)
        ·
          refine ⟨64608141546381151471703843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43072094364254100981135895 64608141546381151471703843)
          ·
            refine ⟨96912212319571727207555765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64608141546381151471703843 96912212319571727207555765)
            ·
              refine ⟨9085519904959849425708353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 96912212319571727207555765 9085519904959849425708353)
              ·
                refine ⟨6814139928719887069281265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9085519904959849425708353 6814139928719887069281265)
                ·
                  refine ⟨5110604946539915301960949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6814139928719887069281265 5110604946539915301960949)
                  ·
                    refine ⟨479119213738117059558839, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5110604946539915301960949 479119213738117059558839)
                    ·
                      rfl

theorem cell23_2799244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 5, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 5, 2, 2, 5].length) (baseStart_2799244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2799244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2799244 prefixEnd_2799244 := by exact prefixLift 2799244
  have htrace : WordTrace (prefixWord ++ tailWord_2799244) baseStart_2799244 baseEnd_2799244 := by
    simpa [prefixWord, tailWord_2799244, baseEnd_2799244] using wordTrace_append hprefix tailTrace_2799244
  have hstable : (prefixWord ++ tailWord_2799244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2799244).length < 2 ^ (prefixWord ++ tailWord_2799244).sum := by decide
  have hdescent : baseEnd_2799244 < baseStart_2799244 := by decide
  rcases family_descends (prefixWord ++ tailWord_2799244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2799257 : List Nat := [1, 2, 1, 2, 1, 2, 2, 2, 2, 8]
def baseStart_2799257 : Nat := 118140960795 + 2799257 * 2 ^ 59
def prefixEnd_2799257 : Nat := 4983230072969 + 3 ^ 40 * 2799257 * 2
def baseEnd_2799257 : Nat := 479121438820953209271319

theorem tailTrace_2799257 : CollatzResearch.WordTrace tailWord_2799257 prefixEnd_2799257 479121438820953209271319 := by
  unfold tailWord_2799257
  simp only [CollatzResearch.WordTrace]
  refine ⟨102097290419777438879212025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68064860279851625919474683 102097290419777438879212025)
  ·
    refine ⟨76572967814833079159409019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102097290419777438879212025 76572967814833079159409019)
    ·
      refine ⟨114859451722249618739113529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76572967814833079159409019 114859451722249618739113529)
      ·
        refine ⟨86144588791687214054335147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 114859451722249618739113529 86144588791687214054335147)
        ·
          refine ⟨129216883187530821081502721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86144588791687214054335147 129216883187530821081502721)
          ·
            refine ⟨96912662390648115811127041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 129216883187530821081502721 96912662390648115811127041)
            ·
              refine ⟨72684496792986086858345281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 96912662390648115811127041 72684496792986086858345281)
              ·
                refine ⟨54513372594739565143758961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 72684496792986086858345281 54513372594739565143758961)
                ·
                  refine ⟨40885029446054673857819221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 54513372594739565143758961 40885029446054673857819221)
                  ·
                    refine ⟨479121438820953209271319, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 40885029446054673857819221 479121438820953209271319)
                    ·
                      rfl

theorem cell23_2799257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 2, 2, 8].length) (baseStart_2799257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2799257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2799257 prefixEnd_2799257 := by exact prefixLift 2799257
  have htrace : WordTrace (prefixWord ++ tailWord_2799257) baseStart_2799257 baseEnd_2799257 := by
    simpa [prefixWord, tailWord_2799257, baseEnd_2799257] using wordTrace_append hprefix tailTrace_2799257
  have hstable : (prefixWord ++ tailWord_2799257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2799257).length < 2 ^ (prefixWord ++ tailWord_2799257).sum := by decide
  have hdescent : baseEnd_2799257 < baseStart_2799257 := by decide
  rcases family_descends (prefixWord ++ tailWord_2799257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2799325 : List Nat := [1, 4, 3, 3, 1, 1, 1, 2, 3, 4]
def baseStart_2799325 : Nat := 118140960795 + 2799325 * 2 ^ 59
def prefixEnd_2799325 : Nat := 4983230072969 + 3 ^ 40 * 2799325 * 2
def baseEnd_2799325 : Nat := 479133077715788453921215

theorem tailTrace_2799325 : CollatzResearch.WordTrace tailWord_2799325 prefixEnd_2799325 479133077715788453921215 := by
  unfold tailWord_2799325
  simp only [CollatzResearch.WordTrace]
  refine ⟨102099770583531086492687429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68066513722354057661791619 102099770583531086492687429)
  ·
    refine ⟨19143706984412078717378893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 102099770583531086492687429 19143706984412078717378893)
    ·
      refine ⟨7178890119154529519017085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19143706984412078717378893 7178890119154529519017085)
      ·
        refine ⟨2692083794682948569631407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7178890119154529519017085 2692083794682948569631407)
        ·
          refine ⟨4038125692024422854447111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2692083794682948569631407 4038125692024422854447111)
          ·
            refine ⟨6057188538036634281670667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4038125692024422854447111 6057188538036634281670667)
            ·
              refine ⟨9085782807054951422506001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6057188538036634281670667 9085782807054951422506001)
              ·
                refine ⟨6814337105291213566879501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9085782807054951422506001 6814337105291213566879501)
                ·
                  refine ⟨2555376414484205087579813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6814337105291213566879501 2555376414484205087579813)
                  ·
                    refine ⟨479133077715788453921215, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2555376414484205087579813 479133077715788453921215)
                    ·
                      rfl

theorem cell23_2799325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 1, 1, 2, 3, 4].length) (baseStart_2799325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2799325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2799325 prefixEnd_2799325 := by exact prefixLift 2799325
  have htrace : WordTrace (prefixWord ++ tailWord_2799325) baseStart_2799325 baseEnd_2799325 := by
    simpa [prefixWord, tailWord_2799325, baseEnd_2799325] using wordTrace_append hprefix tailTrace_2799325
  have hstable : (prefixWord ++ tailWord_2799325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2799325).length < 2 ^ (prefixWord ++ tailWord_2799325).sum := by decide
  have hdescent : baseEnd_2799325 < baseStart_2799325 := by decide
  rcases family_descends (prefixWord ++ tailWord_2799325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2799381 : List Nat := [1, 3, 2, 1, 2, 3, 3, 1, 1, 6]
def baseStart_2799381 : Nat := 118140960795 + 2799381 * 2 ^ 59
def prefixEnd_2799381 : Nat := 4983230072969 + 3 ^ 40 * 2799381 * 2
def baseEnd_2799381 : Nat := 479142662688005714221129

theorem tailTrace_2799381 : CollatzResearch.WordTrace tailWord_2799381 prefixEnd_2799381 479142662688005714221129 := by
  unfold tailWord_2799381
  simp only [CollatzResearch.WordTrace]
  refine ⟨102101813071328208056725997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68067875380885472037817331 102101813071328208056725997)
  ·
    refine ⟨38288179901748078021272249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 102101813071328208056725997 38288179901748078021272249)
    ·
      refine ⟨28716134926311058515954187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38288179901748078021272249 28716134926311058515954187)
      ·
        refine ⟨43074202389466587773931281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28716134926311058515954187 43074202389466587773931281)
        ·
          refine ⟨32305651792099940830448461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43074202389466587773931281 32305651792099940830448461)
          ·
            refine ⟨12114619422037477811418173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32305651792099940830448461 12114619422037477811418173)
            ·
              refine ⟨4542982283264054179281815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12114619422037477811418173 4542982283264054179281815)
              ·
                refine ⟨6814473424896081268922723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4542982283264054179281815 6814473424896081268922723)
                ·
                  refine ⟨10221710137344121903384085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6814473424896081268922723 10221710137344121903384085)
                  ·
                    refine ⟨479142662688005714221129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10221710137344121903384085 479142662688005714221129)
                    ·
                      rfl

theorem cell23_2799381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 3, 1, 1, 6].length) (baseStart_2799381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2799381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2799381 prefixEnd_2799381 := by exact prefixLift 2799381
  have htrace : WordTrace (prefixWord ++ tailWord_2799381) baseStart_2799381 baseEnd_2799381 := by
    simpa [prefixWord, tailWord_2799381, baseEnd_2799381] using wordTrace_append hprefix tailTrace_2799381
  have hstable : (prefixWord ++ tailWord_2799381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2799381).length < 2 ^ (prefixWord ++ tailWord_2799381).sum := by decide
  have hdescent : baseEnd_2799381 < baseStart_2799381 := by decide
  rcases family_descends (prefixWord ++ tailWord_2799381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2799388 : List Nat := [2, 2, 3, 1, 1, 2, 4, 2, 1, 1, 4]
def baseStart_2799388 : Nat := 118140960795 + 2799388 * 2 ^ 59
def prefixEnd_2799388 : Nat := 4983230072969 + 3 ^ 40 * 2799388 * 2
def baseEnd_2799388 : Nat := 1437431582428598615275855

theorem tailTrace_2799388 : CollatzResearch.WordTrace tailWord_2799388 prefixEnd_2799388 1437431582428598615275855 := by
  unfold tailWord_2799388
  simp only [CollatzResearch.WordTrace]
  refine ⟨51051034191151424126115409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68068045588201898834820545 51051034191151424126115409)
  ·
    refine ⟨38288275643363568094586557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51051034191151424126115409 38288275643363568094586557)
    ·
      refine ⟨14358103366261338035469959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38288275643363568094586557 14358103366261338035469959)
      ·
        refine ⟨21537155049392007053204939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14358103366261338035469959 21537155049392007053204939)
        ·
          refine ⟨32305732574088010579807409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21537155049392007053204939 32305732574088010579807409)
          ·
            refine ⟨24229299430566007934855557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32305732574088010579807409 24229299430566007934855557)
            ·
              refine ⟨4542993643231126487785417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24229299430566007934855557 4542993643231126487785417)
              ·
                refine ⟨3407245232423344865839063, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4542993643231126487785417 3407245232423344865839063)
                ·
                  refine ⟨5110867848635017298758595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3407245232423344865839063 5110867848635017298758595)
                  ·
                    refine ⟨7666301772952525948137893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5110867848635017298758595 7666301772952525948137893)
                    ·
                      refine ⟨1437431582428598615275855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7666301772952525948137893 1437431582428598615275855)
                      ·
                        rfl

theorem cell23_2799388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 4, 2, 1, 1, 4].length) (baseStart_2799388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2799388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2799388 prefixEnd_2799388 := by exact prefixLift 2799388
  have htrace : WordTrace (prefixWord ++ tailWord_2799388) baseStart_2799388 baseEnd_2799388 := by
    simpa [prefixWord, tailWord_2799388, baseEnd_2799388] using wordTrace_append hprefix tailTrace_2799388
  have hstable : (prefixWord ++ tailWord_2799388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2799388).length < 2 ^ (prefixWord ++ tailWord_2799388).sum := by decide
  have hdescent : baseEnd_2799388 < baseStart_2799388 := by decide
  rcases family_descends (prefixWord ++ tailWord_2799388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2799411 : List Nat := [1, 1, 1, 2, 7, 2, 9]
def baseStart_2799411 : Nat := 118140960795 + 2799411 * 2 ^ 59
def prefixEnd_2799411 : Nat := 4983230072969 + 3 ^ 40 * 2799411 * 2
def baseEnd_2799411 : Nat := 17746214722020395373929

theorem tailTrace_2799411 : CollatzResearch.WordTrace tailWord_2799411 prefixEnd_2799411 17746214722020395373929 := by
  unfold tailWord_2799411
  simp only [CollatzResearch.WordTrace]
  refine ⟨102102907261219523180318087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68068604840813015453545391 102102907261219523180318087)
  ·
    refine ⟨153154360891829284770477131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102102907261219523180318087 153154360891829284770477131)
    ·
      refine ⟨229731541337743927155715697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 153154360891829284770477131 229731541337743927155715697)
      ·
        refine ⟨172298656003307945366786773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 229731541337743927155715697 172298656003307945366786773)
        ·
          refine ⟨4038249750077529969534065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 172298656003307945366786773 4038249750077529969534065)
          ·
            refine ⟨3028687312558147477150549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4038249750077529969534065 3028687312558147477150549)
            ·
              refine ⟨17746214722020395373929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 3028687312558147477150549 17746214722020395373929)
              ·
                rfl

theorem cell23_2799411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 2, 9].length) (baseStart_2799411 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2799411 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2799411 prefixEnd_2799411 := by exact prefixLift 2799411
  have htrace : WordTrace (prefixWord ++ tailWord_2799411) baseStart_2799411 baseEnd_2799411 := by
    simpa [prefixWord, tailWord_2799411, baseEnd_2799411] using wordTrace_append hprefix tailTrace_2799411
  have hstable : (prefixWord ++ tailWord_2799411).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2799411).length < 2 ^ (prefixWord ++ tailWord_2799411).sum := by decide
  have hdescent : baseEnd_2799411 < baseStart_2799411 := by decide
  rcases family_descends (prefixWord ++ tailWord_2799411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2799422 : List Nat := [4, 2, 1, 2, 2, 1, 3, 1, 3, 2, 2]
def baseStart_2799422 : Nat := 118140960795 + 2799422 * 2 ^ 59
def prefixEnd_2799422 : Nat := 4983230072969 + 3 ^ 40 * 2799422 * 2
def baseEnd_2799422 : Nat := 1437449040770851482250699

theorem tailTrace_2799422 : CollatzResearch.WordTrace tailWord_2799422 prefixEnd_2799422 1437449040770851482250699 := by
  unfold tailWord_2799422
  simp only [CollatzResearch.WordTrace]
  refine ⟨12762913558022459007371065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 68068872309453114705979013 12762913558022459007371065)
  ·
    refine ⟨9572185168516844255528299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12762913558022459007371065 9572185168516844255528299)
    ·
      refine ⟨14358277752775266383292449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9572185168516844255528299 14358277752775266383292449)
      ·
        refine ⟨10768708314581449787469337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14358277752775266383292449 10768708314581449787469337)
        ·
          refine ⟨8076531235936087340602003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10768708314581449787469337 8076531235936087340602003)
          ·
            refine ⟨12114796853904131010903005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8076531235936087340602003 12114796853904131010903005)
            ·
              refine ⟨4543048820214049129088627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12114796853904131010903005 4543048820214049129088627)
              ·
                refine ⟨6814573230321073693632941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4543048820214049129088627 6814573230321073693632941)
                ·
                  refine ⟨2555464961370402635112353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6814573230321073693632941 2555464961370402635112353)
                  ·
                    refine ⟨1916598721027801976334265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2555464961370402635112353 1916598721027801976334265)
                    ·
                      refine ⟨1437449040770851482250699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1916598721027801976334265 1437449040770851482250699)
                      ·
                        rfl

theorem cell23_2799422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 3, 1, 3, 2, 2].length) (baseStart_2799422 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2799422 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2799422 prefixEnd_2799422 := by exact prefixLift 2799422
  have htrace : WordTrace (prefixWord ++ tailWord_2799422) baseStart_2799422 baseEnd_2799422 := by
    simpa [prefixWord, tailWord_2799422, baseEnd_2799422] using wordTrace_append hprefix tailTrace_2799422
  have hstable : (prefixWord ++ tailWord_2799422).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2799422).length < 2 ^ (prefixWord ++ tailWord_2799422).sum := by decide
  have hdescent : baseEnd_2799422 < baseStart_2799422 := by decide
  rcases family_descends (prefixWord ++ tailWord_2799422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2799481 : List Nat := [1, 2, 1, 3, 2, 2, 1, 1, 1, 6, 3]
def baseStart_2799481 : Nat := 118140960795 + 2799481 * 2 ^ 59
def prefixEnd_2799481 : Nat := 4983230072969 + 3 ^ 40 * 2799481 * 2
def baseEnd_2799481 : Nat := 1437479336129466751412927

theorem tailTrace_2799481 : CollatzResearch.WordTrace tailWord_2799481 prefixEnd_2799481 1437479336129466751412927 := by
  unfold tailWord_2799481
  simp only [CollatzResearch.WordTrace]
  refine ⟨102105460370965925135366297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68070306913977283423577531 102105460370965925135366297)
  ·
    refine ⟨76579095278224443851524723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102105460370965925135366297 76579095278224443851524723)
    ·
      refine ⟨114868642917336665777287085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76579095278224443851524723 114868642917336665777287085)
      ·
        refine ⟨43075741094001249666482657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 114868642917336665777287085 43075741094001249666482657)
        ·
          refine ⟨32306805820500937249861993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43075741094001249666482657 32306805820500937249861993)
          ·
            refine ⟨24230104365375702937396495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32306805820500937249861993 24230104365375702937396495)
            ·
              refine ⟨36345156548063554406094743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24230104365375702937396495 36345156548063554406094743)
              ·
                refine ⟨54517734822095331609142115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36345156548063554406094743 54517734822095331609142115)
                ·
                  refine ⟨81776602233142997413713173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 54517734822095331609142115 81776602233142997413713173)
                  ·
                    refine ⟨3833278229678578003767805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 81776602233142997413713173 3833278229678578003767805)
                    ·
                      refine ⟨1437479336129466751412927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3833278229678578003767805 1437479336129466751412927)
                      ·
                        rfl

theorem cell23_2799481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 1, 1, 1, 6, 3].length) (baseStart_2799481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2799481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2799481 prefixEnd_2799481 := by exact prefixLift 2799481
  have htrace : WordTrace (prefixWord ++ tailWord_2799481) baseStart_2799481 baseEnd_2799481 := by
    simpa [prefixWord, tailWord_2799481, baseEnd_2799481] using wordTrace_append hprefix tailTrace_2799481
  have hstable : (prefixWord ++ tailWord_2799481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2799481).length < 2 ^ (prefixWord ++ tailWord_2799481).sum := by decide
  have hdescent : baseEnd_2799481 < baseStart_2799481 := by decide
  rcases family_descends (prefixWord ++ tailWord_2799481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2799491 : List Nat := [1, 1, 1, 3, 4, 2, 1, 1, 1, 4, 4]
def baseStart_2799491 : Nat := 118140960795 + 2799491 * 2 ^ 59
def prefixEnd_2799491 : Nat := 4983230072969 + 3 ^ 40 * 2799491 * 2
def baseEnd_2799491 : Nat := 1437484470936011712287881

theorem tailTrace_2799491 : CollatzResearch.WordTrace tailWord_2799491 prefixEnd_2799491 1437484470936011712287881 := by
  unfold tailWord_2799491
  simp only [CollatzResearch.WordTrace]
  refine ⟨102105825100929696843230327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68070550067286464562153551 102105825100929696843230327)
  ·
    refine ⟨153158737651394545264845491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102105825100929696843230327 153158737651394545264845491)
    ·
      refine ⟨229738106477091817897268237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 153158737651394545264845491 229738106477091817897268237)
      ·
        refine ⟨86151789928909431711475589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 229738106477091817897268237 86151789928909431711475589)
        ·
          refine ⟨16153460611670518445901673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 86151789928909431711475589 16153460611670518445901673)
          ·
            refine ⟨12115095458752888834426255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16153460611670518445901673 12115095458752888834426255)
            ·
              refine ⟨18172643188129333251639383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12115095458752888834426255 18172643188129333251639383)
              ·
                refine ⟨27258964782193999877459075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18172643188129333251639383 27258964782193999877459075)
                ·
                  refine ⟨40888447173290999816188613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27258964782193999877459075 40888447173290999816188613)
                  ·
                    refine ⟨7666583844992062465535365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 40888447173290999816188613 7666583844992062465535365)
                    ·
                      refine ⟨1437484470936011712287881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7666583844992062465535365 1437484470936011712287881)
                      ·
                        rfl

theorem cell23_2799491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 1, 1, 1, 4, 4].length) (baseStart_2799491 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2799491 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2799491 prefixEnd_2799491 := by exact prefixLift 2799491
  have htrace : WordTrace (prefixWord ++ tailWord_2799491) baseStart_2799491 baseEnd_2799491 := by
    simpa [prefixWord, tailWord_2799491, baseEnd_2799491] using wordTrace_append hprefix tailTrace_2799491
  have hstable : (prefixWord ++ tailWord_2799491).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2799491).length < 2 ^ (prefixWord ++ tailWord_2799491).sum := by decide
  have hdescent : baseEnd_2799491 < baseStart_2799491 := by decide
  rcases family_descends (prefixWord ++ tailWord_2799491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2799538 : List Nat := [3, 2, 1, 1, 1, 1, 1, 3, 1, 7, 2]
def baseStart_2799538 : Nat := 118140960795 + 2799538 * 2 ^ 59
def prefixEnd_2799538 : Nat := 4983230072969 + 3 ^ 40 * 2799538 * 2
def baseEnd_2799538 : Nat := 1437508604526773028400165

theorem tailTrace_2799538 : CollatzResearch.WordTrace tailWord_2799538 prefixEnd_2799538 1437508604526773028400165 := by
  unfold tailWord_2799538
  simp only [CollatzResearch.WordTrace]
  refine ⟨25526884832939855967547817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68071692887839615913460845 25526884832939855967547817)
  ·
    refine ⟨19145163624704891975660863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25526884832939855967547817 19145163624704891975660863)
    ·
      refine ⟨28717745437057337963491295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19145163624704891975660863 28717745437057337963491295)
      ·
        refine ⟨43076618155586006945236943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28717745437057337963491295 43076618155586006945236943)
        ·
          refine ⟨64614927233379010417855415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43076618155586006945236943 64614927233379010417855415)
          ·
            refine ⟨96922390850068515626783123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64614927233379010417855415 96922390850068515626783123)
            ·
              refine ⟨145383586275102773440174685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 96922390850068515626783123 145383586275102773440174685)
              ·
                refine ⟨54518844853163540040065507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 145383586275102773440174685 54518844853163540040065507)
                ·
                  refine ⟨81778267279745310060098261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 54518844853163540040065507 81778267279745310060098261)
                  ·
                    refine ⟨1916678139369030704533553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 81778267279745310060098261 1916678139369030704533553)
                    ·
                      refine ⟨1437508604526773028400165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1916678139369030704533553 1437508604526773028400165)
                      ·
                        rfl

theorem cell23_2799538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 3, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 3, 1, 7, 2].length) (baseStart_2799538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2799538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2799538 prefixEnd_2799538 := by exact prefixLift 2799538
  have htrace : WordTrace (prefixWord ++ tailWord_2799538) baseStart_2799538 baseEnd_2799538 := by
    simpa [prefixWord, tailWord_2799538, baseEnd_2799538] using wordTrace_append hprefix tailTrace_2799538
  have hstable : (prefixWord ++ tailWord_2799538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2799538).length < 2 ^ (prefixWord ++ tailWord_2799538).sum := by decide
  have hdescent : baseEnd_2799538 < baseStart_2799538 := by decide
  rcases family_descends (prefixWord ++ tailWord_2799538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2799551 : List Nat := [1, 1, 2, 2, 2, 1, 3, 1, 3, 3, 4]
def baseStart_2799551 : Nat := 118140960795 + 2799551 * 2 ^ 59
def prefixEnd_2799551 : Nat := 4983230072969 + 3 ^ 40 * 2799551 * 2
def baseEnd_2799551 : Nat := 1437515279775281477537605

theorem tailTrace_2799551 : CollatzResearch.WordTrace tailWord_2799551 prefixEnd_2799551 1437515279775281477537605 := by
  unfold tailWord_2799551
  simp only [CollatzResearch.WordTrace]
  refine ⟨102108013480712327090414507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68072008987141551393609671 102108013480712327090414507)
  ·
    refine ⟨153162020221068490635621761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102108013480712327090414507 153162020221068490635621761)
    ·
      refine ⟨114871515165801367976716321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 153162020221068490635621761 114871515165801367976716321)
      ·
        refine ⟨86153636374351025982537241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 114871515165801367976716321 86153636374351025982537241)
        ·
          refine ⟨64615227280763269486902931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 86153636374351025982537241 64615227280763269486902931)
          ·
            refine ⟨96922840921144904230354397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64615227280763269486902931 96922840921144904230354397)
            ·
              refine ⟨36346065345429339086382899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 96922840921144904230354397 36346065345429339086382899)
              ·
                refine ⟨54519098018144008629574349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36346065345429339086382899 54519098018144008629574349)
                ·
                  refine ⟨20444661756804003236090381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 54519098018144008629574349 20444661756804003236090381)
                  ·
                    refine ⟨7666748158801501213533893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20444661756804003236090381 7666748158801501213533893)
                    ·
                      refine ⟨1437515279775281477537605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7666748158801501213533893 1437515279775281477537605)
                      ·
                        rfl

theorem cell23_2799551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 3, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 3, 1, 3, 3, 4].length) (baseStart_2799551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2799551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2799551 prefixEnd_2799551 := by exact prefixLift 2799551
  have htrace : WordTrace (prefixWord ++ tailWord_2799551) baseStart_2799551 baseEnd_2799551 := by
    simpa [prefixWord, tailWord_2799551, baseEnd_2799551] using wordTrace_append hprefix tailTrace_2799551
  have hstable : (prefixWord ++ tailWord_2799551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2799551).length < 2 ^ (prefixWord ++ tailWord_2799551).sum := by decide
  have hdescent : baseEnd_2799551 < baseStart_2799551 := by decide
  rcases family_descends (prefixWord ++ tailWord_2799551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2799568 : List Nat := [2, 1, 1, 1, 1, 2, 4, 2, 1, 6, 2]
def baseStart_2799568 : Nat := 118140960795 + 2799568 * 2 ^ 59
def prefixEnd_2799568 : Nat := 4983230072969 + 3 ^ 40 * 2799568 * 2
def baseEnd_2799568 : Nat := 1437524008946407911025027

theorem tailTrace_2799568 : CollatzResearch.WordTrace tailWord_2799568 prefixEnd_2799568 1437524008946407911025027 := by
  unfold tailWord_2799568
  simp only [CollatzResearch.WordTrace]
  refine ⟨51054316760825369496891679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68072422347767159329188905 51054316760825369496891679)
  ·
    refine ⟨76581475141238054245337519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51054316760825369496891679 76581475141238054245337519)
    ·
      refine ⟨114872212711857081368006279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76581475141238054245337519 114872212711857081368006279)
      ·
        refine ⟨172308319067785622052009419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114872212711857081368006279 172308319067785622052009419)
        ·
          refine ⟨258462478601678433078014129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 172308319067785622052009419 258462478601678433078014129)
          ·
            refine ⟨193846858951258824808510597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 258462478601678433078014129 193846858951258824808510597)
            ·
              refine ⟨36346286053361029651595737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 193846858951258824808510597 36346286053361029651595737)
              ·
                refine ⟨27259714540020772238696803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36346286053361029651595737 27259714540020772238696803)
                ·
                  refine ⟨40889571810031158358045205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27259714540020772238696803 40889571810031158358045205)
                  ·
                    refine ⟨1916698678595210548033369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 40889571810031158358045205 1916698678595210548033369)
                    ·
                      refine ⟨1437524008946407911025027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1916698678595210548033369 1437524008946407911025027)
                      ·
                        rfl

theorem cell23_2799568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 4, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 4, 2, 1, 6, 2].length) (baseStart_2799568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2799568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2799568 prefixEnd_2799568 := by exact prefixLift 2799568
  have htrace : WordTrace (prefixWord ++ tailWord_2799568) baseStart_2799568 baseEnd_2799568 := by
    simpa [prefixWord, tailWord_2799568, baseEnd_2799568] using wordTrace_append hprefix tailTrace_2799568
  have hstable : (prefixWord ++ tailWord_2799568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2799568).length < 2 ^ (prefixWord ++ tailWord_2799568).sum := by decide
  have hdescent : baseEnd_2799568 < baseStart_2799568 := by decide
  rcases family_descends (prefixWord ++ tailWord_2799568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2799595 : List Nat := [1, 1, 1, 1, 2, 3, 1, 8, 1, 4]
def baseStart_2799595 : Nat := 118140960795 + 2799595 * 2 ^ 59
def prefixEnd_2799595 : Nat := 4983230072969 + 3 ^ 40 * 2799595 * 2
def baseEnd_2799595 : Nat := 479179290974693101795801

theorem tailTrace_2799595 : CollatzResearch.WordTrace tailWord_2799595 prefixEnd_2799595 479179290974693101795801 := by
  unfold tailWord_2799595
  simp only [CollatzResearch.WordTrace]
  refine ⟨102109618292552922605016239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68073078861701948403344159 102109618292552922605016239)
  ·
    refine ⟨153164427438829383907524359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102109618292552922605016239 153164427438829383907524359)
    ·
      refine ⟨229746641158244075861286539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 153164427438829383907524359 229746641158244075861286539)
      ·
        refine ⟨344619961737366113791929809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 229746641158244075861286539 344619961737366113791929809)
        ·
          refine ⟨258464971303024585343947357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 344619961737366113791929809 258464971303024585343947357)
          ·
            refine ⟨96924364238634219503980259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 258464971303024585343947357 96924364238634219503980259)
            ·
              refine ⟨145386546357951329255970389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 96924364238634219503980259 145386546357951329255970389)
              ·
                refine ⟨1703748590132242139718403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 145386546357951329255970389 1703748590132242139718403)
                ·
                  refine ⟨2555622885198363209577605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1703748590132242139718403 2555622885198363209577605)
                  ·
                    refine ⟨479179290974693101795801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2555622885198363209577605 479179290974693101795801)
                    ·
                      rfl

theorem cell23_2799595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 8, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 8, 1, 4].length) (baseStart_2799595 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2799595 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2799595 prefixEnd_2799595 := by exact prefixLift 2799595
  have htrace : WordTrace (prefixWord ++ tailWord_2799595) baseStart_2799595 baseEnd_2799595 := by
    simpa [prefixWord, tailWord_2799595, baseEnd_2799595] using wordTrace_append hprefix tailTrace_2799595
  have hstable : (prefixWord ++ tailWord_2799595).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2799595).length < 2 ^ (prefixWord ++ tailWord_2799595).sum := by decide
  have hdescent : baseEnd_2799595 < baseStart_2799595 := by decide
  rcases family_descends (prefixWord ++ tailWord_2799595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2799611 : List Nat := [1, 1, 1, 1, 1, 3, 4, 2, 1, 2, 6]
def baseStart_2799611 : Nat := 118140960795 + 2799611 * 2 ^ 59
def prefixEnd_2799611 : Nat := 4983230072969 + 3 ^ 40 * 2799611 * 2
def baseEnd_2799611 : Nat := 1437546088614551242787329

theorem tailTrace_2799611 : CollatzResearch.WordTrace tailWord_2799611 prefixEnd_2799611 1437546088614551242787329 := by
  unfold tailWord_2799611
  simp only [CollatzResearch.WordTrace]
  refine ⟨102110201860494957337598687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68073467906996638225065791 102110201860494957337598687)
  ·
    refine ⟨153165302790742436006398031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102110201860494957337598687 153165302790742436006398031)
    ·
      refine ⟨229747954186113654009597047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 153165302790742436006398031 229747954186113654009597047)
      ·
        refine ⟨344621931279170481014395571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 229747954186113654009597047 344621931279170481014395571)
        ·
          refine ⟨516932896918755721521593357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 344621931279170481014395571 516932896918755721521593357)
          ·
            refine ⟨193849836344533395570597509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 516932896918755721521593357 193849836344533395570597509)
            ·
              refine ⟨36346844314600011669487033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 193849836344533395570597509 36346844314600011669487033)
              ·
                refine ⟨27260133235950008752115275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36346844314600011669487033 27260133235950008752115275)
                ·
                  refine ⟨40890199853925013128172913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27260133235950008752115275 40890199853925013128172913)
                  ·
                    refine ⟨30667649890443759846129685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 40890199853925013128172913 30667649890443759846129685)
                    ·
                      refine ⟨1437546088614551242787329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 30667649890443759846129685 1437546088614551242787329)
                      ·
                        rfl

theorem cell23_2799611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 4, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 4, 2, 1, 2, 6].length) (baseStart_2799611 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2799611 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2799611 prefixEnd_2799611 := by exact prefixLift 2799611
  have htrace : WordTrace (prefixWord ++ tailWord_2799611) baseStart_2799611 baseEnd_2799611 := by
    simpa [prefixWord, tailWord_2799611, baseEnd_2799611] using wordTrace_append hprefix tailTrace_2799611
  have hstable : (prefixWord ++ tailWord_2799611).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2799611).length < 2 ^ (prefixWord ++ tailWord_2799611).sum := by decide
  have hdescent : baseEnd_2799611 < baseStart_2799611 := by decide
  rcases family_descends (prefixWord ++ tailWord_2799611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2799688 : List Nat := [2, 1, 3, 1, 1, 1, 2, 3, 3, 2, 4]
def baseStart_2799688 : Nat := 118140960795 + 2799688 * 2 ^ 59
def prefixEnd_2799688 : Nat := 4983230072969 + 3 ^ 40 * 2799688 * 2
def baseEnd_2799688 : Nat := 1437585626624947441524475

theorem tailTrace_2799688 : CollatzResearch.WordTrace tailWord_2799688 prefixEnd_2799688 1437585626624947441524475 := by
  unfold tailWord_2799688
  simp only [CollatzResearch.WordTrace]
  refine ⟨51056505140607999744075859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68075340187477332992101145 51056505140607999744075859)
  ·
    refine ⟨76584757710911999616113789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51056505140607999744075859 76584757710911999616113789)
    ·
      refine ⟨28719284141591999856042671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 76584757710911999616113789 28719284141591999856042671)
      ·
        refine ⟨43078926212387999784064007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28719284141591999856042671 43078926212387999784064007)
        ·
          refine ⟨64618389318581999676096011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43078926212387999784064007 64618389318581999676096011)
          ·
            refine ⟨96927583977872999514144017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64618389318581999676096011 96927583977872999514144017)
            ·
              refine ⟨72695687983404749635608013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 96927583977872999514144017 72695687983404749635608013)
              ·
                refine ⟨27260882993776781113353005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 72695687983404749635608013 27260882993776781113353005)
                ·
                  refine ⟨10222831122666292917507377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27260882993776781113353005 10222831122666292917507377)
                  ·
                    refine ⟨7667123341999719688130533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10222831122666292917507377 7667123341999719688130533)
                    ·
                      refine ⟨1437585626624947441524475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7667123341999719688130533 1437585626624947441524475)
                      ·
                        rfl

theorem cell23_2799688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 3, 3, 2, 4].length) (baseStart_2799688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2799688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2799688 prefixEnd_2799688 := by exact prefixLift 2799688
  have htrace : WordTrace (prefixWord ++ tailWord_2799688) baseStart_2799688 baseEnd_2799688 := by
    simpa [prefixWord, tailWord_2799688, baseEnd_2799688] using wordTrace_append hprefix tailTrace_2799688
  have hstable : (prefixWord ++ tailWord_2799688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2799688).length < 2 ^ (prefixWord ++ tailWord_2799688).sum := by decide
  have hdescent : baseEnd_2799688 < baseStart_2799688 := by decide
  rcases family_descends (prefixWord ++ tailWord_2799688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2799692 : List Nat := [2, 2, 1, 3, 1, 1, 6, 1, 1, 1, 4]
def baseStart_2799692 : Nat := 118140960795 + 2799692 * 2 ^ 59
def prefixEnd_2799692 : Nat := 4983230072969 + 3 ^ 40 * 2799692 * 2
def baseEnd_2799692 : Nat := 1437587680547565425874457

theorem tailTrace_2799692 : CollatzResearch.WordTrace tailWord_2799692 prefixEnd_2799692 1437587680547565425874457 := by
  unfold tailWord_2799692
  simp only [CollatzResearch.WordTrace]
  refine ⟨51056578086600754085648665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68075437448801005447531553 51056578086600754085648665)
  ·
    refine ⟨38292433564950565564236499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51056578086600754085648665 38292433564950565564236499)
    ·
      refine ⟨57438650347425848346354749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38292433564950565564236499 57438650347425848346354749)
      ·
        refine ⟨21539493880284693129883031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 57438650347425848346354749 21539493880284693129883031)
        ·
          refine ⟨32309240820427039694824547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21539493880284693129883031 32309240820427039694824547)
          ·
            refine ⟨48463861230640559542236821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32309240820427039694824547 48463861230640559542236821)
            ·
              refine ⟨2271743495186276228542351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 48463861230640559542236821 2271743495186276228542351)
              ·
                refine ⟨3407615242779414342813527, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2271743495186276228542351 3407615242779414342813527)
                ·
                  refine ⟨5111422864169121514220291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3407615242779414342813527 5111422864169121514220291)
                  ·
                    refine ⟨7667134296253682271330437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5111422864169121514220291 7667134296253682271330437)
                    ·
                      refine ⟨1437587680547565425874457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7667134296253682271330437 1437587680547565425874457)
                      ·
                        rfl

theorem cell23_2799692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 6, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 6, 1, 1, 1, 4].length) (baseStart_2799692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2799692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2799692 prefixEnd_2799692 := by exact prefixLift 2799692
  have htrace : WordTrace (prefixWord ++ tailWord_2799692) baseStart_2799692 baseEnd_2799692 := by
    simpa [prefixWord, tailWord_2799692, baseEnd_2799692] using wordTrace_append hprefix tailTrace_2799692
  have hstable : (prefixWord ++ tailWord_2799692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2799692).length < 2 ^ (prefixWord ++ tailWord_2799692).sum := by decide
  have hdescent : baseEnd_2799692 < baseStart_2799692 := by decide
  rcases family_descends (prefixWord ++ tailWord_2799692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2799695 : List Nat := [1, 1, 2, 1, 1, 2, 2, 7, 1, 2, 3]
def baseStart_2799695 : Nat := 118140960795 + 2799695 * 2 ^ 59
def prefixEnd_2799695 : Nat := 4983230072969 + 3 ^ 40 * 2799695 * 2
def baseEnd_2799695 : Nat := 1437589220989528914136943

theorem tailTrace_2799695 : CollatzResearch.WordTrace tailWord_2799695 prefixEnd_2799695 1437589220989528914136943 := by
  unfold tailWord_2799695
  simp only [CollatzResearch.WordTrace]
  refine ⟨102113265592190639683656539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68075510394793759789104359 102113265592190639683656539)
  ·
    refine ⟨153169898388285959525484809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102113265592190639683656539 153169898388285959525484809)
    ·
      refine ⟨114877423791214469644113607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 153169898388285959525484809 114877423791214469644113607)
      ·
        refine ⟨172316135686821704466170411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114877423791214469644113607 172316135686821704466170411)
        ·
          refine ⟨258474203530232556699255617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 172316135686821704466170411 258474203530232556699255617)
          ·
            refine ⟨193855652647674417524441713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 258474203530232556699255617 193855652647674417524441713)
            ·
              refine ⟨145391739485755813143331285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 193855652647674417524441713 145391739485755813143331285)
              ·
                refine ⟨3407618894197401870546827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 145391739485755813143331285 3407618894197401870546827)
                ·
                  refine ⟨5111428341296102805820241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3407618894197401870546827 5111428341296102805820241)
                  ·
                    refine ⟨3833571255972077104365181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5111428341296102805820241 3833571255972077104365181)
                    ·
                      refine ⟨1437589220989528914136943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3833571255972077104365181 1437589220989528914136943)
                      ·
                        rfl

theorem cell23_2799695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 7, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 7, 1, 2, 3].length) (baseStart_2799695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2799695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2799695 prefixEnd_2799695 := by exact prefixLift 2799695
  have htrace : WordTrace (prefixWord ++ tailWord_2799695) baseStart_2799695 baseEnd_2799695 := by
    simpa [prefixWord, tailWord_2799695, baseEnd_2799695] using wordTrace_append hprefix tailTrace_2799695
  have hstable : (prefixWord ++ tailWord_2799695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2799695).length < 2 ^ (prefixWord ++ tailWord_2799695).sum := by decide
  have hdescent : baseEnd_2799695 < baseStart_2799695 := by decide
  rcases family_descends (prefixWord ++ tailWord_2799695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2799776 : List Nat := [2, 1, 1, 4, 2, 4, 2, 1, 2, 1, 3]
def baseStart_2799776 : Nat := 118140960795 + 2799776 * 2 ^ 59
def prefixEnd_2799776 : Nat := 4983230072969 + 3 ^ 40 * 2799776 * 2
def baseEnd_2799776 : Nat := 1437630812922543097224071

theorem tailTrace_2799776 : CollatzResearch.WordTrace tailWord_2799776 prefixEnd_2799776 1437630812922543097224071 := by
  unfold tailWord_2799776
  simp only [CollatzResearch.WordTrace]
  refine ⟨51058109952448595258677591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68077479936598127011570121 51058109952448595258677591)
  ·
    refine ⟨76587164928672892888016387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51058109952448595258677591 76587164928672892888016387)
    ·
      refine ⟨114880747393009339332024581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76587164928672892888016387 114880747393009339332024581)
      ·
        refine ⟨21540140136189251124754609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 114880747393009339332024581 21540140136189251124754609)
        ·
          refine ⟨16155105102141938343565957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21540140136189251124754609 16155105102141938343565957)
          ·
            refine ⟨3029082206651613439418617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16155105102141938343565957 3029082206651613439418617)
            ·
              refine ⟨2271811654988710079563963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3029082206651613439418617 2271811654988710079563963)
              ·
                refine ⟨3407717482483065119345945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2271811654988710079563963 3407717482483065119345945)
                ·
                  refine ⟨2555788111862298839509459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3407717482483065119345945 2555788111862298839509459)
                  ·
                    refine ⟨3833682167793448259264189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2555788111862298839509459 3833682167793448259264189)
                    ·
                      refine ⟨1437630812922543097224071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3833682167793448259264189 1437630812922543097224071)
                      ·
                        rfl

theorem cell23_2799776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 4, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 4, 2, 1, 2, 1, 3].length) (baseStart_2799776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2799776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2799776 prefixEnd_2799776 := by exact prefixLift 2799776
  have htrace : WordTrace (prefixWord ++ tailWord_2799776) baseStart_2799776 baseEnd_2799776 := by
    simpa [prefixWord, tailWord_2799776, baseEnd_2799776] using wordTrace_append hprefix tailTrace_2799776
  have hstable : (prefixWord ++ tailWord_2799776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2799776).length < 2 ^ (prefixWord ++ tailWord_2799776).sum := by decide
  have hdescent : baseEnd_2799776 < baseStart_2799776 := by decide
  rcases family_descends (prefixWord ++ tailWord_2799776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2799786 : List Nat := [3, 1, 5, 1, 2, 1, 1, 1, 3, 3, 2]
def baseStart_2799786 : Nat := 118140960795 + 2799786 * 2 ^ 59
def prefixEnd_2799786 : Nat := 4983230072969 + 3 ^ 40 * 2799786 * 2
def baseEnd_2799786 : Nat := 1437635947729088058099025

theorem tailTrace_2799786 : CollatzResearch.WordTrace tailWord_2799786 prefixEnd_2799786 1437635947729088058099025 := by
  unfold tailWord_2799786
  simp only [CollatzResearch.WordTrace]
  refine ⟨25529146158715240556304803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68077723089907308150146141 25529146158715240556304803)
  ·
    refine ⟨38293719238072860834457205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25529146158715240556304803 38293719238072860834457205)
    ·
      refine ⟨3590036178569330703230363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 38293719238072860834457205 3590036178569330703230363)
      ·
        refine ⟨5385054267853996054845545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3590036178569330703230363 5385054267853996054845545)
        ·
          refine ⟨4038790700890497041134159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5385054267853996054845545 4038790700890497041134159)
          ·
            refine ⟨6058186051335745561701239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4038790700890497041134159 6058186051335745561701239)
            ·
              refine ⟨9087279077003618342551859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6058186051335745561701239 9087279077003618342551859)
              ·
                refine ⟨13630918615505427513827789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9087279077003618342551859 13630918615505427513827789)
                ·
                  refine ⟨5111594480814535317685421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13630918615505427513827789 5111594480814535317685421)
                  ·
                    refine ⟨1916847930305450744132033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5111594480814535317685421 1916847930305450744132033)
                    ·
                      refine ⟨1437635947729088058099025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1916847930305450744132033 1437635947729088058099025)
                      ·
                        rfl

theorem cell23_2799786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 1, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 1, 1, 1, 3, 3, 2].length) (baseStart_2799786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2799786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2799786 prefixEnd_2799786 := by exact prefixLift 2799786
  have htrace : WordTrace (prefixWord ++ tailWord_2799786) baseStart_2799786 baseEnd_2799786 := by
    simpa [prefixWord, tailWord_2799786, baseEnd_2799786] using wordTrace_append hprefix tailTrace_2799786
  have hstable : (prefixWord ++ tailWord_2799786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2799786).length < 2 ^ (prefixWord ++ tailWord_2799786).sum := by decide
  have hdescent : baseEnd_2799786 < baseStart_2799786 := by decide
  rcases family_descends (prefixWord ++ tailWord_2799786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2799832 : List Nat := [2, 1, 2, 2, 4, 2, 1, 1, 2, 3, 3]
def baseStart_2799832 : Nat := 118140960795 + 2799832 * 2 ^ 59
def prefixEnd_2799832 : Nat := 4983230072969 + 3 ^ 40 * 2799832 * 2
def baseEnd_2799832 : Nat := 1437659567839194878123813

theorem tailTrace_2799832 : CollatzResearch.WordTrace tailWord_2799832 prefixEnd_2799832 1437659567839194878123813 := by
  unfold tailWord_2799832
  simp only [CollatzResearch.WordTrace]
  refine ⟨51059131196347156040696875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68078841595129541387595833 51059131196347156040696875)
  ·
    refine ⟨76588696794520734061045313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51059131196347156040696875 76588696794520734061045313)
    ·
      refine ⟨57441522595890550545783985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76588696794520734061045313 57441522595890550545783985)
      ·
        refine ⟨43081141946917912909337989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57441522595890550545783985 43081141946917912909337989)
        ·
          refine ⟨8077714115047108670500873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 43081141946917912909337989 8077714115047108670500873)
          ·
            refine ⟨6058285586285331502875655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8077714115047108670500873 6058285586285331502875655)
            ·
              refine ⟨9087428379427997254313483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6058285586285331502875655 9087428379427997254313483)
              ·
                refine ⟨13631142569141995881470225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9087428379427997254313483 13631142569141995881470225)
                ·
                  refine ⟨10223356926856496911102669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13631142569141995881470225 10223356926856496911102669)
                  ·
                    refine ⟨3833758847571186341663501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10223356926856496911102669 3833758847571186341663501)
                    ·
                      refine ⟨1437659567839194878123813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3833758847571186341663501 1437659567839194878123813)
                      ·
                        rfl

theorem cell23_2799832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 2, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 2, 1, 1, 2, 3, 3].length) (baseStart_2799832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2799832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2799832 prefixEnd_2799832 := by exact prefixLift 2799832
  have htrace : WordTrace (prefixWord ++ tailWord_2799832) baseStart_2799832 baseEnd_2799832 := by
    simpa [prefixWord, tailWord_2799832, baseEnd_2799832] using wordTrace_append hprefix tailTrace_2799832
  have hstable : (prefixWord ++ tailWord_2799832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2799832).length < 2 ^ (prefixWord ++ tailWord_2799832).sum := by decide
  have hdescent : baseEnd_2799832 < baseStart_2799832 := by decide
  rcases family_descends (prefixWord ++ tailWord_2799832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2799872 : List Nat := [2, 1, 1, 2, 1, 1, 5, 2, 2, 4, 2]
def baseStart_2799872 : Nat := 118140960795 + 2799872 * 2 ^ 59
def prefixEnd_2799872 : Nat := 4983230072969 + 3 ^ 40 * 2799872 * 2
def baseEnd_2799872 : Nat := 1437680107065374721623629

theorem tailTrace_2799872 : CollatzResearch.WordTrace tailWord_2799872 prefixEnd_2799872 1437680107065374721623629 := by
  unfold tailWord_2799872
  simp only [CollatzResearch.WordTrace]
  refine ⟨51059860656274699456424935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68079814208366265941899913 51059860656274699456424935)
  ·
    refine ⟨76589790984412049184637403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51059860656274699456424935 76589790984412049184637403)
    ·
      refine ⟨114884686476618073776956105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76589790984412049184637403 114884686476618073776956105)
      ·
        refine ⟨86163514857463555332717079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 114884686476618073776956105 86163514857463555332717079)
        ·
          refine ⟨129245272286195332999075619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86163514857463555332717079 129245272286195332999075619)
          ·
            refine ⟨193867908429292999498613429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 129245272286195332999075619 193867908429292999498613429)
            ·
              refine ⟨18175116415246218702995009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 193867908429292999498613429 18175116415246218702995009)
              ·
                refine ⟨13631337311434664027246257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18175116415246218702995009 13631337311434664027246257)
                ·
                  refine ⟨10223502983575998020434693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13631337311434664027246257 10223502983575998020434693)
                  ·
                    refine ⟨1916906809420499628831505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10223502983575998020434693 1916906809420499628831505)
                    ·
                      refine ⟨1437680107065374721623629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1916906809420499628831505 1437680107065374721623629)
                      ·
                        rfl

theorem cell23_2799872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 5, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 5, 2, 2, 4, 2].length) (baseStart_2799872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2799872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2799872 prefixEnd_2799872 := by exact prefixLift 2799872
  have htrace : WordTrace (prefixWord ++ tailWord_2799872) baseStart_2799872 baseEnd_2799872 := by
    simpa [prefixWord, tailWord_2799872, baseEnd_2799872] using wordTrace_append hprefix tailTrace_2799872
  have hstable : (prefixWord ++ tailWord_2799872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2799872).length < 2 ^ (prefixWord ++ tailWord_2799872).sum := by decide
  have hdescent : baseEnd_2799872 < baseStart_2799872 := by decide
  rcases family_descends (prefixWord ++ tailWord_2799872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2799882 : List Nat := [3, 1, 2, 2, 1, 1, 3, 3, 3, 4]
def baseStart_2799882 : Nat := 118140960795 + 2799882 * 2 ^ 59
def prefixEnd_2799882 : Nat := 4983230072969 + 3 ^ 40 * 2799882 * 2
def baseEnd_2799882 : Nat := 479228413957306560832861

theorem tailTrace_2799882 : CollatzResearch.WordTrace tailWord_2799882 prefixEnd_2799882 479228413957306560832861 := by
  unfold tailWord_2799882
  simp only [CollatzResearch.WordTrace]
  refine ⟨25530021510628292655178475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68080057361675447080475933 25530021510628292655178475)
  ·
    refine ⟨38295032265942438982767713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25530021510628292655178475 38295032265942438982767713)
    ·
      refine ⟨28721274199456829237075785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38295032265942438982767713 28721274199456829237075785)
      ·
        refine ⟨21540955649592621927806839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28721274199456829237075785 21540955649592621927806839)
        ·
          refine ⟨32311433474388932891710259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21540955649592621927806839 32311433474388932891710259)
          ·
            refine ⟨48467150211583399337565389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32311433474388932891710259 48467150211583399337565389)
            ·
              refine ⟨18175181329343774751587021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 48467150211583399337565389 18175181329343774751587021)
              ·
                refine ⟨6815692998503915531845133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18175181329343774751587021 6815692998503915531845133)
                ·
                  refine ⟨2555884874438968324441925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6815692998503915531845133 2555884874438968324441925)
                  ·
                    refine ⟨479228413957306560832861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2555884874438968324441925 479228413957306560832861)
                    ·
                      rfl

theorem cell23_2799882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 3, 3, 3, 4].length) (baseStart_2799882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2799882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2799882 prefixEnd_2799882 := by exact prefixLift 2799882
  have htrace : WordTrace (prefixWord ++ tailWord_2799882) baseStart_2799882 baseEnd_2799882 := by
    simpa [prefixWord, tailWord_2799882, baseEnd_2799882] using wordTrace_append hprefix tailTrace_2799882
  have hstable : (prefixWord ++ tailWord_2799882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2799882).length < 2 ^ (prefixWord ++ tailWord_2799882).sum := by decide
  have hdescent : baseEnd_2799882 < baseStart_2799882 := by decide
  rcases family_descends (prefixWord ++ tailWord_2799882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2799939 : List Nat := [1, 1, 1, 3, 1, 3, 5, 1, 3, 1, 3]
def baseStart_2799939 : Nat := 118140960795 + 2799939 * 2 ^ 59
def prefixEnd_2799939 : Nat := 4983230072969 + 3 ^ 40 * 2799939 * 2
def baseEnd_2799939 : Nat := 1437714510269225959485821

theorem tailTrace_2799939 : CollatzResearch.WordTrace tailWord_2799939 prefixEnd_2799939 1437714510269225959485821 := by
  unfold tailWord_2799939
  simp only [CollatzResearch.WordTrace]
  refine ⟨102122165003306669355538871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68081443335537779570359247 102122165003306669355538871)
  ·
    refine ⟨153183247504960004033308307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102122165003306669355538871 153183247504960004033308307)
    ·
      refine ⟨229774871257440006049962461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 153183247504960004033308307 229774871257440006049962461)
      ·
        refine ⟨86165576721540002268735923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 229774871257440006049962461 86165576721540002268735923)
        ·
          refine ⟨129248365082310003403103885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86165576721540002268735923 129248365082310003403103885)
          ·
            refine ⟨48468136905866251276163957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 129248365082310003403103885 48468136905866251276163957)
            ·
              refine ⟨4543887834924961057140371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 48468136905866251276163957 4543887834924961057140371)
              ·
                refine ⟨6815831752387441585710557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4543887834924961057140371 6815831752387441585710557)
                ·
                  refine ⟨2555936907145290594641459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6815831752387441585710557 2555936907145290594641459)
                  ·
                    refine ⟨3833905360717935891962189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2555936907145290594641459 3833905360717935891962189)
                    ·
                      refine ⟨1437714510269225959485821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3833905360717935891962189 1437714510269225959485821)
                      ·
                        rfl

theorem cell23_2799939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 5, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 5, 1, 3, 1, 3].length) (baseStart_2799939 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2799939 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2799939 prefixEnd_2799939 := by exact prefixLift 2799939
  have htrace : WordTrace (prefixWord ++ tailWord_2799939) baseStart_2799939 baseEnd_2799939 := by
    simpa [prefixWord, tailWord_2799939, baseEnd_2799939] using wordTrace_append hprefix tailTrace_2799939
  have hstable : (prefixWord ++ tailWord_2799939).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2799939).length < 2 ^ (prefixWord ++ tailWord_2799939).sum := by decide
  have hdescent : baseEnd_2799939 < baseStart_2799939 := by decide
  rcases family_descends (prefixWord ++ tailWord_2799939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2799945 : List Nat := [1, 2, 1, 1, 2, 3, 1, 1, 2, 5, 4]
def baseStart_2799945 : Nat := 118140960795 + 2799945 * 2 ^ 59
def prefixEnd_2799945 : Nat := 4983230072969 + 3 ^ 40 * 2799945 * 2
def baseEnd_2799945 : Nat := 1437717591153152936010793

theorem tailTrace_2799945 : CollatzResearch.WordTrace tailWord_2799945 prefixEnd_2799945 1437717591153152936010793 := by
  unfold tailWord_2799945
  simp only [CollatzResearch.WordTrace]
  refine ⟨102122383841284932380257289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68081589227523288253504859 102122383841284932380257289)
  ·
    refine ⟨76591787880963699285192967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102122383841284932380257289 76591787880963699285192967)
    ·
      refine ⟨114887681821445548927789451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76591787880963699285192967 114887681821445548927789451)
      ·
        refine ⟨172331522732168323391684177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114887681821445548927789451 172331522732168323391684177)
        ·
          refine ⟨129248642049126242543763133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 172331522732168323391684177 129248642049126242543763133)
          ·
            refine ⟨48468240768422340953911175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 129248642049126242543763133 48468240768422340953911175)
            ·
              refine ⟨72702361152633511430866763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48468240768422340953911175 72702361152633511430866763)
              ·
                refine ⟨109053541728950267146300145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 72702361152633511430866763 109053541728950267146300145)
                ·
                  refine ⟨81790156296712700359725109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 109053541728950267146300145 81790156296712700359725109)
                  ·
                    refine ⟨7667827152816815658724229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 81790156296712700359725109 7667827152816815658724229)
                    ·
                      refine ⟨1437717591153152936010793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7667827152816815658724229 1437717591153152936010793)
                      ·
                        rfl

theorem cell23_2799945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 1, 2, 5, 4].length) (baseStart_2799945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2799945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2799945 prefixEnd_2799945 := by exact prefixLift 2799945
  have htrace : WordTrace (prefixWord ++ tailWord_2799945) baseStart_2799945 baseEnd_2799945 := by
    simpa [prefixWord, tailWord_2799945, baseEnd_2799945] using wordTrace_append hprefix tailTrace_2799945
  have hstable : (prefixWord ++ tailWord_2799945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2799945).length < 2 ^ (prefixWord ++ tailWord_2799945).sum := by decide
  have hdescent : baseEnd_2799945 < baseStart_2799945 := by decide
  rcases family_descends (prefixWord ++ tailWord_2799945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2799972 : List Nat := [2, 3, 1, 1, 3, 1, 3, 2, 1, 6]
def baseStart_2799972 : Nat := 118140960795 + 2799972 * 2 ^ 59
def prefixEnd_2799972 : Nat := 4983230072969 + 3 ^ 40 * 2799972 * 2
def baseEnd_2799972 : Nat := 479243818376941443457723

theorem tailTrace_2799972 : CollatzResearch.WordTrace tailWord_2799972 prefixEnd_2799972 479243818376941443457723 := by
  unfold tailWord_2799972
  simp only [CollatzResearch.WordTrace]
  refine ⟨51061684306093557995745085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68082245741458077327660113 51061684306093557995745085)
  ·
    refine ⟨19148131614785084248404407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51061684306093557995745085 19148131614785084248404407)
    ·
      refine ⟨28722197422177626372606611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19148131614785084248404407 28722197422177626372606611)
      ·
        refine ⟨43083296133266439558909917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28722197422177626372606611 43083296133266439558909917)
        ·
          refine ⟨16156236049974914834591219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43083296133266439558909917 16156236049974914834591219)
          ·
            refine ⟨24234354074962372251886829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16156236049974914834591219 24234354074962372251886829)
            ·
              refine ⟨9087882778110889594457561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24234354074962372251886829 9087882778110889594457561)
              ·
                refine ⟨6815912083583167195843171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9087882778110889594457561 6815912083583167195843171)
                ·
                  refine ⟨10223868125374750793764757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6815912083583167195843171 10223868125374750793764757)
                  ·
                    refine ⟨479243818376941443457723, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10223868125374750793764757 479243818376941443457723)
                    ·
                      rfl

theorem cell23_2799972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 3, 2, 1, 6].length) (baseStart_2799972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2799972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2799972 prefixEnd_2799972 := by exact prefixLift 2799972
  have htrace : WordTrace (prefixWord ++ tailWord_2799972) baseStart_2799972 baseEnd_2799972 := by
    simpa [prefixWord, tailWord_2799972, baseEnd_2799972] using wordTrace_append hprefix tailTrace_2799972
  have hstable : (prefixWord ++ tailWord_2799972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2799972).length < 2 ^ (prefixWord ++ tailWord_2799972).sum := by decide
  have hdescent : baseEnd_2799972 < baseStart_2799972 := by decide
  rcases family_descends (prefixWord ++ tailWord_2799972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2799976 : List Nat := [2, 1, 4, 2, 2, 2, 3, 1, 1, 5]
def baseStart_2799976 : Nat := 118140960795 + 2799976 * 2 ^ 59
def prefixEnd_2799976 : Nat := 4983230072969 + 3 ^ 40 * 2799976 * 2
def baseEnd_2799976 : Nat := 479244503017814104907717

theorem tailTrace_2799976 : CollatzResearch.WordTrace tailWord_2799976 prefixEnd_2799976 479244503017814104907717 := by
  unfold tailWord_2799976
  simp only [CollatzResearch.WordTrace]
  refine ⟨51061757252086312337317891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68082343002781749783090521 51061757252086312337317891)
  ·
    refine ⟨76592635878129468505976837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51061757252086312337317891 76592635878129468505976837)
    ·
      refine ⟨14361119227149275344870657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 76592635878129468505976837 14361119227149275344870657)
      ·
        refine ⟨10770839420361956508652993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14361119227149275344870657 10770839420361956508652993)
        ·
          refine ⟨8078129565271467381489745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10770839420361956508652993 8078129565271467381489745)
          ·
            refine ⟨6058597173953600536117309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8078129565271467381489745 6058597173953600536117309)
            ·
              refine ⟨2271973940232600201043991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6058597173953600536117309 2271973940232600201043991)
              ·
                refine ⟨3407960910348900301565987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2271973940232600201043991 3407960910348900301565987)
                ·
                  refine ⟨5111941365523350452348981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3407960910348900301565987 5111941365523350452348981)
                  ·
                    refine ⟨479244503017814104907717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5111941365523350452348981 479244503017814104907717)
                    ·
                      rfl

theorem cell23_2799976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 2, 3, 1, 1, 5].length) (baseStart_2799976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2799976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2799976 prefixEnd_2799976 := by exact prefixLift 2799976
  have htrace : WordTrace (prefixWord ++ tailWord_2799976) baseStart_2799976 baseEnd_2799976 := by
    simpa [prefixWord, tailWord_2799976, baseEnd_2799976] using wordTrace_append hprefix tailTrace_2799976
  have hstable : (prefixWord ++ tailWord_2799976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2799976).length < 2 ^ (prefixWord ++ tailWord_2799976).sum := by decide
  have hdescent : baseEnd_2799976 < baseStart_2799976 := by decide
  rcases family_descends (prefixWord ++ tailWord_2799976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2799979 : List Nat := [1, 1, 1, 1, 2, 2, 2, 4, 5, 2, 2]
def baseStart_2799979 : Nat := 118140960795 + 2799979 * 2 ^ 59
def prefixEnd_2799979 : Nat := 4983230072969 + 3 ^ 40 * 2799979 * 2
def baseEnd_2799979 : Nat := 1437735049495405802985637

theorem tailTrace_2799979 : CollatzResearch.WordTrace tailWord_2799979 prefixEnd_2799979 1437735049495405802985637 := by
  unfold tailWord_2799979
  simp only [CollatzResearch.WordTrace]
  refine ⟨102123623923161756186994991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68082415948774504124663327 102123623923161756186994991)
  ·
    refine ⟨153185435884742634280492487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102123623923161756186994991 153185435884742634280492487)
    ·
      refine ⟨229778153827113951420738731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 153185435884742634280492487 229778153827113951420738731)
      ·
        refine ⟨344667230740670927131108097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 229778153827113951420738731 344667230740670927131108097)
        ·
          refine ⟨258500423055503195348331073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 344667230740670927131108097 258500423055503195348331073)
          ·
            refine ⟨193875317291627396511248305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 258500423055503195348331073 193875317291627396511248305)
            ·
              refine ⟨145406487968720547383436229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 193875317291627396511248305 145406487968720547383436229)
              ·
                refine ⟨27263716494135102634394293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 145406487968720547383436229 27263716494135102634394293)
                ·
                  refine ⟨2555973421325165871974465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 27263716494135102634394293 2555973421325165871974465)
                  ·
                    refine ⟨1916980065993874403980849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2555973421325165871974465 1916980065993874403980849)
                    ·
                      refine ⟨1437735049495405802985637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1916980065993874403980849 1437735049495405802985637)
                      ·
                        rfl

theorem cell23_2799979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 4, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 4, 5, 2, 2].length) (baseStart_2799979 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2799979 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2799979 prefixEnd_2799979 := by exact prefixLift 2799979
  have htrace : WordTrace (prefixWord ++ tailWord_2799979) baseStart_2799979 baseEnd_2799979 := by
    simpa [prefixWord, tailWord_2799979, baseEnd_2799979] using wordTrace_append hprefix tailTrace_2799979
  have hstable : (prefixWord ++ tailWord_2799979).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2799979).length < 2 ^ (prefixWord ++ tailWord_2799979).sum := by decide
  have hdescent : baseEnd_2799979 < baseStart_2799979 := by decide
  rcases family_descends (prefixWord ++ tailWord_2799979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2800009 : List Nat := [1, 2, 1, 1, 6, 2, 2, 1, 1, 2, 4]
def baseStart_2800009 : Nat := 118140960795 + 2800009 * 2 ^ 59
def prefixEnd_2800009 : Nat := 4983230072969 + 3 ^ 40 * 2800009 * 2
def baseEnd_2800009 : Nat := 1437750453915040685610499

theorem tailTrace_2800009 : CollatzResearch.WordTrace tailWord_2800009 prefixEnd_2800009 1437750453915040685610499 := by
  unfold tailWord_2800009
  simp only [CollatzResearch.WordTrace]
  refine ⟨102124718113053071310587081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68083145408702047540391387 102124718113053071310587081)
  ·
    refine ⟨76593538584789803482940311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102124718113053071310587081 76593538584789803482940311)
    ·
      refine ⟨114890307877184705224410467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76593538584789803482940311 114890307877184705224410467)
      ·
        refine ⟨172335461815777057836615701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114890307877184705224410467 172335461815777057836615701)
        ·
          refine ⟨8078224772614549586091361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 172335461815777057836615701 8078224772614549586091361)
          ·
            refine ⟨6058668579460912189568521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8078224772614549586091361 6058668579460912189568521)
            ·
              refine ⟨4544001434595684142176391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6058668579460912189568521 4544001434595684142176391)
              ·
                refine ⟨6816002151893526213264587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4544001434595684142176391 6816002151893526213264587)
                ·
                  refine ⟨10224003227840289319896881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6816002151893526213264587 10224003227840289319896881)
                  ·
                    refine ⟨7668002420880216989922661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10224003227840289319896881 7668002420880216989922661)
                    ·
                      refine ⟨1437750453915040685610499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7668002420880216989922661 1437750453915040685610499)
                      ·
                        rfl

theorem cell23_2800009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 2, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 2, 2, 1, 1, 2, 4].length) (baseStart_2800009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2800009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2800009 prefixEnd_2800009 := by exact prefixLift 2800009
  have htrace : WordTrace (prefixWord ++ tailWord_2800009) baseStart_2800009 baseEnd_2800009 := by
    simpa [prefixWord, tailWord_2800009, baseEnd_2800009] using wordTrace_append hprefix tailTrace_2800009
  have hstable : (prefixWord ++ tailWord_2800009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2800009).length < 2 ^ (prefixWord ++ tailWord_2800009).sum := by decide
  have hdescent : baseEnd_2800009 < baseStart_2800009 := by decide
  rcases family_descends (prefixWord ++ tailWord_2800009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2800030 : List Nat := [4, 3, 1, 2, 1, 3, 2, 1, 1, 1, 4]
def baseStart_2800030 : Nat := 118140960795 + 2800030 * 2 ^ 59
def prefixEnd_2800030 : Nat := 4983230072969 + 3 ^ 40 * 2800030 * 2
def baseEnd_2800030 : Nat := 1437761237008785103447903

theorem tailTrace_2800030 : CollatzResearch.WordTrace tailWord_2800030 prefixEnd_2800030 1437761237008785103447903 := by
  unfold tailWord_2800030
  simp only [CollatzResearch.WordTrace]
  refine ⟨12765685505747123987137693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 68083656030651327931401029 12765685505747123987137693)
  ·
    refine ⟨4787132064655171495176635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12765685505747123987137693 4787132064655171495176635)
    ·
      refine ⟨7180698096982757242764953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4787132064655171495176635 7180698096982757242764953)
      ·
        refine ⟨5385523572737067932073715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7180698096982757242764953 5385523572737067932073715)
        ·
          refine ⟨8078285359105601898110573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5385523572737067932073715 8078285359105601898110573)
          ·
            refine ⟨3029357009664600711791465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8078285359105601898110573 3029357009664600711791465)
            ·
              refine ⟨2272017757248450533843599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3029357009664600711791465 2272017757248450533843599)
              ·
                refine ⟨3408026635872675800765399, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2272017757248450533843599 3408026635872675800765399)
                ·
                  refine ⟨5112039953809013701148099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3408026635872675800765399 5112039953809013701148099)
                  ·
                    refine ⟨7668059930713520551722149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5112039953809013701148099 7668059930713520551722149)
                    ·
                      refine ⟨1437761237008785103447903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7668059930713520551722149 1437761237008785103447903)
                      ·
                        rfl

theorem cell23_2800030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 3, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 3, 2, 1, 1, 1, 4].length) (baseStart_2800030 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2800030 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2800030 prefixEnd_2800030 := by exact prefixLift 2800030
  have htrace : WordTrace (prefixWord ++ tailWord_2800030) baseStart_2800030 baseEnd_2800030 := by
    simpa [prefixWord, tailWord_2800030, baseEnd_2800030] using wordTrace_append hprefix tailTrace_2800030
  have hstable : (prefixWord ++ tailWord_2800030).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2800030).length < 2 ^ (prefixWord ++ tailWord_2800030).sum := by decide
  have hdescent : baseEnd_2800030 < baseStart_2800030 := by decide
  rcases family_descends (prefixWord ++ tailWord_2800030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2800033 : List Nat := [1, 2, 3, 5, 1, 1, 1, 3, 1, 2, 3]
def baseStart_2800033 : Nat := 118140960795 + 2800033 * 2 ^ 59
def prefixEnd_2800033 : Nat := 4983230072969 + 3 ^ 40 * 2800033 * 2
def baseEnd_2800033 : Nat := 1437762777450748591710389

theorem tailTrace_2800033 : CollatzResearch.WordTrace tailWord_2800033 prefixEnd_2800033 1437762777450748591710389 := by
  unfold tailWord_2800033
  simp only [CollatzResearch.WordTrace]
  refine ⟨102125593464966123409460753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68083728976644082272973835 102125593464966123409460753)
  ·
    refine ⟨76594195098724592557095565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102125593464966123409460753 76594195098724592557095565)
    ·
      refine ⟨28722823162021722208910837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 76594195098724592557095565 28722823162021722208910837)
      ·
        refine ⟨2692764671439536457085391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 28722823162021722208910837 2692764671439536457085391)
        ·
          refine ⟨4039147007159304685628087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2692764671439536457085391 4039147007159304685628087)
          ·
            refine ⟨6058720510738957028442131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4039147007159304685628087 6058720510738957028442131)
            ·
              refine ⟨9088080766108435542663197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6058720510738957028442131 9088080766108435542663197)
              ·
                refine ⟨3408030287290663328498699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9088080766108435542663197 3408030287290663328498699)
                ·
                  refine ⟨5112045430935994992748049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3408030287290663328498699 5112045430935994992748049)
                  ·
                    refine ⟨3834034073201996244561037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5112045430935994992748049 3834034073201996244561037)
                    ·
                      refine ⟨1437762777450748591710389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3834034073201996244561037 1437762777450748591710389)
                      ·
                        rfl

theorem cell23_2800033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 1, 1, 3, 1, 2, 3].length) (baseStart_2800033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2800033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2800033 prefixEnd_2800033 := by exact prefixLift 2800033
  have htrace : WordTrace (prefixWord ++ tailWord_2800033) baseStart_2800033 baseEnd_2800033 := by
    simpa [prefixWord, tailWord_2800033, baseEnd_2800033] using wordTrace_append hprefix tailTrace_2800033
  have hstable : (prefixWord ++ tailWord_2800033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2800033).length < 2 ^ (prefixWord ++ tailWord_2800033).sum := by decide
  have hdescent : baseEnd_2800033 < baseStart_2800033 := by decide
  rcases family_descends (prefixWord ++ tailWord_2800033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2800103 : List Nat := [1, 1, 5, 2, 1, 1, 2, 4, 2, 2, 2]
def baseStart_2800103 : Nat := 118140960795 + 2800103 * 2 ^ 59
def prefixEnd_2800103 : Nat := 4983230072969 + 3 ^ 40 * 2800103 * 2
def baseEnd_2800103 : Nat := 1437798721096563317835067

theorem tailTrace_2800103 : CollatzResearch.WordTrace tailWord_2800103 prefixEnd_2800103 1437798721096563317835067 := by
  unfold tailWord_2800103
  simp only [CollatzResearch.WordTrace]
  refine ⟨102128146574712525364508963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68085431049808350243005975 102128146574712525364508963)
  ·
    refine ⟨153192219862068788046763445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102128146574712525364508963 153192219862068788046763445)
    ·
      refine ⟨14361770612068948879384073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 153192219862068788046763445 14361770612068948879384073)
      ·
        refine ⟨10771327959051711659538055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14361770612068948879384073 10771327959051711659538055)
        ·
          refine ⟨16156991938577567489307083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10771327959051711659538055 16156991938577567489307083)
          ·
            refine ⟨24235487907866351233960625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16156991938577567489307083 24235487907866351233960625)
            ·
              refine ⟨18176615930899763425470469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24235487907866351233960625 18176615930899763425470469)
              ·
                refine ⟨3408115487043705642275713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18176615930899763425470469 3408115487043705642275713)
                ·
                  refine ⟨2556086615282779231706785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3408115487043705642275713 2556086615282779231706785)
                  ·
                    refine ⟨1917064961462084423780089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2556086615282779231706785 1917064961462084423780089)
                    ·
                      refine ⟨1437798721096563317835067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1917064961462084423780089 1437798721096563317835067)
                      ·
                        rfl

theorem cell23_2800103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 2, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 2, 4, 2, 2, 2].length) (baseStart_2800103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2800103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2800103 prefixEnd_2800103 := by exact prefixLift 2800103
  have htrace : WordTrace (prefixWord ++ tailWord_2800103) baseStart_2800103 baseEnd_2800103 := by
    simpa [prefixWord, tailWord_2800103, baseEnd_2800103] using wordTrace_append hprefix tailTrace_2800103
  have hstable : (prefixWord ++ tailWord_2800103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2800103).length < 2 ^ (prefixWord ++ tailWord_2800103).sum := by decide
  have hdescent : baseEnd_2800103 < baseStart_2800103 := by decide
  rcases family_descends (prefixWord ++ tailWord_2800103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2800122 : List Nat := [3, 1, 1, 1, 1, 2, 2, 4, 1, 7]
def baseStart_2800122 : Nat := 118140960795 + 2800122 * 2 ^ 59
def prefixEnd_2800122 : Nat := 4983230072969 + 3 ^ 40 * 2800122 * 2
def baseEnd_2800122 : Nat := 479269492409666247832493

theorem tailTrace_2800122 : CollatzResearch.WordTrace tailWord_2800122 prefixEnd_2800122 479269492409666247832493 := by
  unfold tailWord_2800122
  simp only [CollatzResearch.WordTrace]
  refine ⟨25532209890410922902362655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68085893041095794406300413 25532209890410922902362655)
  ·
    refine ⟨38298314835616384353543983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25532209890410922902362655 38298314835616384353543983)
    ·
      refine ⟨57447472253424576530315975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38298314835616384353543983 57447472253424576530315975)
      ·
        refine ⟨86171208380136864795473963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57447472253424576530315975 86171208380136864795473963)
        ·
          refine ⟨129256812570205297193210945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86171208380136864795473963 129256812570205297193210945)
          ·
            refine ⟨96942609427653972894908209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 129256812570205297193210945 96942609427653972894908209)
            ·
              refine ⟨72706957070740479671181157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 96942609427653972894908209 72706957070740479671181157)
              ·
                refine ⟨13632554450763839938346467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 72706957070740479671181157 13632554450763839938346467)
                ·
                  refine ⟨20448831676145759907519701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13632554450763839938346467 20448831676145759907519701)
                  ·
                    refine ⟨479269492409666247832493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 20448831676145759907519701 479269492409666247832493)
                    ·
                      rfl

theorem cell23_2800122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 4, 1, 7].length) (baseStart_2800122 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2800122 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2800122 prefixEnd_2800122 := by exact prefixLift 2800122
  have htrace : WordTrace (prefixWord ++ tailWord_2800122) baseStart_2800122 baseEnd_2800122 := by
    simpa [prefixWord, tailWord_2800122, baseEnd_2800122] using wordTrace_append hprefix tailTrace_2800122
  have hstable : (prefixWord ++ tailWord_2800122).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2800122).length < 2 ^ (prefixWord ++ tailWord_2800122).sum := by decide
  have hdescent : baseEnd_2800122 < baseStart_2800122 := by decide
  rcases family_descends (prefixWord ++ tailWord_2800122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2800139 : List Nat := [1, 1, 1, 1, 7, 1, 1, 3, 2, 5]
def baseStart_2800139 : Nat := 118140960795 + 2800139 * 2 ^ 59
def prefixEnd_2800139 : Nat := 4983230072969 + 3 ^ 40 * 2800139 * 2
def baseEnd_2800139 : Nat := 479272402133375058994967

theorem tailTrace_2800139 : CollatzResearch.WordTrace tailWord_2800139 prefixEnd_2800139 479272402133375058994967 := by
  unfold tailWord_2800139
  simp only [CollatzResearch.WordTrace]
  refine ⟨102129459602582103512819471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68086306401721402341879647 102129459602582103512819471)
  ·
    refine ⟨153194189403873155269229207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102129459602582103512819471 153194189403873155269229207)
    ·
      refine ⟨229791284105809732903843811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 153194189403873155269229207 229791284105809732903843811)
      ·
        refine ⟨344686926158714599355765717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 229791284105809732903843811 344686926158714599355765717)
        ·
          refine ⟨8078599831844873422400759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 344686926158714599355765717 8078599831844873422400759)
          ·
            refine ⟨12117899747767310133601139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8078599831844873422400759 12117899747767310133601139)
            ·
              refine ⟨18176849621650965200401709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12117899747767310133601139 18176849621650965200401709)
              ·
                refine ⟨6816318608119111950150641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18176849621650965200401709 6816318608119111950150641)
                ·
                  refine ⟨5112238956089333962612981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6816318608119111950150641 5112238956089333962612981)
                  ·
                    refine ⟨479272402133375058994967, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5112238956089333962612981 479272402133375058994967)
                    ·
                      rfl

theorem cell23_2800139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 1, 3, 2, 5].length) (baseStart_2800139 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2800139 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2800139 prefixEnd_2800139 := by exact prefixLift 2800139
  have htrace : WordTrace (prefixWord ++ tailWord_2800139) baseStart_2800139 baseEnd_2800139 := by
    simpa [prefixWord, tailWord_2800139, baseEnd_2800139] using wordTrace_append hprefix tailTrace_2800139
  have hstable : (prefixWord ++ tailWord_2800139).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2800139).length < 2 ^ (prefixWord ++ tailWord_2800139).sum := by decide
  have hdescent : baseEnd_2800139 < baseStart_2800139 := by decide
  rcases family_descends (prefixWord ++ tailWord_2800139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2800160 : List Nat := [2, 1, 1, 6, 2, 2, 2, 2, 5]
def baseStart_2800160 : Nat := 118140960795 + 2800160 * 2 ^ 59
def prefixEnd_2800160 : Nat := 4983230072969 + 3 ^ 40 * 2800160 * 2
def baseEnd_2800160 : Nat := 159758665499318843869145

theorem tailTrace_2800160 : CollatzResearch.WordTrace tailWord_2800160 prefixEnd_2800160 159758665499318843869145 := by
  unfold tailWord_2800160
  simp only [CollatzResearch.WordTrace]
  refine ⟨51065112767753012049666967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68086817023670682732889289 51065112767753012049666967)
  ·
    refine ⟨76597669151629518074500451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51065112767753012049666967 76597669151629518074500451)
    ·
      refine ⟨114896503727444277111750677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76597669151629518074500451 114896503727444277111750677)
      ·
        refine ⟨5385773612223950489613313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 114896503727444277111750677 5385773612223950489613313)
        ·
          refine ⟨4039330209167962867209985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5385773612223950489613313 4039330209167962867209985)
          ·
            refine ⟨3029497656875972150407489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4039330209167962867209985 3029497656875972150407489)
            ·
              refine ⟨2272123242656979112805617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3029497656875972150407489 2272123242656979112805617)
              ·
                refine ⟨1704092431992734334604213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2272123242656979112805617 1704092431992734334604213)
                ·
                  refine ⟨159758665499318843869145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1704092431992734334604213 159758665499318843869145)
                  ·
                    rfl

theorem cell23_2800160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 2, 2, 2, 5].length) (baseStart_2800160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2800160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2800160 prefixEnd_2800160 := by exact prefixLift 2800160
  have htrace : WordTrace (prefixWord ++ tailWord_2800160) baseStart_2800160 baseEnd_2800160 := by
    simpa [prefixWord, tailWord_2800160, baseEnd_2800160] using wordTrace_append hprefix tailTrace_2800160
  have hstable : (prefixWord ++ tailWord_2800160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2800160).length < 2 ^ (prefixWord ++ tailWord_2800160).sum := by decide
  have hdescent : baseEnd_2800160 < baseStart_2800160 := by decide
  rcases family_descends (prefixWord ++ tailWord_2800160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2800179 : List Nat := [1, 1, 1, 2, 4, 2, 2, 2, 1, 4, 3]
def baseStart_2800179 : Nat := 118140960795 + 2800179 * 2 ^ 59
def prefixEnd_2800179 : Nat := 4983230072969 + 3 ^ 40 * 2800179 * 2
def baseEnd_2800179 : Nat := 1437837745626305020484717

theorem tailTrace_2800179 : CollatzResearch.WordTrace tailWord_2800179 prefixEnd_2800179 1437837745626305020484717 := by
  unfold tailWord_2800179
  simp only [CollatzResearch.WordTrace]
  refine ⟨102130918522437190344275591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68087279014958126896183727 102130918522437190344275591)
  ·
    refine ⟨153196377783655785516413387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102130918522437190344275591 153196377783655785516413387)
    ·
      refine ⟨229794566675483678274620081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 153196377783655785516413387 229794566675483678274620081)
      ·
        refine ⟨172345925006612758705965061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 229794566675483678274620081 172345925006612758705965061)
        ·
          refine ⟨32314860938739892257368449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 172345925006612758705965061 32314860938739892257368449)
          ·
            refine ⟨24236145704054919193026337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32314860938739892257368449 24236145704054919193026337)
            ·
              refine ⟨18177109278041189394769753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24236145704054919193026337 18177109278041189394769753)
              ·
                refine ⟨13632831958530892046077315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18177109278041189394769753 13632831958530892046077315)
                ·
                  refine ⟨20449247937796338069115973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13632831958530892046077315 20449247937796338069115973)
                  ·
                    refine ⟨3834233988336813387959245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20449247937796338069115973 3834233988336813387959245)
                    ·
                      refine ⟨1437837745626305020484717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3834233988336813387959245 1437837745626305020484717)
                      ·
                        rfl

theorem cell23_2800179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 2, 2, 1, 4, 3].length) (baseStart_2800179 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2800179 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2800179 prefixEnd_2800179 := by exact prefixLift 2800179
  have htrace : WordTrace (prefixWord ++ tailWord_2800179) baseStart_2800179 baseEnd_2800179 := by
    simpa [prefixWord, tailWord_2800179, baseEnd_2800179] using wordTrace_append hprefix tailTrace_2800179
  have hstable : (prefixWord ++ tailWord_2800179).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2800179).length < 2 ^ (prefixWord ++ tailWord_2800179).sum := by decide
  have hdescent : baseEnd_2800179 < baseStart_2800179 := by decide
  rcases family_descends (prefixWord ++ tailWord_2800179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2800186 : List Nat := [3, 1, 1, 1, 3, 4, 1, 2, 3, 4]
def baseStart_2800186 : Nat := 118140960795 + 2800186 * 2 ^ 59
def prefixEnd_2800186 : Nat := 4983230072969 + 3 ^ 40 * 2800186 * 2
def baseEnd_2800186 : Nat := 479280446663628831032395

theorem tailTrace_2800186 : CollatzResearch.WordTrace tailWord_2800186 prefixEnd_2800186 479280446663628831032395 := by
  unfold tailWord_2800186
  simp only [CollatzResearch.WordTrace]
  refine ⟨25532793458352957634945103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68087449222274553693186941 25532793458352957634945103)
  ·
    refine ⟨38299190187529436452417655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25532793458352957634945103 38299190187529436452417655)
    ·
      refine ⟨57448785281294154678626483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38299190187529436452417655 57448785281294154678626483)
      ·
        refine ⟨86173177921941232017939725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57448785281294154678626483 86173177921941232017939725)
        ·
          refine ⟨32314941720727962006727397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 86173177921941232017939725 32314941720727962006727397)
          ·
            refine ⟨6059051572636492876261387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 32314941720727962006727397 6059051572636492876261387)
            ·
              refine ⟨9088577358954739314392081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6059051572636492876261387 9088577358954739314392081)
              ·
                refine ⟨6816433019216054485794061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9088577358954739314392081 6816433019216054485794061)
                ·
                  refine ⟨2556162382206020432172773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6816433019216054485794061 2556162382206020432172773)
                  ·
                    refine ⟨479280446663628831032395, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2556162382206020432172773 479280446663628831032395)
                    ·
                      rfl

theorem cell23_2800186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 4, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 4, 1, 2, 3, 4].length) (baseStart_2800186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2800186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2800186 prefixEnd_2800186 := by exact prefixLift 2800186
  have htrace : WordTrace (prefixWord ++ tailWord_2800186) baseStart_2800186 baseEnd_2800186 := by
    simpa [prefixWord, tailWord_2800186, baseEnd_2800186] using wordTrace_append hprefix tailTrace_2800186
  have hstable : (prefixWord ++ tailWord_2800186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2800186).length < 2 ^ (prefixWord ++ tailWord_2800186).sum := by decide
  have hdescent : baseEnd_2800186 < baseStart_2800186 := by decide
  rcases family_descends (prefixWord ++ tailWord_2800186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2800190 : List Nat := [4, 2, 1, 4, 1, 2, 1, 1, 2, 5]
def baseStart_2800190 : Nat := 118140960795 + 2800190 * 2 ^ 59
def prefixEnd_2800190 : Nat := 4983230072969 + 3 ^ 40 * 2800190 * 2
def baseEnd_2800190 : Nat := 479281131304501492482389

theorem tailTrace_2800190 : CollatzResearch.WordTrace tailWord_2800190 prefixEnd_2800190 479281131304501492482389 := by
  unfold tailWord_2800190
  simp only [CollatzResearch.WordTrace]
  refine ⟨12766414965674667402865753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 68087546483598226148617349 12766414965674667402865753)
  ·
    refine ⟨9574811224256000552149315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12766414965674667402865753 9574811224256000552149315)
    ·
      refine ⟨14362216836384000828223973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9574811224256000552149315 14362216836384000828223973)
      ·
        refine ⟨2692915656822000155291995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14362216836384000828223973 2692915656822000155291995)
        ·
          refine ⟨4039373485233000232937993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2692915656822000155291995 4039373485233000232937993)
          ·
            refine ⟨3029530113924750174703495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4039373485233000232937993 3029530113924750174703495)
            ·
              refine ⟨4544295170887125262055243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3029530113924750174703495 4544295170887125262055243)
              ·
                refine ⟨6816442756330687893082865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4544295170887125262055243 6816442756330687893082865)
                ·
                  refine ⟨5112332067248015919812149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6816442756330687893082865 5112332067248015919812149)
                  ·
                    refine ⟨479281131304501492482389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5112332067248015919812149 479281131304501492482389)
                    ·
                      rfl

theorem cell23_2800190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 2, 1, 1, 2, 5].length) (baseStart_2800190 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2800190 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2800190 prefixEnd_2800190 := by exact prefixLift 2800190
  have htrace : WordTrace (prefixWord ++ tailWord_2800190) baseStart_2800190 baseEnd_2800190 := by
    simpa [prefixWord, tailWord_2800190, baseEnd_2800190] using wordTrace_append hprefix tailTrace_2800190
  have hstable : (prefixWord ++ tailWord_2800190).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2800190).length < 2 ^ (prefixWord ++ tailWord_2800190).sum := by decide
  have hdescent : baseEnd_2800190 < baseStart_2800190 := by decide
  rcases family_descends (prefixWord ++ tailWord_2800190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2800193 : List Nat := [1, 2, 5, 1, 1, 4, 1, 1, 2, 1, 4]
def baseStart_2800193 : Nat := 118140960795 + 2800193 * 2 ^ 59
def prefixEnd_2800193 : Nat := 4983230072969 + 3 ^ 40 * 2800193 * 2
def baseEnd_2800193 : Nat := 1437844934355467965709653

theorem tailTrace_2800193 : CollatzResearch.WordTrace tailWord_2800193 prefixEnd_2800193 1437844934355467965709653 := by
  unfold tailWord_2800193
  simp only [CollatzResearch.WordTrace]
  refine ⟨102131429144386470735285233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68087619429590980490190155 102131429144386470735285233)
  ·
    refine ⟨76598571858289853051463925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102131429144386470735285233 76598571858289853051463925)
    ·
      refine ⟨7181116111714673723574743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 76598571858289853051463925 7181116111714673723574743)
      ·
        refine ⟨10771674167572010585362115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7181116111714673723574743 10771674167572010585362115)
        ·
          refine ⟨16157511251358015878043173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10771674167572010585362115 16157511251358015878043173)
          ·
            refine ⟨3029533359629627977133095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16157511251358015878043173 3029533359629627977133095)
            ·
              refine ⟨4544300039444441965699643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3029533359629627977133095 4544300039444441965699643)
              ·
                refine ⟨6816450059166662948549465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4544300039444441965699643 6816450059166662948549465)
                ·
                  refine ⟨5112337544374997211412099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6816450059166662948549465 5112337544374997211412099)
                  ·
                    refine ⟨7668506316562495817118149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5112337544374997211412099 7668506316562495817118149)
                    ·
                      refine ⟨1437844934355467965709653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7668506316562495817118149 1437844934355467965709653)
                      ·
                        rfl

theorem cell23_2800193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 4, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 4, 1, 1, 2, 1, 4].length) (baseStart_2800193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2800193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2800193 prefixEnd_2800193 := by exact prefixLift 2800193
  have htrace : WordTrace (prefixWord ++ tailWord_2800193) baseStart_2800193 baseEnd_2800193 := by
    simpa [prefixWord, tailWord_2800193, baseEnd_2800193] using wordTrace_append hprefix tailTrace_2800193
  have hstable : (prefixWord ++ tailWord_2800193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2800193).length < 2 ^ (prefixWord ++ tailWord_2800193).sum := by decide
  have hdescent : baseEnd_2800193 < baseStart_2800193 := by decide
  rcases family_descends (prefixWord ++ tailWord_2800193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2800236 : List Nat := [2, 2, 1, 1, 3, 1, 3, 2, 1, 5, 2]
def baseStart_2800236 : Nat := 118140960795 + 2800236 * 2 ^ 59
def prefixEnd_2800236 : Nat := 4983230072969 + 3 ^ 40 * 2800236 * 2
def baseEnd_2800236 : Nat := 1437867014023611297471955

theorem tailTrace_2800236 : CollatzResearch.WordTrace tailWord_2800236 prefixEnd_2800236 1437867014023611297471955 := by
  unfold tailWord_2800236
  simp only [CollatzResearch.WordTrace]
  refine ⟨51066498741615344539550281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68088664988820459386067041 51066498741615344539550281)
  ·
    refine ⟨38299874056211508404662711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51066498741615344539550281 38299874056211508404662711)
    ·
      refine ⟨57449811084317262606994067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38299874056211508404662711 57449811084317262606994067)
      ·
        refine ⟨86174716626475893910491101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57449811084317262606994067 86174716626475893910491101)
        ·
          refine ⟨32315518734928460216434163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 86174716626475893910491101 32315518734928460216434163)
          ·
            refine ⟨48473278102392690324651245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32315518734928460216434163 48473278102392690324651245)
            ·
              refine ⟨18177479288397258871744217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 48473278102392690324651245 18177479288397258871744217)
              ·
                refine ⟨13633109466297944153808163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18177479288397258871744217 13633109466297944153808163)
                ·
                  refine ⟨20449664199446916230712245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13633109466297944153808163 20449664199446916230712245)
                  ·
                    refine ⟨1917156018698148396629273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 20449664199446916230712245 1917156018698148396629273)
                    ·
                      refine ⟨1437867014023611297471955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1917156018698148396629273 1437867014023611297471955)
                      ·
                        rfl

theorem cell23_2800236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 5, 2].length) (baseStart_2800236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2800236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2800236 prefixEnd_2800236 := by exact prefixLift 2800236
  have htrace : WordTrace (prefixWord ++ tailWord_2800236) baseStart_2800236 baseEnd_2800236 := by
    simpa [prefixWord, tailWord_2800236, baseEnd_2800236] using wordTrace_append hprefix tailTrace_2800236
  have hstable : (prefixWord ++ tailWord_2800236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2800236).length < 2 ^ (prefixWord ++ tailWord_2800236).sum := by decide
  have hdescent : baseEnd_2800236 < baseStart_2800236 := by decide
  rcases family_descends (prefixWord ++ tailWord_2800236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2800259 : List Nat := [1, 1, 1, 3, 3, 1, 2, 4, 1, 6]
def baseStart_2800259 : Nat := 118140960795 + 2800259 * 2 ^ 59
def prefixEnd_2800259 : Nat := 4983230072969 + 3 ^ 40 * 2800259 * 2
def baseEnd_2800259 : Nat := 479292941359554902494783

theorem tailTrace_2800259 : CollatzResearch.WordTrace tailWord_2800259 prefixEnd_2800259 479292941359554902494783 := by
  unfold tailWord_2800259
  simp only [CollatzResearch.WordTrace]
  refine ⟨102133836362147364007187831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68089224241431576004791887 102133836362147364007187831)
  ·
    refine ⟨153200754543221046010781747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102133836362147364007187831 153200754543221046010781747)
    ·
      refine ⟨229801131814831569016172621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 153200754543221046010781747 229801131814831569016172621)
      ·
        refine ⟨86175424430561838381064733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 229801131814831569016172621 86175424430561838381064733)
        ·
          refine ⟨32315784161460689392899275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 86175424430561838381064733 32315784161460689392899275)
          ·
            refine ⟨48473676242191034089348913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32315784161460689392899275 48473676242191034089348913)
            ·
              refine ⟨36355257181643275567011685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48473676242191034089348913 36355257181643275567011685)
              ·
                refine ⟨6816610721558114168814691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 36355257181643275567011685 6816610721558114168814691)
                ·
                  refine ⟨10224916082337171253222037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6816610721558114168814691 10224916082337171253222037)
                  ·
                    refine ⟨479292941359554902494783, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10224916082337171253222037 479292941359554902494783)
                    ·
                      rfl

theorem cell23_2800259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 2, 4, 1, 6].length) (baseStart_2800259 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2800259 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2800259 prefixEnd_2800259 := by exact prefixLift 2800259
  have htrace : WordTrace (prefixWord ++ tailWord_2800259) baseStart_2800259 baseEnd_2800259 := by
    simpa [prefixWord, tailWord_2800259, baseEnd_2800259] using wordTrace_append hprefix tailTrace_2800259
  have hstable : (prefixWord ++ tailWord_2800259).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2800259).length < 2 ^ (prefixWord ++ tailWord_2800259).sum := by decide
  have hdescent : baseEnd_2800259 < baseStart_2800259 := by decide
  rcases family_descends (prefixWord ++ tailWord_2800259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2800279 : List Nat := [1, 1, 3, 3, 2, 1, 1, 1, 3, 1, 6]
def baseStart_2800279 : Nat := 118140960795 + 2800279 * 2 ^ 59
def prefixEnd_2800279 : Nat := 4983230072969 + 3 ^ 40 * 2800279 * 2
def baseEnd_2800279 : Nat := 1437889093691754629234257

theorem tailTrace_2800279 : CollatzResearch.WordTrace tailWord_2800279 prefixEnd_2800279 1437889093691754629234257 := by
  unfold tailWord_2800279
  simp only [CollatzResearch.WordTrace]
  refine ⟨102134565822074907422915891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68089710548049938281943927 102134565822074907422915891)
  ·
    refine ⟨153201848733112361134373837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102134565822074907422915891 153201848733112361134373837)
    ·
      refine ⟨57450693274917135425390189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 153201848733112361134373837 57450693274917135425390189)
      ·
        refine ⟨21544009978093925784521321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 57450693274917135425390189 21544009978093925784521321)
        ·
          refine ⟨16158007483570444338390991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21544009978093925784521321 16158007483570444338390991)
          ·
            refine ⟨24237011225355666507586487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16158007483570444338390991 24237011225355666507586487)
            ·
              refine ⟨36355516838033499761379731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24237011225355666507586487 36355516838033499761379731)
              ·
                refine ⟨54533275257050249642069597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36355516838033499761379731 54533275257050249642069597)
                ·
                  refine ⟨20449978221393843615776099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 54533275257050249642069597 20449978221393843615776099)
                  ·
                    refine ⟨30674967332090765423664149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20449978221393843615776099 30674967332090765423664149)
                    ·
                      refine ⟨1437889093691754629234257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 30674967332090765423664149 1437889093691754629234257)
                      ·
                        rfl

theorem cell23_2800279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 1, 1, 3, 1, 6].length) (baseStart_2800279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2800279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2800279 prefixEnd_2800279 := by exact prefixLift 2800279
  have htrace : WordTrace (prefixWord ++ tailWord_2800279) baseStart_2800279 baseEnd_2800279 := by
    simpa [prefixWord, tailWord_2800279, baseEnd_2800279] using wordTrace_append hprefix tailTrace_2800279
  have hstable : (prefixWord ++ tailWord_2800279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2800279).length < 2 ^ (prefixWord ++ tailWord_2800279).sum := by decide
  have hdescent : baseEnd_2800279 < baseStart_2800279 := by decide
  rcases family_descends (prefixWord ++ tailWord_2800279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2800303 : List Nat := [1, 1, 2, 1, 2, 5, 3, 2, 1, 2, 3]
def baseStart_2800303 : Nat := 118140960795 + 2800303 * 2 ^ 59
def prefixEnd_2800303 : Nat := 4983230072969 + 3 ^ 40 * 2800303 * 2
def baseEnd_2800303 : Nat := 1437901417227462535334147

theorem tailTrace_2800303 : CollatzResearch.WordTrace tailWord_2800303 prefixEnd_2800303 1437901417227462535334147 := by
  unfold tailWord_2800303
  simp only [CollatzResearch.WordTrace]
  refine ⟨102135441173987959521789563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68090294115991973014526375 102135441173987959521789563)
  ·
    refine ⟨153203161760981939282684345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102135441173987959521789563 153203161760981939282684345)
    ·
      refine ⟨114902371320736454462013259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 153203161760981939282684345 114902371320736454462013259)
      ·
        refine ⟨172353556981104681693019889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114902371320736454462013259 172353556981104681693019889)
        ·
          refine ⟨129265167735828511269764917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 172353556981104681693019889 129265167735828511269764917)
          ·
            refine ⟨12118609475233922931540461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 129265167735828511269764917 12118609475233922931540461)
            ·
              refine ⟨4544478553212721099327673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12118609475233922931540461 4544478553212721099327673)
              ·
                refine ⟨3408358914909540824495755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4544478553212721099327673 3408358914909540824495755)
                ·
                  refine ⟨5112538372364311236743633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3408358914909540824495755 5112538372364311236743633)
                  ·
                    refine ⟨3834403779273233427557725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5112538372364311236743633 3834403779273233427557725)
                    ·
                      refine ⟨1437901417227462535334147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3834403779273233427557725 1437901417227462535334147)
                      ·
                        rfl

theorem cell23_2800303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 3, 2, 1, 2, 3].length) (baseStart_2800303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2800303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2800303 prefixEnd_2800303 := by exact prefixLift 2800303
  have htrace : WordTrace (prefixWord ++ tailWord_2800303) baseStart_2800303 baseEnd_2800303 := by
    simpa [prefixWord, tailWord_2800303, baseEnd_2800303] using wordTrace_append hprefix tailTrace_2800303
  have hstable : (prefixWord ++ tailWord_2800303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2800303).length < 2 ^ (prefixWord ++ tailWord_2800303).sum := by decide
  have hdescent : baseEnd_2800303 < baseStart_2800303 := by decide
  rcases family_descends (prefixWord ++ tailWord_2800303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2800310 : List Nat := [5, 1, 3, 1, 2, 1, 1, 2, 1, 6]
def baseStart_2800310 : Nat := 118140960795 + 2800310 * 2 ^ 59
def prefixEnd_2800310 : Nat := 4983230072969 + 3 ^ 40 * 2800310 * 2
def baseEnd_2800310 : Nat := 479301670530681335982205

theorem tailTrace_2800310 : CollatzResearch.WordTrace tailWord_2800310 prefixEnd_2800310 479301670530681335982205 := by
  unfold tailWord_2800310
  simp only [CollatzResearch.WordTrace]
  refine ⟨6383481030310162482330899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 68090464323308399811529589 6383481030310162482330899)
  ·
    refine ⟨9575221545465243723496349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6383481030310162482330899 9575221545465243723496349)
    ·
      refine ⟨3590708079549466396311131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9575221545465243723496349 3590708079549466396311131)
      ·
        refine ⟨5386062119324199594466697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3590708079549466396311131 5386062119324199594466697)
        ·
          refine ⟨4039546589493149695850023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5386062119324199594466697 4039546589493149695850023)
          ·
            refine ⟨6059319884239724543775035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4039546589493149695850023 6059319884239724543775035)
            ·
              refine ⟨9088979826359586815662553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6059319884239724543775035 9088979826359586815662553)
              ·
                refine ⟨6816734869769690111746915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9088979826359586815662553 6816734869769690111746915)
                ·
                  refine ⟨10225102304654535167620373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6816734869769690111746915 10225102304654535167620373)
                  ·
                    refine ⟨479301670530681335982205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10225102304654535167620373 479301670530681335982205)
                    ·
                      rfl

theorem cell23_2800310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 1, 1, 2, 1, 6].length) (baseStart_2800310 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2800310 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2800310 prefixEnd_2800310 := by exact prefixLift 2800310
  have htrace : WordTrace (prefixWord ++ tailWord_2800310) baseStart_2800310 baseEnd_2800310 := by
    simpa [prefixWord, tailWord_2800310, baseEnd_2800310] using wordTrace_append hprefix tailTrace_2800310
  have hstable : (prefixWord ++ tailWord_2800310).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2800310).length < 2 ^ (prefixWord ++ tailWord_2800310).sum := by decide
  have hdescent : baseEnd_2800310 < baseStart_2800310 := by decide
  rcases family_descends (prefixWord ++ tailWord_2800310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2800320 : List Nat := [2, 1, 1, 2, 4, 3, 3, 1, 1, 2, 3]
def baseStart_2800320 : Nat := 118140960795 + 2800320 * 2 ^ 59
def prefixEnd_2800320 : Nat := 4983230072969 + 3 ^ 40 * 2800320 * 2
def baseEnd_2800320 : Nat := 1437910146398588968821569

theorem tailTrace_2800320 : CollatzResearch.WordTrace tailWord_2800320 prefixEnd_2800320 1437910146398588968821569 := by
  unfold tailWord_2800320
  simp only [CollatzResearch.WordTrace]
  refine ⟨51068030607463185712579207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68090707476617580950105609 51068030607463185712579207)
  ·
    refine ⟨76602045911194778568868811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51068030607463185712579207 76602045911194778568868811)
    ·
      refine ⟨114903068866792167853303217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76602045911194778568868811 114903068866792167853303217)
      ·
        refine ⟨86177301650094125889977413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 114903068866792167853303217 86177301650094125889977413)
        ·
          refine ⟨16158244059392648604370765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 86177301650094125889977413 16158244059392648604370765)
          ·
            refine ⟨6059341522272243226639037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16158244059392648604370765 6059341522272243226639037)
            ·
              refine ⟨2272253070852091209989639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6059341522272243226639037 2272253070852091209989639)
              ·
                refine ⟨3408379606278136814984459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2272253070852091209989639 3408379606278136814984459)
                ·
                  refine ⟨5112569409417205222476689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3408379606278136814984459 5112569409417205222476689)
                  ·
                    refine ⟨3834427057062903916857517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5112569409417205222476689 3834427057062903916857517)
                    ·
                      refine ⟨1437910146398588968821569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3834427057062903916857517 1437910146398588968821569)
                      ·
                        rfl

theorem cell23_2800320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 3, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 3, 3, 1, 1, 2, 3].length) (baseStart_2800320 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2800320 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2800320 prefixEnd_2800320 := by exact prefixLift 2800320
  have htrace : WordTrace (prefixWord ++ tailWord_2800320) baseStart_2800320 baseEnd_2800320 := by
    simpa [prefixWord, tailWord_2800320, baseEnd_2800320] using wordTrace_append hprefix tailTrace_2800320
  have hstable : (prefixWord ++ tailWord_2800320).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2800320).length < 2 ^ (prefixWord ++ tailWord_2800320).sum := by decide
  have hdescent : baseEnd_2800320 < baseStart_2800320 := by decide
  rcases family_descends (prefixWord ++ tailWord_2800320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2800334 : List Nat := [4, 1, 1, 1, 3, 2, 4, 2, 1, 2, 2]
def baseStart_2800334 : Nat := 118140960795 + 2800334 * 2 ^ 59
def prefixEnd_2800334 : Nat := 4983230072969 + 3 ^ 40 * 2800334 * 2
def baseEnd_2800334 : Nat := 1437917335127751914046505

theorem tailTrace_2800334 : CollatzResearch.WordTrace tailWord_2800334 prefixEnd_2800334 1437917335127751914046505 := by
  unfold tailWord_2800334
  simp only [CollatzResearch.WordTrace]
  refine ⟨12767071479609456477021007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 68091047891250434544112037 12767071479609456477021007)
  ·
    refine ⟨19150607219414184715531511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12767071479609456477021007 19150607219414184715531511)
    ·
      refine ⟨28725910829121277073297267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19150607219414184715531511 28725910829121277073297267)
      ·
        refine ⟨43088866243681915609945901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28725910829121277073297267 43088866243681915609945901)
        ·
          refine ⟨16158324841380718353729713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43088866243681915609945901 16158324841380718353729713)
          ·
            refine ⟨12118743631035538765297285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16158324841380718353729713 12118743631035538765297285)
            ·
              refine ⟨2272264430819163518493241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12118743631035538765297285 2272264430819163518493241)
              ·
                refine ⟨1704198323114372638869931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2272264430819163518493241 1704198323114372638869931)
                ·
                  refine ⟨2556297484671558958304897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1704198323114372638869931 2556297484671558958304897)
                  ·
                    refine ⟨1917223113503669218728673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2556297484671558958304897 1917223113503669218728673)
                    ·
                      refine ⟨1437917335127751914046505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1917223113503669218728673 1437917335127751914046505)
                      ·
                        rfl

theorem cell23_2800334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 4, 2, 1, 2, 2].length) (baseStart_2800334 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2800334 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2800334 prefixEnd_2800334 := by exact prefixLift 2800334
  have htrace : WordTrace (prefixWord ++ tailWord_2800334) baseStart_2800334 baseEnd_2800334 := by
    simpa [prefixWord, tailWord_2800334, baseEnd_2800334] using wordTrace_append hprefix tailTrace_2800334
  have hstable : (prefixWord ++ tailWord_2800334).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2800334).length < 2 ^ (prefixWord ++ tailWord_2800334).sum := by decide
  have hdescent : baseEnd_2800334 < baseStart_2800334 := by decide
  rcases family_descends (prefixWord ++ tailWord_2800334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2800340 : List Nat := [2, 4, 1, 3, 3, 1, 1, 8]
def baseStart_2800340 : Nat := 118140960795 + 2800340 * 2 ^ 59
def prefixEnd_2800340 : Nat := 4983230072969 + 3 ^ 40 * 2800340 * 2
def baseEnd_2800340 : Nat := 53256311704136255206351

theorem tailTrace_2800340 : CollatzResearch.WordTrace tailWord_2800340 prefixEnd_2800340 53256311704136255206351 := by
  unfold tailWord_2800340
  simp only [CollatzResearch.WordTrace]
  refine ⟨51068395337426957420443237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68091193783235943227257649 51068395337426957420443237)
  ·
    refine ⟨9575324125767554516333107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 51068395337426957420443237 9575324125767554516333107)
    ·
      refine ⟨14362986188651331774499661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9575324125767554516333107 14362986188651331774499661)
      ·
        refine ⟨5386119820744249415437373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14362986188651331774499661 5386119820744249415437373)
        ·
          refine ⟨2019794932779093530789015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5386119820744249415437373 2019794932779093530789015)
          ·
            refine ⟨3029692399168640296183523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2019794932779093530789015 3029692399168640296183523)
            ·
              refine ⟨4544538598752960444275285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3029692399168640296183523 4544538598752960444275285)
              ·
                refine ⟨53256311704136255206351, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4544538598752960444275285 53256311704136255206351)
                ·
                  rfl

theorem cell23_2800340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 3, 1, 1, 8].length) (baseStart_2800340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2800340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2800340 prefixEnd_2800340 := by exact prefixLift 2800340
  have htrace : WordTrace (prefixWord ++ tailWord_2800340) baseStart_2800340 baseEnd_2800340 := by
    simpa [prefixWord, tailWord_2800340, baseEnd_2800340] using wordTrace_append hprefix tailTrace_2800340
  have hstable : (prefixWord ++ tailWord_2800340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2800340).length < 2 ^ (prefixWord ++ tailWord_2800340).sum := by decide
  have hdescent : baseEnd_2800340 < baseStart_2800340 := by decide
  rcases family_descends (prefixWord ++ tailWord_2800340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2800343 : List Nat := [1, 1, 3, 2, 1, 4, 1, 2, 3, 3, 2]
def baseStart_2800343 : Nat := 118140960795 + 2800343 * 2 ^ 59
def prefixEnd_2800343 : Nat := 4983230072969 + 3 ^ 40 * 2800343 * 2
def baseEnd_2800343 : Nat := 1437921956453642378833963

theorem tailTrace_2800343 : CollatzResearch.WordTrace tailWord_2800343 prefixEnd_2800343 1437921956453642378833963 := by
  unfold tailWord_2800343
  simp only [CollatzResearch.WordTrace]
  refine ⟨102136900093843046353245683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68091266729228697568830455 102136900093843046353245683)
  ·
    refine ⟨153205350140764569529868525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102136900093843046353245683 153205350140764569529868525)
    ·
      refine ⟨57452006302786713573700697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 153205350140764569529868525 57452006302786713573700697)
      ·
        refine ⟨43089004727090035180275523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57452006302786713573700697 43089004727090035180275523)
        ·
          refine ⟨64633507090635052770413285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43089004727090035180275523 64633507090635052770413285)
          ·
            refine ⟨12118782579494072394452491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 64633507090635052770413285 12118782579494072394452491)
            ·
              refine ⟨18178173869241108591678737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12118782579494072394452491 18178173869241108591678737)
              ·
                refine ⟨13633630401930831443759053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18178173869241108591678737 13633630401930831443759053)
                ·
                  refine ⟨5112611400724061791409645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13633630401930831443759053 5112611400724061791409645)
                  ·
                    refine ⟨1917229275271523171778617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5112611400724061791409645 1917229275271523171778617)
                    ·
                      refine ⟨1437921956453642378833963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1917229275271523171778617 1437921956453642378833963)
                      ·
                        rfl

theorem cell23_2800343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 1, 2, 3, 3, 2].length) (baseStart_2800343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2800343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2800343 prefixEnd_2800343 := by exact prefixLift 2800343
  have htrace : WordTrace (prefixWord ++ tailWord_2800343) baseStart_2800343 baseEnd_2800343 := by
    simpa [prefixWord, tailWord_2800343, baseEnd_2800343] using wordTrace_append hprefix tailTrace_2800343
  have hstable : (prefixWord ++ tailWord_2800343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2800343).length < 2 ^ (prefixWord ++ tailWord_2800343).sum := by decide
  have hdescent : baseEnd_2800343 < baseStart_2800343 := by decide
  rcases family_descends (prefixWord ++ tailWord_2800343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2800407 : List Nat := [1, 1, 3, 4, 3, 2, 1, 1, 1, 4, 2]
def baseStart_2800407 : Nat := 118140960795 + 2800407 * 2 ^ 59
def prefixEnd_2800407 : Nat := 4983230072969 + 3 ^ 40 * 2800407 * 2
def baseEnd_2800407 : Nat := 1437954819215530128433669

theorem tailTrace_2800407 : CollatzResearch.WordTrace tailWord_2800407 prefixEnd_2800407 1437954819215530128433669 := by
  unfold tailWord_2800407
  simp only [CollatzResearch.WordTrace]
  refine ⟨102139234365611185283575475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68092822910407456855716983 102139234365611185283575475)
  ·
    refine ⟨153208851548416777925363213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102139234365611185283575475 153208851548416777925363213)
    ·
      refine ⟨57453319330656291722011205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 153208851548416777925363213 57453319330656291722011205)
      ·
        refine ⟨10772497374498054697877101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 57453319330656291722011205 10772497374498054697877101)
        ·
          refine ⟨4039686515436770511703913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10772497374498054697877101 4039686515436770511703913)
          ·
            refine ⟨3029764886577577883777935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4039686515436770511703913 3029764886577577883777935)
            ·
              refine ⟨4544647329866366825666903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3029764886577577883777935 4544647329866366825666903)
              ·
                refine ⟨6816970994799550238500355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4544647329866366825666903 6816970994799550238500355)
                ·
                  refine ⟨10225456492199325357750533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6816970994799550238500355 10225456492199325357750533)
                  ·
                    refine ⟨1917273092287373504578225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10225456492199325357750533 1917273092287373504578225)
                    ·
                      refine ⟨1437954819215530128433669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1917273092287373504578225 1437954819215530128433669)
                      ·
                        rfl

theorem cell23_2800407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 2, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 2, 1, 1, 1, 4, 2].length) (baseStart_2800407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2800407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2800407 prefixEnd_2800407 := by exact prefixLift 2800407
  have htrace : WordTrace (prefixWord ++ tailWord_2800407) baseStart_2800407 baseEnd_2800407 := by
    simpa [prefixWord, tailWord_2800407, baseEnd_2800407] using wordTrace_append hprefix tailTrace_2800407
  have hstable : (prefixWord ++ tailWord_2800407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2800407).length < 2 ^ (prefixWord ++ tailWord_2800407).sum := by decide
  have hdescent : baseEnd_2800407 < baseStart_2800407 := by decide
  rcases family_descends (prefixWord ++ tailWord_2800407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2800506 : List Nat := [3, 1, 1, 1, 1, 1, 3, 3, 1, 2, 6]
def baseStart_2800506 : Nat := 118140960795 + 2800506 * 2 ^ 59
def prefixEnd_2800506 : Nat := 4983230072969 + 3 ^ 40 * 2800506 * 2
def baseEnd_2800506 : Nat := 1438005653800325241095713

theorem tailTrace_2800506 : CollatzResearch.WordTrace tailWord_2800506 prefixEnd_2800506 1438005653800325241095713 := by
  unfold tailWord_2800506
  simp only [CollatzResearch.WordTrace]
  refine ⟨25535711298063131297857343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68095230128168350127619581 25535711298063131297857343)
  ·
    refine ⟨38303566947094696946786015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25535711298063131297857343 38303566947094696946786015)
    ·
      refine ⟨57455350420642045420179023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38303566947094696946786015 57455350420642045420179023)
      ·
        refine ⟨86183025630963068130268535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57455350420642045420179023 86183025630963068130268535)
        ·
          refine ⟨129274538446444602195402803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86183025630963068130268535 129274538446444602195402803)
          ·
            refine ⟨193911807669666903293104205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 129274538446444602195402803 193911807669666903293104205)
            ·
              refine ⟨72716927876125088734914077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 193911807669666903293104205 72716927876125088734914077)
              ·
                refine ⟨27268847953546908275592779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 72716927876125088734914077 27268847953546908275592779)
                ·
                  refine ⟨40903271930320362413389169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27268847953546908275592779 40903271930320362413389169)
                  ·
                    refine ⟨30677453947740271810041877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 40903271930320362413389169 30677453947740271810041877)
                    ·
                      refine ⟨1438005653800325241095713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 30677453947740271810041877 1438005653800325241095713)
                      ·
                        rfl

theorem cell23_2800506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 3, 1, 2, 6].length) (baseStart_2800506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2800506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2800506 prefixEnd_2800506 := by exact prefixLift 2800506
  have htrace : WordTrace (prefixWord ++ tailWord_2800506) baseStart_2800506 baseEnd_2800506 := by
    simpa [prefixWord, tailWord_2800506, baseEnd_2800506] using wordTrace_append hprefix tailTrace_2800506
  have hstable : (prefixWord ++ tailWord_2800506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2800506).length < 2 ^ (prefixWord ++ tailWord_2800506).sum := by decide
  have hdescent : baseEnd_2800506 < baseStart_2800506 := by decide
  rcases family_descends (prefixWord ++ tailWord_2800506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2800507 : List Nat := [1, 1, 1, 1, 1, 5, 6, 2, 1, 4]
def baseStart_2800507 : Nat := 118140960795 + 2800507 * 2 ^ 59
def prefixEnd_2800507 : Nat := 4983230072969 + 3 ^ 40 * 2800507 * 2
def baseEnd_2800507 : Nat := 479335389093659912394403

theorem tailTrace_2800507 : CollatzResearch.WordTrace tailWord_2800507 prefixEnd_2800507 479335389093659912394403 := by
  unfold tailWord_2800507
  simp only [CollatzResearch.WordTrace]
  refine ⟨102142881665248902362215775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68095254443499268241477183 102142881665248902362215775)
  ·
    refine ⟨153214322497873353543323663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102142881665248902362215775 153214322497873353543323663)
    ·
      refine ⟨229821483746810030314985495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 153214322497873353543323663 229821483746810030314985495)
      ·
        refine ⟨344732225620215045472478243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 229821483746810030314985495 344732225620215045472478243)
        ·
          refine ⟨517098338430322568208717365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 344732225620215045472478243 517098338430322568208717365)
          ·
            refine ⟨48477969227842740769567253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 517098338430322568208717365 48477969227842740769567253)
            ·
              refine ⟨2272404807555128473573465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 48477969227842740769567253 2272404807555128473573465)
              ·
                refine ⟨1704303605666346355180099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2272404807555128473573465 1704303605666346355180099)
                ·
                  refine ⟨2556455408499519532770149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1704303605666346355180099 2556455408499519532770149)
                  ·
                    refine ⟨479335389093659912394403, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2556455408499519532770149 479335389093659912394403)
                    ·
                      rfl

theorem cell23_2800507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 6, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 6, 2, 1, 4].length) (baseStart_2800507 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2800507 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2800507 prefixEnd_2800507 := by exact prefixLift 2800507
  have htrace : WordTrace (prefixWord ++ tailWord_2800507) baseStart_2800507 baseEnd_2800507 := by
    simpa [prefixWord, tailWord_2800507, baseEnd_2800507] using wordTrace_append hprefix tailTrace_2800507
  have hstable : (prefixWord ++ tailWord_2800507).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2800507).length < 2 ^ (prefixWord ++ tailWord_2800507).sum := by decide
  have hdescent : baseEnd_2800507 < baseStart_2800507 := by decide
  rcases family_descends (prefixWord ++ tailWord_2800507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2800533 : List Nat := [1, 3, 2, 1, 1, 4, 2, 1, 3, 5]
def baseStart_2800533 : Nat := 118140960795 + 2800533 * 2 ^ 59
def prefixEnd_2800533 : Nat := 4983230072969 + 3 ^ 40 * 2800533 * 2
def baseEnd_2800533 : Nat := 479339839259332211819363

theorem tailTrace_2800533 : CollatzResearch.WordTrace tailWord_2800533 prefixEnd_2800533 479339839259332211819363 := by
  unfold tailWord_2800533
  simp only [CollatzResearch.WordTrace]
  refine ⟨102143829963154708802662253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68095886642103139201774835 102143829963154708802662253)
  ·
    refine ⟨38303936236183015800998345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 102143829963154708802662253 38303936236183015800998345)
    ·
      refine ⟨28727952177137261850748759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38303936236183015800998345 28727952177137261850748759)
      ·
        refine ⟨43091928265705892776123139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28727952177137261850748759 43091928265705892776123139)
        ·
          refine ⟨64637892398558839164184709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43091928265705892776123139 64637892398558839164184709)
          ·
            refine ⟨12119604824729782343284633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 64637892398558839164184709 12119604824729782343284633)
            ·
              refine ⟨9089703618547336757463475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12119604824729782343284633 9089703618547336757463475)
              ·
                refine ⟨13634555427821005136195213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9089703618547336757463475 13634555427821005136195213)
                ·
                  refine ⟨5112958285432876926073205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13634555427821005136195213 5112958285432876926073205)
                  ·
                    refine ⟨479339839259332211819363, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5112958285432876926073205 479339839259332211819363)
                    ·
                      rfl

theorem cell23_2800533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 2, 1, 3, 5].length) (baseStart_2800533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2800533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2800533 prefixEnd_2800533 := by exact prefixLift 2800533
  have htrace : WordTrace (prefixWord ++ tailWord_2800533) baseStart_2800533 baseEnd_2800533 := by
    simpa [prefixWord, tailWord_2800533, baseEnd_2800533] using wordTrace_append hprefix tailTrace_2800533
  have hstable : (prefixWord ++ tailWord_2800533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2800533).length < 2 ^ (prefixWord ++ tailWord_2800533).sum := by decide
  have hdescent : baseEnd_2800533 < baseStart_2800533 := by decide
  rcases family_descends (prefixWord ++ tailWord_2800533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2800534 : List Nat := [5, 3, 1, 1, 1, 2, 1, 1, 1, 4, 3]
def baseStart_2800534 : Nat := 118140960795 + 2800534 * 2 ^ 59
def prefixEnd_2800534 : Nat := 4983230072969 + 3 ^ 40 * 2800534 * 2
def baseEnd_2800534 : Nat := 1438020031258651131545585

theorem tailTrace_2800534 : CollatzResearch.WordTrace tailWord_2800534 prefixEnd_2800534 1438020031258651131545585 := by
  unfold tailWord_2800534
  simp only [CollatzResearch.WordTrace]
  refine ⟨6383991652259442873340541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 68095910957434057315632437 6383991652259442873340541)
  ·
    refine ⟨2393996869597291077502703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6383991652259442873340541 2393996869597291077502703)
    ·
      refine ⟨3590995304395936616254055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2393996869597291077502703 3590995304395936616254055)
      ·
        refine ⟨5386492956593904924381083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3590995304395936616254055 5386492956593904924381083)
        ·
          refine ⟨8079739434890857386571625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5386492956593904924381083 8079739434890857386571625)
          ·
            refine ⟨6059804576168143039928719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8079739434890857386571625 6059804576168143039928719)
            ·
              refine ⟨9089706864252214559893079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6059804576168143039928719 9089706864252214559893079)
              ·
                refine ⟨13634560296378321839839619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9089706864252214559893079 13634560296378321839839619)
                ·
                  refine ⟨20451840444567482759759429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13634560296378321839839619 20451840444567482759759429)
                  ·
                    refine ⟨3834720083356403017454893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20451840444567482759759429 3834720083356403017454893)
                    ·
                      refine ⟨1438020031258651131545585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3834720083356403017454893 1438020031258651131545585)
                      ·
                        rfl

theorem cell23_2800534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 2, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 2, 1, 1, 1, 4, 3].length) (baseStart_2800534 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2800534 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2800534 prefixEnd_2800534 := by exact prefixLift 2800534
  have htrace : WordTrace (prefixWord ++ tailWord_2800534) baseStart_2800534 baseEnd_2800534 := by
    simpa [prefixWord, tailWord_2800534, baseEnd_2800534] using wordTrace_append hprefix tailTrace_2800534
  have hstable : (prefixWord ++ tailWord_2800534).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2800534).length < 2 ^ (prefixWord ++ tailWord_2800534).sum := by decide
  have hdescent : baseEnd_2800534 < baseStart_2800534 := by decide
  rcases family_descends (prefixWord ++ tailWord_2800534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2800547 : List Nat := [1, 1, 1, 4, 1, 2, 3, 5, 1, 1, 3]
def baseStart_2800547 : Nat := 118140960795 + 2800547 * 2 ^ 59
def prefixEnd_2800547 : Nat := 4983230072969 + 3 ^ 40 * 2800547 * 2
def baseEnd_2800547 : Nat := 1438026706507159580683025

theorem tailTrace_2800547 : CollatzResearch.WordTrace tailWord_2800547 prefixEnd_2800547 1438026706507159580683025 := by
  unfold tailWord_2800547
  simp only [CollatzResearch.WordTrace]
  refine ⟨102144340585103989193671895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68096227056735992795781263 102144340585103989193671895)
  ·
    refine ⟨153216510877655983790507843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102144340585103989193671895 153216510877655983790507843)
    ·
      refine ⟨229824766316483975685761765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 153216510877655983790507843 229824766316483975685761765)
      ·
        refine ⟨43092143684340745441080331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 229824766316483975685761765 43092143684340745441080331)
        ·
          refine ⟨64638215526511118161620497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43092143684340745441080331 64638215526511118161620497)
          ·
            refine ⟨48478661644883338621215373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64638215526511118161620497 48478661644883338621215373)
            ·
              refine ⟨18179498116831251982955765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 48478661644883338621215373 18179498116831251982955765)
              ·
                refine ⟨1704327948452929873402103, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 18179498116831251982955765 1704327948452929873402103)
                ·
                  refine ⟨2556491922679394810103155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1704327948452929873402103 2556491922679394810103155)
                  ·
                    refine ⟨3834737884019092215154733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2556491922679394810103155 3834737884019092215154733)
                    ·
                      refine ⟨1438026706507159580683025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3834737884019092215154733 1438026706507159580683025)
                      ·
                        rfl

theorem cell23_2800547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 3, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 3, 5, 1, 1, 3].length) (baseStart_2800547 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2800547 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2800547 prefixEnd_2800547 := by exact prefixLift 2800547
  have htrace : WordTrace (prefixWord ++ tailWord_2800547) baseStart_2800547 baseEnd_2800547 := by
    simpa [prefixWord, tailWord_2800547, baseEnd_2800547] using wordTrace_append hprefix tailTrace_2800547
  have hstable : (prefixWord ++ tailWord_2800547).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2800547).length < 2 ^ (prefixWord ++ tailWord_2800547).sum := by decide
  have hdescent : baseEnd_2800547 < baseStart_2800547 := by decide
  rcases family_descends (prefixWord ++ tailWord_2800547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2800564 : List Nat := [2, 5, 2, 1, 1, 1, 1, 3, 3, 1, 3]
def baseStart_2800564 : Nat := 118140960795 + 2800564 * 2 ^ 59
def prefixEnd_2800564 : Nat := 4983230072969 + 3 ^ 40 * 2800564 * 2
def baseEnd_2800564 : Nat := 1438035435678286014170447

theorem tailTrace_2800564 : CollatzResearch.WordTrace tailWord_2800564 prefixEnd_2800564 1438035435678286014170447 := by
  unfold tailWord_2800564
  simp only [CollatzResearch.WordTrace]
  refine ⟨51072480313021200548520373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68096640417361600731360497 51072480313021200548520373)
  ·
    refine ⟨4788045029345737551423785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 51072480313021200548520373 4788045029345737551423785)
    ·
      refine ⟨3591033772009303163567839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4788045029345737551423785 3591033772009303163567839)
      ·
        refine ⟨5386550658013954745351759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3591033772009303163567839 5386550658013954745351759)
        ·
          refine ⟨8079825987020932118027639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5386550658013954745351759 8079825987020932118027639)
          ·
            refine ⟨12119738980531398177041459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8079825987020932118027639 12119738980531398177041459)
            ·
              refine ⟨18179608470797097265562189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12119738980531398177041459 18179608470797097265562189)
              ·
                refine ⟨6817353176548911474585821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18179608470797097265562189 6817353176548911474585821)
                ·
                  refine ⟨2556507441205841802969683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6817353176548911474585821 2556507441205841802969683)
                  ·
                    refine ⟨3834761161808762704454525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2556507441205841802969683 3834761161808762704454525)
                    ·
                      refine ⟨1438035435678286014170447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3834761161808762704454525 1438035435678286014170447)
                      ·
                        rfl

theorem cell23_2800564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 1, 3, 3, 1, 3].length) (baseStart_2800564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2800564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2800564 prefixEnd_2800564 := by exact prefixLift 2800564
  have htrace : WordTrace (prefixWord ++ tailWord_2800564) baseStart_2800564 baseEnd_2800564 := by
    simpa [prefixWord, tailWord_2800564, baseEnd_2800564] using wordTrace_append hprefix tailTrace_2800564
  have hstable : (prefixWord ++ tailWord_2800564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2800564).length < 2 ^ (prefixWord ++ tailWord_2800564).sum := by decide
  have hdescent : baseEnd_2800564 < baseStart_2800564 := by decide
  rcases family_descends (prefixWord ++ tailWord_2800564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2800587 : List Nat := [1, 1, 1, 1, 3, 5, 2, 2, 3, 2, 2]
def baseStart_2800587 : Nat := 118140960795 + 2800587 * 2 ^ 59
def prefixEnd_2800587 : Nat := 4983230072969 + 3 ^ 40 * 2800587 * 2
def baseEnd_2800587 : Nat := 1438047245733339424182841

theorem tailTrace_2800587 : CollatzResearch.WordTrace tailWord_2800587 prefixEnd_2800587 1438047245733339424182841 := by
  unfold tailWord_2800587
  simp only [CollatzResearch.WordTrace]
  refine ⟨102145799504959076025128015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68097199669972717350085343 102145799504959076025128015)
  ·
    refine ⟨153218699257438614037692023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102145799504959076025128015 153218699257438614037692023)
    ·
      refine ⟨229828048886157921056538035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 153218699257438614037692023 229828048886157921056538035)
      ·
        refine ⟨344742073329236881584807053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 229828048886157921056538035 344742073329236881584807053)
        ·
          refine ⟨129278277498463830594302645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 344742073329236881584807053 129278277498463830594302645)
          ·
            refine ⟨12119838515480984118215873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 129278277498463830594302645 12119838515480984118215873)
            ·
              refine ⟨9089878886610738088661905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12119838515480984118215873 9089878886610738088661905)
              ·
                refine ⟨6817409164958053566496429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9089878886610738088661905 6817409164958053566496429)
                ·
                  refine ⟨2556528436859270087436161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6817409164958053566496429 2556528436859270087436161)
                  ·
                    refine ⟨1917396327644452565577121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2556528436859270087436161 1917396327644452565577121)
                    ·
                      refine ⟨1438047245733339424182841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1917396327644452565577121 1438047245733339424182841)
                      ·
                        rfl

theorem cell23_2800587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 2, 2, 3, 2, 2].length) (baseStart_2800587 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2800587 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2800587 prefixEnd_2800587 := by exact prefixLift 2800587
  have htrace : WordTrace (prefixWord ++ tailWord_2800587) baseStart_2800587 baseEnd_2800587 := by
    simpa [prefixWord, tailWord_2800587, baseEnd_2800587] using wordTrace_append hprefix tailTrace_2800587
  have hstable : (prefixWord ++ tailWord_2800587).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2800587).length < 2 ^ (prefixWord ++ tailWord_2800587).sum := by decide
  have hdescent : baseEnd_2800587 < baseStart_2800587 := by decide
  rcases family_descends (prefixWord ++ tailWord_2800587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2800598 : List Nat := [5, 2, 1, 1, 2, 3, 1, 3, 1, 1, 3]
def baseStart_2800598 : Nat := 118140960795 + 2800598 * 2 ^ 59
def prefixEnd_2800598 : Nat := 4983230072969 + 3 ^ 40 * 2800598 * 2
def baseEnd_2800598 : Nat := 1438052894020538881145291

theorem tailTrace_2800598 : CollatzResearch.WordTrace tailWord_2800598 prefixEnd_2800598 1438052894020538881145291 := by
  unfold tailWord_2800598
  simp only [CollatzResearch.WordTrace]
  refine ⟨6384137544244951556486153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 68097467138612816602518965 6384137544244951556486153)
  ·
    refine ⟨4788103158183713667364615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6384137544244951556486153 4788103158183713667364615)
    ·
      refine ⟨7182154737275570501046923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4788103158183713667364615 7182154737275570501046923)
      ·
        refine ⟨10773232105913355751570385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7182154737275570501046923 10773232105913355751570385)
        ·
          refine ⟨8079924079435016813677789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10773232105913355751570385 8079924079435016813677789)
          ·
            refine ⟨3029971529788131305129171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8079924079435016813677789 3029971529788131305129171)
            ·
              refine ⟨4544957294682196957693757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3029971529788131305129171 4544957294682196957693757)
              ·
                refine ⟨1704358985505823859135159, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4544957294682196957693757 1704358985505823859135159)
                ·
                  refine ⟨2556538478258735788702739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1704358985505823859135159 2556538478258735788702739)
                  ·
                    refine ⟨3834807717388103683054109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2556538478258735788702739 3834807717388103683054109)
                    ·
                      refine ⟨1438052894020538881145291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3834807717388103683054109 1438052894020538881145291)
                      ·
                        rfl

theorem cell23_2800598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 3, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 3, 1, 3, 1, 1, 3].length) (baseStart_2800598 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2800598 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2800598 prefixEnd_2800598 := by exact prefixLift 2800598
  have htrace : WordTrace (prefixWord ++ tailWord_2800598) baseStart_2800598 baseEnd_2800598 := by
    simpa [prefixWord, tailWord_2800598, baseEnd_2800598] using wordTrace_append hprefix tailTrace_2800598
  have hstable : (prefixWord ++ tailWord_2800598).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2800598).length < 2 ^ (prefixWord ++ tailWord_2800598).sum := by decide
  have hdescent : baseEnd_2800598 < baseStart_2800598 := by decide
  rcases family_descends (prefixWord ++ tailWord_2800598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2800610 : List Nat := [3, 3, 3, 1, 1, 1, 11]
def baseStart_2800610 : Nat := 118140960795 + 2800610 * 2 ^ 59
def prefixEnd_2800610 : Nat := 4983230072969 + 3 ^ 40 * 2800610 * 2
def baseEnd_2800610 : Nat := 17753815503560405360435

theorem tailTrace_2800610 : CollatzResearch.WordTrace tailWord_2800610 prefixEnd_2800610 17753815503560405360435 := by
  unfold tailWord_2800610
  simp only [CollatzResearch.WordTrace]
  refine ⟨25536659595968937738303821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68097758922583833968810189 25536659595968937738303821)
  ·
    refine ⟨9576247348488351651863933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25536659595968937738303821 9576247348488351651863933)
    ·
      refine ⟨3591092755683131869448975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9576247348488351651863933 3591092755683131869448975)
      ·
        refine ⟨5386639133524697804173463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3591092755683131869448975 5386639133524697804173463)
        ·
          refine ⟨8079958700287046706260195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5386639133524697804173463 8079958700287046706260195)
          ·
            refine ⟨12119938050430570059390293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8079958700287046706260195 12119938050430570059390293)
            ·
              refine ⟨17753815503560405360435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 12119938050430570059390293 17753815503560405360435)
              ·
                rfl

theorem cell23_2800610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 11].length) (baseStart_2800610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2800610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2800610 prefixEnd_2800610 := by exact prefixLift 2800610
  have htrace : WordTrace (prefixWord ++ tailWord_2800610) baseStart_2800610 baseEnd_2800610 := by
    simpa [prefixWord, tailWord_2800610, baseEnd_2800610] using wordTrace_append hprefix tailTrace_2800610
  have hstable : (prefixWord ++ tailWord_2800610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2800610).length < 2 ^ (prefixWord ++ tailWord_2800610).sum := by decide
  have hdescent : baseEnd_2800610 < baseStart_2800610 := by decide
  rcases family_descends (prefixWord ++ tailWord_2800610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2800647 : List Nat := [1, 1, 4, 3, 1, 1, 3, 1, 3, 3, 2]
def baseStart_2800647 : Nat := 118140960795 + 2800647 * 2 ^ 59
def prefixEnd_2800647 : Nat := 4983230072969 + 3 ^ 40 * 2800647 * 2
def baseEnd_2800647 : Nat := 1438078054572609189432565

theorem tailTrace_2800647 : CollatzResearch.WordTrace tailWord_2800647 prefixEnd_2800647 1438078054572609189432565 := by
  unfold tailWord_2800647
  simp only [CollatzResearch.WordTrace]
  refine ⟨102147987884741706272312195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68098658589827804181541463 102147987884741706272312195)
  ·
    refine ⟨153221981827112559408468293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102147987884741706272312195 153221981827112559408468293)
    ·
      refine ⟨28729121592583604889087805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 153221981827112559408468293 28729121592583604889087805)
      ·
        refine ⟨10773420597218851833407927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28729121592583604889087805 10773420597218851833407927)
        ·
          refine ⟨16160130895828277750111891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10773420597218851833407927 16160130895828277750111891)
          ·
            refine ⟨24240196343742416625167837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16160130895828277750111891 24240196343742416625167837)
            ·
              refine ⟨9090073628903406234437939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24240196343742416625167837 9090073628903406234437939)
              ·
                refine ⟨13635110443355109351656909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9090073628903406234437939 13635110443355109351656909)
                ·
                  refine ⟨5113166416258166006871341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13635110443355109351656909 5113166416258166006871341)
                  ·
                    refine ⟨1917437406096812252576753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5113166416258166006871341 1917437406096812252576753)
                    ·
                      refine ⟨1438078054572609189432565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1917437406096812252576753 1438078054572609189432565)
                      ·
                        rfl

theorem cell23_2800647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 3, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 3, 1, 3, 3, 2].length) (baseStart_2800647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2800647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2800647 prefixEnd_2800647 := by exact prefixLift 2800647
  have htrace : WordTrace (prefixWord ++ tailWord_2800647) baseStart_2800647 baseEnd_2800647 := by
    simpa [prefixWord, tailWord_2800647, baseEnd_2800647] using wordTrace_append hprefix tailTrace_2800647
  have hstable : (prefixWord ++ tailWord_2800647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2800647).length < 2 ^ (prefixWord ++ tailWord_2800647).sum := by decide
  have hdescent : baseEnd_2800647 < baseStart_2800647 := by decide
  rcases family_descends (prefixWord ++ tailWord_2800647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2800658 : List Nat := [3, 2, 5, 1, 2, 1, 1, 1, 1, 1, 5]
def baseStart_2800658 : Nat := 118140960795 + 2800658 * 2 ^ 59
def prefixEnd_2800658 : Nat := 4983230072969 + 3 ^ 40 * 2800658 * 2
def baseEnd_2800658 : Nat := 1438083702859808646395015

theorem tailTrace_2800658 : CollatzResearch.WordTrace tailWord_2800658 prefixEnd_2800658 1438083702859808646395015 := by
  unfold tailWord_2800658
  simp only [CollatzResearch.WordTrace]
  refine ⟨25537097271925463787740657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68098926058467903433975085 25537097271925463787740657)
  ·
    refine ⟨19152822953944097840805493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25537097271925463787740657 19152822953944097840805493)
    ·
      refine ⟨1795577151932259172575515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 19152822953944097840805493 1795577151932259172575515)
      ·
        refine ⟨2693365727898388758863273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1795577151932259172575515 2693365727898388758863273)
        ·
          refine ⟨2020024295923791569147455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2693365727898388758863273 2020024295923791569147455)
          ·
            refine ⟨3030036443885687353721183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2020024295923791569147455 3030036443885687353721183)
            ·
              refine ⟨4545054665828531030581775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3030036443885687353721183 4545054665828531030581775)
              ·
                refine ⟨6817581998742796545872663, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4545054665828531030581775 6817581998742796545872663)
                ·
                  refine ⟨10226372998114194818808995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6817581998742796545872663 10226372998114194818808995)
                  ·
                    refine ⟨15339559497171292228213493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10226372998114194818808995 15339559497171292228213493)
                    ·
                      refine ⟨1438083702859808646395015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15339559497171292228213493 1438083702859808646395015)
                      ·
                        rfl

theorem cell23_2800658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 2, 1, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 2, 1, 1, 1, 1, 1, 5].length) (baseStart_2800658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2800658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2800658 prefixEnd_2800658 := by exact prefixLift 2800658
  have htrace : WordTrace (prefixWord ++ tailWord_2800658) baseStart_2800658 baseEnd_2800658 := by
    simpa [prefixWord, tailWord_2800658, baseEnd_2800658] using wordTrace_append hprefix tailTrace_2800658
  have hstable : (prefixWord ++ tailWord_2800658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2800658).length < 2 ^ (prefixWord ++ tailWord_2800658).sum := by decide
  have hdescent : baseEnd_2800658 < baseStart_2800658 := by decide
  rcases family_descends (prefixWord ++ tailWord_2800658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2800672 : List Nat := [2, 1, 1, 7, 2, 1, 2, 2, 1, 2, 2]
def baseStart_2800672 : Nat := 118140960795 + 2800672 * 2 ^ 59
def prefixEnd_2800672 : Nat := 4983230072969 + 3 ^ 40 * 2800672 * 2
def baseEnd_2800672 : Nat := 1438090891588971591619951

theorem tailTrace_2800672 : CollatzResearch.WordTrace tailWord_2800672 prefixEnd_2800672 1438090891588971591619951 := by
  unfold tailWord_2800672
  simp only [CollatzResearch.WordTrace]
  refine ⟨51074449854825567770986135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68099266473100757027981513 51074449854825567770986135)
  ·
    refine ⟨76611674782238351656479203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51074449854825567770986135 76611674782238351656479203)
    ·
      refine ⟨114917512173357527484718805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76611674782238351656479203 114917512173357527484718805)
      ·
        refine ⟨2693379191563067050423097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 114917512173357527484718805 2693379191563067050423097)
        ·
          refine ⟨2020034393672300287817323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2693379191563067050423097 2020034393672300287817323)
          ·
            refine ⟨3030051590508450431725985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2020034393672300287817323 3030051590508450431725985)
            ·
              refine ⟨2272538692881337823794489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3030051590508450431725985 2272538692881337823794489)
              ·
                refine ⟨1704404019661003367845867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2272538692881337823794489 1704404019661003367845867)
                ·
                  refine ⟨2556606029491505051768801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1704404019661003367845867 2556606029491505051768801)
                  ·
                    refine ⟨1917454522118628788826601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2556606029491505051768801 1917454522118628788826601)
                    ·
                      refine ⟨1438090891588971591619951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1917454522118628788826601 1438090891588971591619951)
                      ·
                        rfl

theorem cell23_2800672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 2, 1, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 2, 1, 2, 2, 1, 2, 2].length) (baseStart_2800672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2800672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2800672 prefixEnd_2800672 := by exact prefixLift 2800672
  have htrace : WordTrace (prefixWord ++ tailWord_2800672) baseStart_2800672 baseEnd_2800672 := by
    simpa [prefixWord, tailWord_2800672, baseEnd_2800672] using wordTrace_append hprefix tailTrace_2800672
  have hstable : (prefixWord ++ tailWord_2800672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2800672).length < 2 ^ (prefixWord ++ tailWord_2800672).sum := by decide
  have hdescent : baseEnd_2800672 < baseStart_2800672 := by decide
  rcases family_descends (prefixWord ++ tailWord_2800672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2800683 : List Nat := [1, 1, 1, 1, 2, 1, 6, 3, 7]
def baseStart_2800683 : Nat := 118140960795 + 2800683 * 2 ^ 59
def prefixEnd_2800683 : Nat := 4983230072969 + 3 ^ 40 * 2800683 * 2
def baseEnd_2800683 : Nat := 159788504430685672064711

theorem tailTrace_2800683 : CollatzResearch.WordTrace tailWord_2800683 prefixEnd_2800683 159788504430685672064711 := by
  unfold tailWord_2800683
  simp only [CollatzResearch.WordTrace]
  refine ⟨102149300912611284420622703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68099533941740856280415135 102149300912611284420622703)
  ·
    refine ⟨153223951368916926630934055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102149300912611284420622703 153223951368916926630934055)
    ·
      refine ⟨229835927053375389946401083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 153223951368916926630934055 229835927053375389946401083)
      ·
        refine ⟨344753890580063084919601625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 229835927053375389946401083 344753890580063084919601625)
        ·
          refine ⟨258565417935047313689701219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 344753890580063084919601625 258565417935047313689701219)
          ·
            refine ⟨387848126902570970534551829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 258565417935047313689701219 387848126902570970534551829)
            ·
              refine ⟨18180380948558014243807117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 387848126902570970534551829 18180380948558014243807117)
              ·
                refine ⟨6817642855709255341427669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18180380948558014243807117 6817642855709255341427669)
                ·
                  refine ⟨159788504430685672064711, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6817642855709255341427669 159788504430685672064711)
                  ·
                    rfl

theorem cell23_2800683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 6, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 6, 3, 7].length) (baseStart_2800683 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2800683 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2800683 prefixEnd_2800683 := by exact prefixLift 2800683
  have htrace : WordTrace (prefixWord ++ tailWord_2800683) baseStart_2800683 baseEnd_2800683 := by
    simpa [prefixWord, tailWord_2800683, baseEnd_2800683] using wordTrace_append hprefix tailTrace_2800683
  have hstable : (prefixWord ++ tailWord_2800683).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2800683).length < 2 ^ (prefixWord ++ tailWord_2800683).sum := by decide
  have hdescent : baseEnd_2800683 < baseStart_2800683 := by decide
  rcases family_descends (prefixWord ++ tailWord_2800683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2800690 : List Nat := [3, 2, 1, 1, 2, 2, 3, 1, 2, 2, 4]
def baseStart_2800690 : Nat := 118140960795 + 2800690 * 2 ^ 59
def prefixEnd_2800690 : Nat := 4983230072969 + 3 ^ 40 * 2800690 * 2
def baseEnd_2800690 : Nat := 1438100134240752521194867

theorem tailTrace_2800690 : CollatzResearch.WordTrace tailWord_2800690 prefixEnd_2800690 1438100134240752521194867 := by
  unfold tailWord_2800690
  simp only [CollatzResearch.WordTrace]
  refine ⟨25537389055896481154031881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68099704149057283077418349 25537389055896481154031881)
  ·
    refine ⟨19153041791922360865523911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25537389055896481154031881 19153041791922360865523911)
    ·
      refine ⟨28729562687883541298285867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19153041791922360865523911 28729562687883541298285867)
      ·
        refine ⟨43094344031825311947428801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28729562687883541298285867 43094344031825311947428801)
        ·
          refine ⟨32320758023868983960571601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43094344031825311947428801 32320758023868983960571601)
          ·
            refine ⟨24240568517901737970428701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32320758023868983960571601 24240568517901737970428701)
            ·
              refine ⟨9090213194213151738910763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24240568517901737970428701 9090213194213151738910763)
              ·
                refine ⟨13635319791319727608366145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9090213194213151738910763 13635319791319727608366145)
                ·
                  refine ⟨10226489843489795706274609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13635319791319727608366145 10226489843489795706274609)
                  ·
                    refine ⟨7669867382617346779705957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10226489843489795706274609 7669867382617346779705957)
                    ·
                      refine ⟨1438100134240752521194867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7669867382617346779705957 1438100134240752521194867)
                      ·
                        rfl

theorem cell23_2800690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 3, 1, 2, 2, 4].length) (baseStart_2800690 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2800690 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2800690 prefixEnd_2800690 := by exact prefixLift 2800690
  have htrace : WordTrace (prefixWord ++ tailWord_2800690) baseStart_2800690 baseEnd_2800690 := by
    simpa [prefixWord, tailWord_2800690, baseEnd_2800690] using wordTrace_append hprefix tailTrace_2800690
  have hstable : (prefixWord ++ tailWord_2800690).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2800690).length < 2 ^ (prefixWord ++ tailWord_2800690).sum := by decide
  have hdescent : baseEnd_2800690 < baseStart_2800690 := by decide
  rcases family_descends (prefixWord ++ tailWord_2800690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2800694 : List Nat := [5, 1, 2, 1, 1, 2, 1, 3, 1, 4, 2]
def baseStart_2800694 : Nat := 118140960795 + 2800694 * 2 ^ 59
def prefixEnd_2800694 : Nat := 4983230072969 + 3 ^ 40 * 2800694 * 2
def baseEnd_2800694 : Nat := 1438102188163370505544849

theorem tailTrace_2800694 : CollatzResearch.WordTrace tailWord_2800694 prefixEnd_2800694 1438102188163370505544849 := by
  unfold tailWord_2800694
  simp only [CollatzResearch.WordTrace]
  refine ⟨6384356382223214581204571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 68099801410380955532848757 6384356382223214581204571)
  ·
    refine ⟨9576534573334821871806857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6384356382223214581204571 9576534573334821871806857)
    ·
      refine ⟨7182400930001116403855143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9576534573334821871806857 7182400930001116403855143)
      ·
        refine ⟨10773601395001674605782715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7182400930001116403855143 10773601395001674605782715)
        ·
          refine ⟨16160402092502511908674073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10773601395001674605782715 16160402092502511908674073)
          ·
            refine ⟨12120301569376883931505555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16160402092502511908674073 12120301569376883931505555)
            ·
              refine ⟨18180452354065325897258333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12120301569376883931505555 18180452354065325897258333)
              ·
                refine ⟨6817669632774497211471875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18180452354065325897258333 6817669632774497211471875)
                ·
                  refine ⟨10226504449161745817207813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6817669632774497211471875 10226504449161745817207813)
                  ·
                    refine ⟨1917469584217827340726465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10226504449161745817207813 1917469584217827340726465)
                    ·
                      refine ⟨1438102188163370505544849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1917469584217827340726465 1438102188163370505544849)
                      ·
                        rfl

theorem cell23_2800694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 1, 3, 1, 4, 2].length) (baseStart_2800694 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2800694 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2800694 prefixEnd_2800694 := by exact prefixLift 2800694
  have htrace : WordTrace (prefixWord ++ tailWord_2800694) baseStart_2800694 baseEnd_2800694 := by
    simpa [prefixWord, tailWord_2800694, baseEnd_2800694] using wordTrace_append hprefix tailTrace_2800694
  have hstable : (prefixWord ++ tailWord_2800694).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2800694).length < 2 ^ (prefixWord ++ tailWord_2800694).sum := by decide
  have hdescent : baseEnd_2800694 < baseStart_2800694 := by decide
  rcases family_descends (prefixWord ++ tailWord_2800694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2800700 : List Nat := [2, 2, 2, 2, 2, 3, 1, 2, 7]
def baseStart_2800700 : Nat := 118140960795 + 2800700 * 2 ^ 59
def prefixEnd_2800700 : Nat := 4983230072969 + 3 ^ 40 * 2800700 * 2
def baseEnd_2800700 : Nat := 159789474338588609118869

theorem tailTrace_2800700 : CollatzResearch.WordTrace tailWord_2800700 prefixEnd_2800700 159789474338588609118869 := by
  unfold tailWord_2800700
  simp only [CollatzResearch.WordTrace]
  refine ⟨51074960476774848161995777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68099947302366464215994369 51074960476774848161995777)
  ·
    refine ⟨38306220357581136121496833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51074960476774848161995777 38306220357581136121496833)
    ·
      refine ⟨28729665268185852091122625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38306220357581136121496833 28729665268185852091122625)
      ·
        refine ⟨21547248951139389068341969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28729665268185852091122625 21547248951139389068341969)
        ·
          refine ⟨16160436713354541801256477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21547248951139389068341969 16160436713354541801256477)
          ·
            refine ⟨6060163767507953175471179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16160436713354541801256477 6060163767507953175471179)
            ·
              refine ⟨9090245651261929763206769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6060163767507953175471179 9090245651261929763206769)
              ·
                refine ⟨6817684238446447322405077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9090245651261929763206769 6817684238446447322405077)
                ·
                  refine ⟨159789474338588609118869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6817684238446447322405077 159789474338588609118869)
                  ·
                    rfl

theorem cell23_2800700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 3, 1, 2, 7].length) (baseStart_2800700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2800700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2800700 prefixEnd_2800700 := by exact prefixLift 2800700
  have htrace : WordTrace (prefixWord ++ tailWord_2800700) baseStart_2800700 baseEnd_2800700 := by
    simpa [prefixWord, tailWord_2800700, baseEnd_2800700] using wordTrace_append hprefix tailTrace_2800700
  have hstable : (prefixWord ++ tailWord_2800700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2800700).length < 2 ^ (prefixWord ++ tailWord_2800700).sum := by decide
  have hdescent : baseEnd_2800700 < baseStart_2800700 := by decide
  rcases family_descends (prefixWord ++ tailWord_2800700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2800734 : List Nat := [4, 4, 1, 1, 1, 1, 1, 3, 7]
def baseStart_2800734 : Nat := 118140960795 + 2800734 * 2 ^ 59
def prefixEnd_2800734 : Nat := 4983230072969 + 3 ^ 40 * 2800734 * 2
def baseEnd_2800734 : Nat := 159791414154394483227185

theorem tailTrace_2800734 : CollatzResearch.WordTrace tailWord_2800734 prefixEnd_2800734 159791414154394483227185 := by
  unfold tailWord_2800734
  simp only [CollatzResearch.WordTrace]
  refine ⟨12768895129428315016341157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 68100774023617680087152837 12768895129428315016341157)
  ·
    refine ⟨2394167836767809065563967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12768895129428315016341157 2394167836767809065563967)
    ·
      refine ⟨3591251755151713598345951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2394167836767809065563967 3591251755151713598345951)
      ·
        refine ⟨5386877632727570397518927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3591251755151713598345951 5386877632727570397518927)
        ·
          refine ⟨8080316449091355596278391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5386877632727570397518927 8080316449091355596278391)
          ·
            refine ⟨12120474673637033394417587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8080316449091355596278391 12120474673637033394417587)
            ·
              refine ⟨18180712010455550091626381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12120474673637033394417587 18180712010455550091626381)
              ·
                refine ⟨6817767003920831284359893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18180712010455550091626381 6817767003920831284359893)
                ·
                  refine ⟨159791414154394483227185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6817767003920831284359893 159791414154394483227185)
                  ·
                    rfl

theorem cell23_2800734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 1, 3, 7].length) (baseStart_2800734 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2800734 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2800734 prefixEnd_2800734 := by exact prefixLift 2800734
  have htrace : WordTrace (prefixWord ++ tailWord_2800734) baseStart_2800734 baseEnd_2800734 := by
    simpa [prefixWord, tailWord_2800734, baseEnd_2800734] using wordTrace_append hprefix tailTrace_2800734
  have hstable : (prefixWord ++ tailWord_2800734).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2800734).length < 2 ^ (prefixWord ++ tailWord_2800734).sum := by decide
  have hdescent : baseEnd_2800734 < baseStart_2800734 := by decide
  rcases family_descends (prefixWord ++ tailWord_2800734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2800794 : List Nat := [3, 1, 1, 5, 1, 1, 3, 1, 3, 4]
def baseStart_2800794 : Nat := 118140960795 + 2800794 * 2 ^ 59
def prefixEnd_2800794 : Nat := 4983230072969 + 3 ^ 40 * 2800794 * 2
def baseEnd_2800794 : Nat := 479384512076273371431463

theorem tailTrace_2800794 : CollatzResearch.WordTrace tailWord_2800794 prefixEnd_2800794 479384512076273371431463 := by
  unfold tailWord_2800794
  simp only [CollatzResearch.WordTrace]
  refine ⟨25538337353802287594478359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68102232943472766918608957 25538337353802287594478359)
  ·
    refine ⟨38307506030703431391717539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25538337353802287594478359 38307506030703431391717539)
    ·
      refine ⟨57461259046055147087576309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38307506030703431391717539 57461259046055147087576309)
      ·
        refine ⟨5386993035567670039460279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 57461259046055147087576309 5386993035567670039460279)
        ·
          refine ⟨8080489553351505059190419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5386993035567670039460279 8080489553351505059190419)
          ·
            refine ⟨12120734330027257588785629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8080489553351505059190419 12120734330027257588785629)
            ·
              refine ⟨4545275373760221595794611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12120734330027257588785629 4545275373760221595794611)
              ·
                refine ⟨6817913060640332393691917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4545275373760221595794611 6817913060640332393691917)
                ·
                  refine ⟨2556717397740124647634469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6817913060640332393691917 2556717397740124647634469)
                  ·
                    refine ⟨479384512076273371431463, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2556717397740124647634469 479384512076273371431463)
                    ·
                      rfl

theorem cell23_2800794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 3, 1, 3, 4].length) (baseStart_2800794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2800794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2800794 prefixEnd_2800794 := by exact prefixLift 2800794
  have htrace : WordTrace (prefixWord ++ tailWord_2800794) baseStart_2800794 baseEnd_2800794 := by
    simpa [prefixWord, tailWord_2800794, baseEnd_2800794] using wordTrace_append hprefix tailTrace_2800794
  have hstable : (prefixWord ++ tailWord_2800794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2800794).length < 2 ^ (prefixWord ++ tailWord_2800794).sum := by decide
  have hdescent : baseEnd_2800794 < baseStart_2800794 := by decide
  rcases family_descends (prefixWord ++ tailWord_2800794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2800845 : List Nat := [1, 6, 2, 2, 1, 1, 1, 4, 1, 4]
def baseStart_2800845 : Nat := 118140960795 + 2800845 * 2 ^ 59
def prefixEnd_2800845 : Nat := 4983230072969 + 3 ^ 40 * 2800845 * 2
def baseEnd_2800845 : Nat := 479393241247399804918885

theorem tailTrace_2800845 : CollatzResearch.WordTrace tailWord_2800845 prefixEnd_2800845 479393241247399804918885 := by
  unfold tailWord_2800845
  simp only [CollatzResearch.WordTrace]
  refine ⟨102155209538024386088019989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68103473025349590725346659 102155209538024386088019989)
  ·
    refine ⟨4788525447094893097875937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 102155209538024386088019989 4788525447094893097875937)
    ·
      refine ⟨3591394085321169823406953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4788525447094893097875937 3591394085321169823406953)
      ·
        refine ⟨2693545563990877367555215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3591394085321169823406953 2693545563990877367555215)
        ·
          refine ⟨4040318345986316051332823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2693545563990877367555215 4040318345986316051332823)
          ·
            refine ⟨6060477518979474076999235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4040318345986316051332823 6060477518979474076999235)
            ·
              refine ⟨9090716278469211115498853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6060477518979474076999235 9090716278469211115498853)
              ·
                refine ⟨1704509302212977084156035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9090716278469211115498853 1704509302212977084156035)
                ·
                  refine ⟨2556763953319465626234053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1704509302212977084156035 2556763953319465626234053)
                  ·
                    refine ⟨479393241247399804918885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2556763953319465626234053 479393241247399804918885)
                    ·
                      rfl

theorem cell23_2800845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 1, 1, 4, 1, 4].length) (baseStart_2800845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2800845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2800845 prefixEnd_2800845 := by exact prefixLift 2800845
  have htrace : WordTrace (prefixWord ++ tailWord_2800845) baseStart_2800845 baseEnd_2800845 := by
    simpa [prefixWord, tailWord_2800845, baseEnd_2800845] using wordTrace_append hprefix tailTrace_2800845
  have hstable : (prefixWord ++ tailWord_2800845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2800845).length < 2 ^ (prefixWord ++ tailWord_2800845).sum := by decide
  have hdescent : baseEnd_2800845 < baseStart_2800845 := by decide
  rcases family_descends (prefixWord ++ tailWord_2800845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2800857 : List Nat := [1, 2, 1, 2, 3, 1, 1, 2, 2, 6, 2]
def baseStart_2800857 : Nat := 118140960795 + 2800857 * 2 ^ 59
def prefixEnd_2800857 : Nat := 4983230072969 + 3 ^ 40 * 2800857 * 2
def baseEnd_2800857 : Nat := 1438185885510053367806599

theorem tailTrace_2800857 : CollatzResearch.WordTrace tailWord_2800857 prefixEnd_2800857 1438185885510053367806599 := by
  unfold tailWord_2800857
  simp only [CollatzResearch.WordTrace]
  refine ⟨102155647213980912137456825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68103764809320608091637883 102155647213980912137456825)
  ·
    refine ⟨76616735410485684103092619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102155647213980912137456825 76616735410485684103092619)
    ·
      refine ⟨114925103115728526154638929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76616735410485684103092619 114925103115728526154638929)
      ·
        refine ⟨86193827336796394615979197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 114925103115728526154638929 86193827336796394615979197)
        ·
          refine ⟨32322685251298647980992199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 86193827336796394615979197 32322685251298647980992199)
          ·
            refine ⟨48484027876947971971488299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32322685251298647980992199 48484027876947971971488299)
            ·
              refine ⟨72726041815421957957232449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48484027876947971971488299 72726041815421957957232449)
              ·
                refine ⟨54544531361566468467924337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 72726041815421957957232449 54544531361566468467924337)
                ·
                  refine ⟨40908398521174851350943253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 54544531361566468467924337 40908398521174851350943253)
                  ·
                    refine ⟨1917581180680071157075465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 40908398521174851350943253 1917581180680071157075465)
                    ·
                      refine ⟨1438185885510053367806599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1917581180680071157075465 1438185885510053367806599)
                      ·
                        rfl

theorem cell23_2800857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 2, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 2, 2, 6, 2].length) (baseStart_2800857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2800857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2800857 prefixEnd_2800857 := by exact prefixLift 2800857
  have htrace : WordTrace (prefixWord ++ tailWord_2800857) baseStart_2800857 baseEnd_2800857 := by
    simpa [prefixWord, tailWord_2800857, baseEnd_2800857] using wordTrace_append hprefix tailTrace_2800857
  have hstable : (prefixWord ++ tailWord_2800857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2800857).length < 2 ^ (prefixWord ++ tailWord_2800857).sum := by decide
  have hdescent : baseEnd_2800857 < baseStart_2800857 := by decide
  rcases family_descends (prefixWord ++ tailWord_2800857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2800908 : List Nat := [2, 2, 1, 2, 2, 3, 2, 4, 1, 2, 2]
def baseStart_2800908 : Nat := 118140960795 + 2800908 * 2 ^ 59
def prefixEnd_2800908 : Nat := 4983230072969 + 3 ^ 40 * 2800908 * 2
def baseEnd_2800908 : Nat := 1438212073023432668268865

theorem tailTrace_2800908 : CollatzResearch.WordTrace tailWord_2800908 prefixEnd_2800908 1438212073023432668268865 := by
  unfold tailWord_2800908
  simp only [CollatzResearch.WordTrace]
  refine ⟨51078753668398073923781689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68105004891197431898375585 51078753668398073923781689)
  ·
    refine ⟨38309065251298555442836267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51078753668398073923781689 38309065251298555442836267)
    ·
      refine ⟨57463597876947833164254401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38309065251298555442836267 57463597876947833164254401)
      ·
        refine ⟨43097698407710874873190801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57463597876947833164254401 43097698407710874873190801)
        ·
          refine ⟨32323273805783156154893101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43097698407710874873190801 32323273805783156154893101)
          ·
            refine ⟨12121227677168683558084913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32323273805783156154893101 12121227677168683558084913)
            ·
              refine ⟨9090920757876512668563685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12121227677168683558084913 9090920757876512668563685)
              ·
                refine ⟨1704547642101846125355691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9090920757876512668563685 1704547642101846125355691)
                ·
                  refine ⟨2556821463152769188033537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1704547642101846125355691 2556821463152769188033537)
                  ·
                    refine ⟨1917616097364576891025153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2556821463152769188033537 1917616097364576891025153)
                    ·
                      refine ⟨1438212073023432668268865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1917616097364576891025153 1438212073023432668268865)
                      ·
                        rfl

theorem cell23_2800908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 2, 4, 1, 2, 2].length) (baseStart_2800908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2800908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2800908 prefixEnd_2800908 := by exact prefixLift 2800908
  have htrace : WordTrace (prefixWord ++ tailWord_2800908) baseStart_2800908 baseEnd_2800908 := by
    simpa [prefixWord, tailWord_2800908, baseEnd_2800908] using wordTrace_append hprefix tailTrace_2800908
  have hstable : (prefixWord ++ tailWord_2800908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2800908).length < 2 ^ (prefixWord ++ tailWord_2800908).sum := by decide
  have hdescent : baseEnd_2800908 < baseStart_2800908 := by decide
  rcases family_descends (prefixWord ++ tailWord_2800908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2800924 : List Nat := [2, 2, 3, 1, 1, 1, 5, 1, 1, 3, 3]
def baseStart_2800924 : Nat := 118140960795 + 2800924 * 2 ^ 59
def prefixEnd_2800924 : Nat := 4983230072969 + 3 ^ 40 * 2800924 * 2
def baseEnd_2800924 : Nat := 1438220288713904605668791

theorem tailTrace_2800924 : CollatzResearch.WordTrace tailWord_2800924 prefixEnd_2800924 1438220288713904605668791 := by
  unfold tailWord_2800924
  simp only [CollatzResearch.WordTrace]
  refine ⟨51079045452369091290072913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68105393936492121720097217 51079045452369091290072913)
  ·
    refine ⟨38309284089276818467554685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51079045452369091290072913 38309284089276818467554685)
    ·
      refine ⟨14365981533478806925333007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38309284089276818467554685 14365981533478806925333007)
      ·
        refine ⟨21548972300218210387999511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14365981533478806925333007 21548972300218210387999511)
        ·
          refine ⟨32323458450327315581999267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21548972300218210387999511 32323458450327315581999267)
          ·
            refine ⟨48485187675490973372998901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32323458450327315581999267 48485187675490973372998901)
            ·
              refine ⟨4545486344577278753718647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 48485187675490973372998901 4545486344577278753718647)
              ·
                refine ⟨6818229516865918130577971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4545486344577278753718647 6818229516865918130577971)
                ·
                  refine ⟨10227344275298877195866957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6818229516865918130577971 10227344275298877195866957)
                  ·
                    refine ⟨3835254103237078948450109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10227344275298877195866957 3835254103237078948450109)
                    ·
                      refine ⟨1438220288713904605668791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3835254103237078948450109 1438220288713904605668791)
                      ·
                        rfl

theorem cell23_2800924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 5, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 5, 1, 1, 3, 3].length) (baseStart_2800924 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2800924 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2800924 prefixEnd_2800924 := by exact prefixLift 2800924
  have htrace : WordTrace (prefixWord ++ tailWord_2800924) baseStart_2800924 baseEnd_2800924 := by
    simpa [prefixWord, tailWord_2800924, baseEnd_2800924] using wordTrace_append hprefix tailTrace_2800924
  have hstable : (prefixWord ++ tailWord_2800924).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2800924).length < 2 ^ (prefixWord ++ tailWord_2800924).sum := by decide
  have hdescent : baseEnd_2800924 < baseStart_2800924 := by decide
  rcases family_descends (prefixWord ++ tailWord_2800924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2800977 : List Nat := [1, 2, 2, 1, 4, 1, 2, 1, 1, 4, 4]
def baseStart_2800977 : Nat := 118140960795 + 2800977 * 2 ^ 59
def prefixEnd_2800977 : Nat := 4983230072969 + 3 ^ 40 * 2800977 * 2
def baseEnd_2800977 : Nat := 1438247503188592898306047

theorem tailTrace_2800977 : CollatzResearch.WordTrace tailWord_2800977 prefixEnd_2800977 1438247503188592898306047 := by
  unfold tailWord_2800977
  simp only [CollatzResearch.WordTrace]
  refine ⟨102160023973546172631825185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68106682649030781754550123 102160023973546172631825185)
  ·
    refine ⟨76620017980159629473868889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102160023973546172631825185 76620017980159629473868889)
    ·
      refine ⟨57465013485119722105401667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76620017980159629473868889 57465013485119722105401667)
      ·
        refine ⟨86197520227679583158102501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57465013485119722105401667 86197520227679583158102501)
        ·
          refine ⟨16162035042689921842144219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 86197520227679583158102501 16162035042689921842144219)
          ·
            refine ⟨24243052564034882763216329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16162035042689921842144219 24243052564034882763216329)
            ·
              refine ⟨18182289423026162072412247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24243052564034882763216329 18182289423026162072412247)
              ·
                refine ⟨27273434134539243108618371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18182289423026162072412247 27273434134539243108618371)
                ·
                  refine ⟨40910151201808864662927557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27273434134539243108618371 40910151201808864662927557)
                  ·
                    refine ⟨7670653350339162124298917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 40910151201808864662927557 7670653350339162124298917)
                    ·
                      refine ⟨1438247503188592898306047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7670653350339162124298917 1438247503188592898306047)
                      ·
                        rfl

theorem cell23_2800977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 2, 1, 1, 4, 4].length) (baseStart_2800977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2800977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2800977 prefixEnd_2800977 := by exact prefixLift 2800977
  have htrace : WordTrace (prefixWord ++ tailWord_2800977) baseStart_2800977 baseEnd_2800977 := by
    simpa [prefixWord, tailWord_2800977, baseEnd_2800977] using wordTrace_append hprefix tailTrace_2800977
  have hstable : (prefixWord ++ tailWord_2800977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2800977).length < 2 ^ (prefixWord ++ tailWord_2800977).sum := by decide
  have hdescent : baseEnd_2800977 < baseStart_2800977 := by decide
  rcases family_descends (prefixWord ++ tailWord_2800977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2801097 : List Nat := [1, 2, 1, 1, 2, 1, 3, 1, 3, 2, 6]
def baseStart_2801097 : Nat := 118140960795 + 2801097 * 2 ^ 59
def prefixEnd_2801097 : Nat := 4983230072969 + 3 ^ 40 * 2801097 * 2
def baseEnd_2801097 : Nat := 1438309120867132428805495

theorem tailTrace_2801097 : CollatzResearch.WordTrace tailWord_2801097 prefixEnd_2801097 1438309120867132428805495 := by
  unfold tailWord_2801097
  simp only [CollatzResearch.WordTrace]
  refine ⟨102164400733111433126193545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68109600488740955417462363 102164400733111433126193545)
  ·
    refine ⟨76623300549833574844645159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102164400733111433126193545 76623300549833574844645159)
    ·
      refine ⟨114934950824750362266967739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76623300549833574844645159 114934950824750362266967739)
      ·
        refine ⟨172402426237125543400451609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114934950824750362266967739 172402426237125543400451609)
        ·
          refine ⟨129301819677844157550338707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 172402426237125543400451609 129301819677844157550338707)
          ·
            refine ⟨193952729516766236325508061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 129301819677844157550338707 193952729516766236325508061)
            ·
              refine ⟨72732273568787338622065523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 193952729516766236325508061 72732273568787338622065523)
              ·
                refine ⟨109098410353181007933098285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 72732273568787338622065523 109098410353181007933098285)
                ·
                  refine ⟨40911903882442877974911857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 109098410353181007933098285 40911903882442877974911857)
                  ·
                    refine ⟨30683927911832158481183893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 40911903882442877974911857 30683927911832158481183893)
                    ·
                      refine ⟨1438309120867132428805495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 30683927911832158481183893 1438309120867132428805495)
                      ·
                        rfl

theorem cell23_2801097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 1, 3, 2, 6].length) (baseStart_2801097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2801097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2801097 prefixEnd_2801097 := by exact prefixLift 2801097
  have htrace : WordTrace (prefixWord ++ tailWord_2801097) baseStart_2801097 baseEnd_2801097 := by
    simpa [prefixWord, tailWord_2801097, baseEnd_2801097] using wordTrace_append hprefix tailTrace_2801097
  have hstable : (prefixWord ++ tailWord_2801097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2801097).length < 2 ^ (prefixWord ++ tailWord_2801097).sum := by decide
  have hdescent : baseEnd_2801097 < baseStart_2801097 := by decide
  rcases family_descends (prefixWord ++ tailWord_2801097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2801184 : List Nat := [2, 1, 1, 6, 1, 12]
def baseStart_2801184 : Nat := 118140960795 + 2801184 * 2 ^ 59
def prefixEnd_2801184 : Nat := 4983230072969 + 3 ^ 40 * 2801184 * 2
def baseEnd_2801184 : Nat := 5919151414337751392665

theorem tailTrace_2801184 : CollatzResearch.WordTrace tailWord_2801184 prefixEnd_2801184 5919151414337751392665 := by
  unfold tailWord_2801184
  simp only [CollatzResearch.WordTrace]
  refine ⟨51083786941898123492305303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68111715922530831323073737 51083786941898123492305303)
  ·
    refine ⟨76625680412847185238457955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51083786941898123492305303 76625680412847185238457955)
    ·
      refine ⟨114938520619270777857686933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76625680412847185238457955 114938520619270777857686933)
      ·
        refine ⟨5387743154028317712079075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 114938520619270777857686933 5387743154028317712079075)
        ·
          refine ⟨8081614731042476568118613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5387743154028317712079075 8081614731042476568118613)
          ·
            refine ⟨5919151414337751392665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 8081614731042476568118613 5919151414337751392665)
            ·
              rfl

theorem cell23_2801184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 12].length) (baseStart_2801184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2801184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2801184 prefixEnd_2801184 := by exact prefixLift 2801184
  have htrace : WordTrace (prefixWord ++ tailWord_2801184) baseStart_2801184 baseEnd_2801184 := by
    simpa [prefixWord, tailWord_2801184, baseEnd_2801184] using wordTrace_append hprefix tailTrace_2801184
  have hstable : (prefixWord ++ tailWord_2801184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2801184).length < 2 ^ (prefixWord ++ tailWord_2801184).sum := by decide
  have hdescent : baseEnd_2801184 < baseStart_2801184 := by decide
  rcases family_descends (prefixWord ++ tailWord_2801184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2801198 : List Nat := [4, 1, 3, 1, 2, 1, 1, 2, 3, 2, 3]
def baseStart_2801198 : Nat := 118140960795 + 2801198 * 2 ^ 59
def prefixEnd_2801198 : Nat := 4983230072969 + 3 ^ 40 * 2801198 * 2
def baseEnd_2801198 : Nat := 1438360982413236533642531

theorem tailTrace_2801198 : CollatzResearch.WordTrace tailWord_2801198 prefixEnd_2801198 1438360982413236533642531 := by
  unfold tailWord_2801198
  simp only [CollatzResearch.WordTrace]
  refine ⟨12771010563218190921952531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 68112056337163684917080165 12771010563218190921952531)
  ·
    refine ⟨19156515844827286382928797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12771010563218190921952531 19156515844827286382928797)
    ·
      refine ⟨7183693441810232393598299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19156515844827286382928797 7183693441810232393598299)
      ·
        refine ⟨10775540162715348590397449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7183693441810232393598299 10775540162715348590397449)
        ·
          refine ⟨8081655122036511442798087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10775540162715348590397449 8081655122036511442798087)
          ·
            refine ⟨12122482683054767164197131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8081655122036511442798087 12122482683054767164197131)
            ·
              refine ⟨18183724024582150746295697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12122482683054767164197131 18183724024582150746295697)
              ·
                refine ⟨13637793018436613059721773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18183724024582150746295697 13637793018436613059721773)
                ·
                  refine ⟨5114172381913729897395665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13637793018436613059721773 5114172381913729897395665)
                  ·
                    refine ⟨3835629286435297423046749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5114172381913729897395665 3835629286435297423046749)
                    ·
                      refine ⟨1438360982413236533642531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3835629286435297423046749 1438360982413236533642531)
                      ·
                        rfl

theorem cell23_2801198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 1, 2, 3, 2, 3].length) (baseStart_2801198 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2801198 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2801198 prefixEnd_2801198 := by exact prefixLift 2801198
  have htrace : WordTrace (prefixWord ++ tailWord_2801198) baseStart_2801198 baseEnd_2801198 := by
    simpa [prefixWord, tailWord_2801198, baseEnd_2801198] using wordTrace_append hprefix tailTrace_2801198
  have hstable : (prefixWord ++ tailWord_2801198).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2801198).length < 2 ^ (prefixWord ++ tailWord_2801198).sum := by decide
  have hdescent : baseEnd_2801198 < baseStart_2801198 := by decide
  rcases family_descends (prefixWord ++ tailWord_2801198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2801229 : List Nat := [1, 6, 1, 1, 4, 1, 2, 1, 1, 1, 4]
def baseStart_2801229 : Nat := 118140960795 + 2801229 * 2 ^ 59
def prefixEnd_2801229 : Nat := 4983230072969 + 3 ^ 40 * 2801229 * 2
def baseEnd_2801229 : Nat := 1438376900313525912354889

theorem tailTrace_2801229 : CollatzResearch.WordTrace tailWord_2801229 prefixEnd_2801229 1438376900313525912354889 := by
  unfold tailWord_2801229
  simp only [CollatzResearch.WordTrace]
  refine ⟨102169215168633219669998741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68112810112422146446665827 102169215168633219669998741)
  ·
    refine ⟨4789181961029682172031191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 102169215168633219669998741 4789181961029682172031191)
    ·
      refine ⟨7183772941544523258046787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4789181961029682172031191 7183772941544523258046787)
      ·
        refine ⟨10775659412316784887070181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7183772941544523258046787 10775659412316784887070181)
        ·
          refine ⟨2020436139809397166325659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10775659412316784887070181 2020436139809397166325659)
          ·
            refine ⟨3030654209714095749488489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2020436139809397166325659 3030654209714095749488489)
            ·
              refine ⟨2272990657285571812116367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3030654209714095749488489 2272990657285571812116367)
              ·
                refine ⟨3409485985928357718174551, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2272990657285571812116367 3409485985928357718174551)
                ·
                  refine ⟨5114228978892536577261827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3409485985928357718174551 5114228978892536577261827)
                  ·
                    refine ⟨7671343468338804865892741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5114228978892536577261827 7671343468338804865892741)
                    ·
                      refine ⟨1438376900313525912354889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7671343468338804865892741 1438376900313525912354889)
                      ·
                        rfl

theorem cell23_2801229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 4, 1, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 4, 1, 2, 1, 1, 1, 4].length) (baseStart_2801229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2801229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2801229 prefixEnd_2801229 := by exact prefixLift 2801229
  have htrace : WordTrace (prefixWord ++ tailWord_2801229) baseStart_2801229 baseEnd_2801229 := by
    simpa [prefixWord, tailWord_2801229, baseEnd_2801229] using wordTrace_append hprefix tailTrace_2801229
  have hstable : (prefixWord ++ tailWord_2801229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2801229).length < 2 ^ (prefixWord ++ tailWord_2801229).sum := by decide
  have hdescent : baseEnd_2801229 < baseStart_2801229 := by decide
  rcases family_descends (prefixWord ++ tailWord_2801229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2801262 : List Nat := [4, 1, 2, 2, 4, 1, 1, 1, 1, 3, 3]
def baseStart_2801262 : Nat := 118140960795 + 2801262 * 2 ^ 59
def prefixEnd_2801262 : Nat := 4983230072969 + 3 ^ 40 * 2801262 * 2
def baseEnd_2801262 : Nat := 1438393845175124283242237

theorem tailTrace_2801262 : CollatzResearch.WordTrace tailWord_2801262 prefixEnd_2801262 1438393845175124283242237 := by
  unfold tailWord_2801262
  simp only [CollatzResearch.WordTrace]
  refine ⟨12771302347189208288243755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 68113612518342444203966693 12771302347189208288243755)
  ·
    refine ⟨19156953520783812432365633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12771302347189208288243755 19156953520783812432365633)
    ·
      refine ⟨14367715140587859324274225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19156953520783812432365633 14367715140587859324274225)
      ·
        refine ⟨10775786355440894493205669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14367715140587859324274225 10775786355440894493205669)
        ·
          refine ⟨2020459941645167717476063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10775786355440894493205669 2020459941645167717476063)
          ·
            refine ⟨3030689912467751576214095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2020459941645167717476063 3030689912467751576214095)
            ·
              refine ⟨4546034868701627364321143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3030689912467751576214095 4546034868701627364321143)
              ·
                refine ⟨6819052303052441046481715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4546034868701627364321143 6819052303052441046481715)
                ·
                  refine ⟨10228578454578661569722573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6819052303052441046481715 10228578454578661569722573)
                  ·
                    refine ⟨3835716920466998088645965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10228578454578661569722573 3835716920466998088645965)
                    ·
                      refine ⟨1438393845175124283242237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3835716920466998088645965 1438393845175124283242237)
                      ·
                        rfl

theorem cell23_2801262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 4, 1, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 4, 1, 1, 1, 1, 3, 3].length) (baseStart_2801262 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2801262 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2801262 prefixEnd_2801262 := by exact prefixLift 2801262
  have htrace : WordTrace (prefixWord ++ tailWord_2801262) baseStart_2801262 baseEnd_2801262 := by
    simpa [prefixWord, tailWord_2801262, baseEnd_2801262] using wordTrace_append hprefix tailTrace_2801262
  have hstable : (prefixWord ++ tailWord_2801262).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2801262).length < 2 ^ (prefixWord ++ tailWord_2801262).sum := by decide
  have hdescent : baseEnd_2801262 < baseStart_2801262 := by decide
  rcases family_descends (prefixWord ++ tailWord_2801262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2801274 : List Nat := [3, 1, 1, 1, 1, 1, 1, 5, 9]
def baseStart_2801274 : Nat := 118140960795 + 2801274 * 2 ^ 59
def prefixEnd_2801274 : Nat := 4983230072969 + 3 ^ 40 * 2801274 * 2
def baseEnd_2801274 : Nat := 159822222993664248476909

theorem tailTrace_2801274 : CollatzResearch.WordTrace tailWord_2801274 prefixEnd_2801274 159822222993664248476909 := by
  unfold tailWord_2801274
  simp only [CollatzResearch.WordTrace]
  refine ⟨25542714113367548088846719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68113904302313461570257917 25542714113367548088846719)
  ·
    refine ⟨38314071170051322133270079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25542714113367548088846719 38314071170051322133270079)
    ·
      refine ⟨57471106755076983199905119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38314071170051322133270079 57471106755076983199905119)
      ·
        refine ⟨86206660132615474799857679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57471106755076983199905119 86206660132615474799857679)
        ·
          refine ⟨129309990198923212199786519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86206660132615474799857679 129309990198923212199786519)
          ·
            refine ⟨193964985298384818299679779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 129309990198923212199786519 193964985298384818299679779)
            ·
              refine ⟨290947477947577227449519669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 193964985298384818299679779 290947477947577227449519669)
              ·
                refine ⟨27276326057585365073392469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 290947477947577227449519669 27276326057585365073392469)
                ·
                  refine ⟨159822222993664248476909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 27276326057585365073392469 159822222993664248476909)
                  ·
                    rfl

theorem cell23_2801274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 5, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 5, 9].length) (baseStart_2801274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2801274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2801274 prefixEnd_2801274 := by exact prefixLift 2801274
  have htrace : WordTrace (prefixWord ++ tailWord_2801274) baseStart_2801274 baseEnd_2801274 := by
    simpa [prefixWord, tailWord_2801274, baseEnd_2801274] using wordTrace_append hprefix tailTrace_2801274
  have hstable : (prefixWord ++ tailWord_2801274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2801274).length < 2 ^ (prefixWord ++ tailWord_2801274).sum := by decide
  have hdescent : baseEnd_2801274 < baseStart_2801274 := by decide
  rcases family_descends (prefixWord ++ tailWord_2801274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2801301 : List Nat := [1, 3, 2, 1, 1, 1, 1, 3, 4, 3, 3]
def baseStart_2801301 : Nat := 118140960795 + 2801301 * 2 ^ 59
def prefixEnd_2801301 : Nat := 4983230072969 + 3 ^ 40 * 2801301 * 2
def baseEnd_2801301 : Nat := 1438413870920649630654557

theorem tailTrace_2801301 : CollatzResearch.WordTrace tailWord_2801301 prefixEnd_2801301 1438413870920649630654557 := by
  unfold tailWord_2801301
  simp only [CollatzResearch.WordTrace]
  refine ⟨102171841224372375966619757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68114560816248250644413171 102171841224372375966619757)
  ·
    refine ⟨38314440459139640987482409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 102171841224372375966619757 38314440459139640987482409)
    ·
      refine ⟨28735830344354730740611807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38314440459139640987482409 28735830344354730740611807)
      ·
        refine ⟨43103745516532096110917711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28735830344354730740611807 43103745516532096110917711)
        ·
          refine ⟨64655618274798144166376567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43103745516532096110917711 64655618274798144166376567)
          ·
            refine ⟨96983427412197216249564851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64655618274798144166376567 96983427412197216249564851)
            ·
              refine ⟨145475141118295824374347277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 96983427412197216249564851 145475141118295824374347277)
              ·
                refine ⟨54553177919360934140380229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 145475141118295824374347277 54553177919360934140380229)
                ·
                  refine ⟨10228720859880175151321293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 54553177919360934140380229 10228720859880175151321293)
                  ·
                    refine ⟨3835770322455065681745485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10228720859880175151321293 3835770322455065681745485)
                    ·
                      refine ⟨1438413870920649630654557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3835770322455065681745485 1438413870920649630654557)
                      ·
                        rfl

theorem cell23_2801301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 3, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 3, 4, 3, 3].length) (baseStart_2801301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2801301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2801301 prefixEnd_2801301 := by exact prefixLift 2801301
  have htrace : WordTrace (prefixWord ++ tailWord_2801301) baseStart_2801301 baseEnd_2801301 := by
    simpa [prefixWord, tailWord_2801301, baseEnd_2801301] using wordTrace_append hprefix tailTrace_2801301
  have hstable : (prefixWord ++ tailWord_2801301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2801301).length < 2 ^ (prefixWord ++ tailWord_2801301).sum := by decide
  have hdescent : baseEnd_2801301 < baseStart_2801301 := by decide
  rcases family_descends (prefixWord ++ tailWord_2801301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2801338 : List Nat := [3, 1, 1, 1, 2, 5, 2, 1, 2, 5]
def baseStart_2801338 : Nat := 118140960795 + 2801338 * 2 ^ 59
def prefixEnd_2801338 : Nat := 4983230072969 + 3 ^ 40 * 2801338 * 2
def baseEnd_2801338 : Nat := 479477623234955328630629

theorem tailTrace_2801338 : CollatzResearch.WordTrace tailWord_2801338 prefixEnd_2801338 479477623234955328630629 := by
  unfold tailWord_2801338
  simp only [CollatzResearch.WordTrace]
  refine ⟨25543297681309582821429167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68115460483492220857144445 25543297681309582821429167)
  ·
    refine ⟨38314946521964374232143751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25543297681309582821429167 38314946521964374232143751)
    ·
      refine ⟨57472419782946561348215627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38314946521964374232143751 57472419782946561348215627)
      ·
        refine ⟨86208629674419842022323441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57472419782946561348215627 86208629674419842022323441)
        ·
          refine ⟨64656472255814881516742581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 86208629674419842022323441 64656472255814881516742581)
          ·
            refine ⟨6061544273982645142194617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 64656472255814881516742581 6061544273982645142194617)
            ·
              refine ⟨4546158205486983856645963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6061544273982645142194617 4546158205486983856645963)
              ·
                refine ⟨6819237308230475784968945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4546158205486983856645963 6819237308230475784968945)
                ·
                  refine ⟨5114427981172856838726709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6819237308230475784968945 5114427981172856838726709)
                  ·
                    refine ⟨479477623234955328630629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5114427981172856838726709 479477623234955328630629)
                    ·
                      rfl

theorem cell23_2801338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 5, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 5, 2, 1, 2, 5].length) (baseStart_2801338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2801338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2801338 prefixEnd_2801338 := by exact prefixLift 2801338
  have htrace : WordTrace (prefixWord ++ tailWord_2801338) baseStart_2801338 baseEnd_2801338 := by
    simpa [prefixWord, tailWord_2801338, baseEnd_2801338] using wordTrace_append hprefix tailTrace_2801338
  have hstable : (prefixWord ++ tailWord_2801338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2801338).length < 2 ^ (prefixWord ++ tailWord_2801338).sum := by decide
  have hdescent : baseEnd_2801338 < baseStart_2801338 := by decide
  rcases family_descends (prefixWord ++ tailWord_2801338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2801358 : List Nat := [4, 1, 1, 1, 3, 1, 1, 4, 2, 1, 4]
def baseStart_2801358 : Nat := 118140960795 + 2801358 * 2 ^ 59
def prefixEnd_2801358 : Nat := 4983230072969 + 3 ^ 40 * 2801358 * 2
def baseEnd_2801358 : Nat := 1438443139317955907641795

theorem tailTrace_2801358 : CollatzResearch.WordTrace tailWord_2801358 prefixEnd_2801358 1438443139317955907641795 := by
  unfold tailWord_2801358
  simp only [CollatzResearch.WordTrace]
  refine ⟨12771740023145734337680591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 68115946790110583134296485 12771740023145734337680591)
  ·
    refine ⟨19157610034718601506520887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12771740023145734337680591 19157610034718601506520887)
    ·
      refine ⟨28736415052077902259781331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19157610034718601506520887 28736415052077902259781331)
      ·
        refine ⟨43104622578116853389671997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28736415052077902259781331 43104622578116853389671997)
        ·
          refine ⟨16164233466793820021126999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43104622578116853389671997 16164233466793820021126999)
          ·
            refine ⟨24246350200190730031690499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16164233466793820021126999 24246350200190730031690499)
            ·
              refine ⟨36369525300286095047535749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24246350200190730031690499 36369525300286095047535749)
              ·
                refine ⟨6819285993803642821412953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 36369525300286095047535749 6819285993803642821412953)
                ·
                  refine ⟨5114464495352732116059715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6819285993803642821412953 5114464495352732116059715)
                  ·
                    refine ⟨7671696743029098174089573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5114464495352732116059715 7671696743029098174089573)
                    ·
                      refine ⟨1438443139317955907641795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7671696743029098174089573 1438443139317955907641795)
                      ·
                        rfl

theorem cell23_2801358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 1, 4, 2, 1, 4].length) (baseStart_2801358 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2801358 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2801358 prefixEnd_2801358 := by exact prefixLift 2801358
  have htrace : WordTrace (prefixWord ++ tailWord_2801358) baseStart_2801358 baseEnd_2801358 := by
    simpa [prefixWord, tailWord_2801358, baseEnd_2801358] using wordTrace_append hprefix tailTrace_2801358
  have hstable : (prefixWord ++ tailWord_2801358).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2801358).length < 2 ^ (prefixWord ++ tailWord_2801358).sum := by decide
  have hdescent : baseEnd_2801358 < baseStart_2801358 := by decide
  rcases family_descends (prefixWord ++ tailWord_2801358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2801368 : List Nat := [2, 1, 2, 2, 3, 1, 2, 3, 3, 4]
def baseStart_2801368 : Nat := 118140960795 + 2801368 * 2 ^ 59
def prefixEnd_2801368 : Nat := 4983230072969 + 3 ^ 40 * 2801368 * 2
def baseEnd_2801368 : Nat := 479482758041500289505583

theorem tailTrace_2801368 : CollatzResearch.WordTrace tailWord_2801368 prefixEnd_2801368 479482758041500289505583 := by
  unfold tailWord_2801368
  simp only [CollatzResearch.WordTrace]
  refine ⟨51087142457564823204654379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68116189943419764272872505 51087142457564823204654379)
  ·
    refine ⟨76630713686347234806981569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51087142457564823204654379 76630713686347234806981569)
    ·
      refine ⟨57473035264760426105236177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76630713686347234806981569 57473035264760426105236177)
      ·
        refine ⟨43104776448570319578927133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57473035264760426105236177 43104776448570319578927133)
        ·
          refine ⟨16164291168213869842097675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43104776448570319578927133 16164291168213869842097675)
          ·
            refine ⟨24246436752320804763146513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16164291168213869842097675 24246436752320804763146513)
            ·
              refine ⟨18184827564240603572359885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24246436752320804763146513 18184827564240603572359885)
              ·
                refine ⟨6819310336590226339634957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18184827564240603572359885 6819310336590226339634957)
                ·
                  refine ⟨2557241376221334877363109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6819310336590226339634957 2557241376221334877363109)
                  ·
                    refine ⟨479482758041500289505583, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2557241376221334877363109 479482758041500289505583)
                    ·
                      rfl

theorem cell23_2801368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 2, 3, 3, 4].length) (baseStart_2801368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2801368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2801368 prefixEnd_2801368 := by exact prefixLift 2801368
  have htrace : WordTrace (prefixWord ++ tailWord_2801368) baseStart_2801368 baseEnd_2801368 := by
    simpa [prefixWord, tailWord_2801368, baseEnd_2801368] using wordTrace_append hprefix tailTrace_2801368
  have hstable : (prefixWord ++ tailWord_2801368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2801368).length < 2 ^ (prefixWord ++ tailWord_2801368).sum := by decide
  have hdescent : baseEnd_2801368 < baseStart_2801368 := by decide
  rcases family_descends (prefixWord ++ tailWord_2801368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2801445 : List Nat := [1, 3, 1, 2, 3, 3, 2, 2, 1, 5]
def baseStart_2801445 : Nat := 118140960795 + 2801445 * 2 ^ 59
def prefixEnd_2801445 : Nat := 4983230072969 + 3 ^ 40 * 2801445 * 2
def baseEnd_2801445 : Nat := 479495937378299022417965

theorem tailTrace_2801445 : CollatzResearch.WordTrace tailWord_2801445 prefixEnd_2801445 479495937378299022417965 := by
  unfold tailWord_2801445
  simp only [CollatzResearch.WordTrace]
  refine ⟨102177093335850688559861789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68118062223900459039907859 102177093335850688559861789)
  ·
    refine ⟨38316410000944008209948171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 102177093335850688559861789 38316410000944008209948171)
    ·
      refine ⟨57474615001416012314922257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38316410000944008209948171 57474615001416012314922257)
      ·
        refine ⟨43105961251062009236191693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57474615001416012314922257 43105961251062009236191693)
        ·
          refine ⟨16164735469148253463571885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43105961251062009236191693 16164735469148253463571885)
          ·
            refine ⟨6061775800930595048839457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16164735469148253463571885 6061775800930595048839457)
            ·
              refine ⟨4546331850697946286629593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6061775800930595048839457 4546331850697946286629593)
              ·
                refine ⟨3409748888023459714972195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4546331850697946286629593 3409748888023459714972195)
                ·
                  refine ⟨5114623332035189572458293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3409748888023459714972195 5114623332035189572458293)
                  ·
                    refine ⟨479495937378299022417965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5114623332035189572458293 479495937378299022417965)
                    ·
                      rfl

theorem cell23_2801445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 3, 2, 2, 1, 5].length) (baseStart_2801445 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2801445 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2801445 prefixEnd_2801445 := by exact prefixLift 2801445
  have htrace : WordTrace (prefixWord ++ tailWord_2801445) baseStart_2801445 baseEnd_2801445 := by
    simpa [prefixWord, tailWord_2801445, baseEnd_2801445] using wordTrace_append hprefix tailTrace_2801445
  have hstable : (prefixWord ++ tailWord_2801445).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2801445).length < 2 ^ (prefixWord ++ tailWord_2801445).sum := by decide
  have hdescent : baseEnd_2801445 < baseStart_2801445 := by decide
  rcases family_descends (prefixWord ++ tailWord_2801445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2801462 : List Nat := [5, 1, 2, 2, 1, 1, 2, 3, 1, 5]
def baseStart_2801462 : Nat := 118140960795 + 2801462 * 2 ^ 59
def prefixEnd_2801462 : Nat := 4983230072969 + 3 ^ 40 * 2801462 * 2
def baseEnd_2801462 : Nat := 479498847102007833580439

theorem tailTrace_2801462 : CollatzResearch.WordTrace tailWord_2801462 prefixEnd_2801462 479498847102007833580439 := by
  unfold tailWord_2801462
  simp only [CollatzResearch.WordTrace]
  refine ⟨6386107086049318778951915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 68118475584526066975487093 6386107086049318778951915)
  ·
    refine ⟨9579160629073978168427873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6386107086049318778951915 9579160629073978168427873)
    ·
      refine ⟨7184370471805483626320905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9579160629073978168427873 7184370471805483626320905)
      ·
        refine ⟨5388277853854112719740679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7184370471805483626320905 5388277853854112719740679)
        ·
          refine ⟨8082416780781169079611019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5388277853854112719740679 8082416780781169079611019)
          ·
            refine ⟨12123625171171753619416529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8082416780781169079611019 12123625171171753619416529)
            ·
              refine ⟨9092718878378815214562397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12123625171171753619416529 9092718878378815214562397)
              ·
                refine ⟨3409769579392055705460899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9092718878378815214562397 3409769579392055705460899)
                ·
                  refine ⟨5114654369088083558191349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3409769579392055705460899 5114654369088083558191349)
                  ·
                    refine ⟨479498847102007833580439, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5114654369088083558191349 479498847102007833580439)
                    ·
                      rfl

theorem cell23_2801462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 2, 3, 1, 5].length) (baseStart_2801462 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2801462 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2801462 prefixEnd_2801462 := by exact prefixLift 2801462
  have htrace : WordTrace (prefixWord ++ tailWord_2801462) baseStart_2801462 baseEnd_2801462 := by
    simpa [prefixWord, tailWord_2801462, baseEnd_2801462] using wordTrace_append hprefix tailTrace_2801462
  have hstable : (prefixWord ++ tailWord_2801462).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2801462).length < 2 ^ (prefixWord ++ tailWord_2801462).sum := by decide
  have hdescent : baseEnd_2801462 < baseStart_2801462 := by decide
  rcases family_descends (prefixWord ++ tailWord_2801462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2801468 : List Nat := [2, 2, 2, 2, 1, 1, 3, 3, 1, 1, 5]
def baseStart_2801468 : Nat := 118140960795 + 2801468 * 2 ^ 59
def prefixEnd_2801468 : Nat := 4983230072969 + 3 ^ 40 * 2801468 * 2
def baseEnd_2801468 : Nat := 1438499622189950477266289

theorem tailTrace_2801468 : CollatzResearch.WordTrace tailWord_2801468 prefixEnd_2801468 1438499622189950477266289 := by
  unfold tailWord_2801468
  simp only [CollatzResearch.WordTrace]
  refine ⟨51088966107383681743974529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68118621476511575658632705 51088966107383681743974529)
  ·
    refine ⟨38316724580537761307980897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51088966107383681743974529 38316724580537761307980897)
    ·
      refine ⟨28737543435403320980985673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38316724580537761307980897 28737543435403320980985673)
      ·
        refine ⟨21553157576552490735739255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28737543435403320980985673 21553157576552490735739255)
        ·
          refine ⟨32329736364828736103608883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21553157576552490735739255 32329736364828736103608883)
          ·
            refine ⟨48494604547243104155413325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32329736364828736103608883 48494604547243104155413325)
            ·
              refine ⟨18185476705216164058279997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 48494604547243104155413325 18185476705216164058279997)
              ·
                refine ⟨6819553764456061521854999, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18185476705216164058279997 6819553764456061521854999)
                ·
                  refine ⟨10229330646684092282782499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6819553764456061521854999 10229330646684092282782499)
                  ·
                    refine ⟨15343995970026138424173749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10229330646684092282782499 15343995970026138424173749)
                    ·
                      refine ⟨1438499622189950477266289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15343995970026138424173749 1438499622189950477266289)
                      ·
                        rfl

theorem cell23_2801468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 3, 3, 1, 1, 5].length) (baseStart_2801468 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2801468 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2801468 prefixEnd_2801468 := by exact prefixLift 2801468
  have htrace : WordTrace (prefixWord ++ tailWord_2801468) baseStart_2801468 baseEnd_2801468 := by
    simpa [prefixWord, tailWord_2801468, baseEnd_2801468] using wordTrace_append hprefix tailTrace_2801468
  have hstable : (prefixWord ++ tailWord_2801468).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2801468).length < 2 ^ (prefixWord ++ tailWord_2801468).sum := by decide
  have hdescent : baseEnd_2801468 < baseStart_2801468 := by decide
  rcases family_descends (prefixWord ++ tailWord_2801468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2801492 : List Nat := [2, 4, 1, 1, 3, 2, 1, 3, 2, 4]
def baseStart_2801492 : Nat := 118140960795 + 2801492 * 2 ^ 59
def prefixEnd_2801492 : Nat := 4983230072969 + 3 ^ 40 * 2801492 * 2
def baseEnd_2801492 : Nat := 479503981908552794455393

theorem tailTrace_2801492 : CollatzResearch.WordTrace tailWord_2801492 prefixEnd_2801492 479503981908552794455393 := by
  unfold tailWord_2801492
  simp only [CollatzResearch.WordTrace]
  refine ⟨51089403783340207793411365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68119205044453610391215153 51089403783340207793411365)
  ·
    refine ⟨9579263209376288961264631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 51089403783340207793411365 9579263209376288961264631)
    ·
      refine ⟨14368894814064433441896947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9579263209376288961264631 14368894814064433441896947)
      ·
        refine ⟨21553342221096650162845421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14368894814064433441896947 21553342221096650162845421)
        ·
          refine ⟨8082503332911243811067033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21553342221096650162845421 8082503332911243811067033)
          ·
            refine ⟨6061877499683432858300275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8082503332911243811067033 6061877499683432858300275)
            ·
              refine ⟨9092816249525149287450413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6061877499683432858300275 9092816249525149287450413)
              ·
                refine ⟨3409806093571930982793905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9092816249525149287450413 3409806093571930982793905)
                ·
                  refine ⟨2557354570178948237095429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3409806093571930982793905 2557354570178948237095429)
                  ·
                    refine ⟨479503981908552794455393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2557354570178948237095429 479503981908552794455393)
                    ·
                      rfl

theorem cell23_2801492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 2, 1, 3, 2, 4].length) (baseStart_2801492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2801492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2801492 prefixEnd_2801492 := by exact prefixLift 2801492
  have htrace : WordTrace (prefixWord ++ tailWord_2801492) baseStart_2801492 baseEnd_2801492 := by
    simpa [prefixWord, tailWord_2801492, baseEnd_2801492] using wordTrace_append hprefix tailTrace_2801492
  have hstable : (prefixWord ++ tailWord_2801492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2801492).length < 2 ^ (prefixWord ++ tailWord_2801492).sum := by decide
  have hdescent : baseEnd_2801492 < baseStart_2801492 := by decide
  rcases family_descends (prefixWord ++ tailWord_2801492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2801568 : List Nat := [2, 1, 1, 4, 1, 1, 1, 1, 3, 4, 4]
def baseStart_2801568 : Nat := 118140960795 + 2801568 * 2 ^ 59
def prefixEnd_2801568 : Nat := 4983230072969 + 3 ^ 40 * 2801568 * 2
def baseEnd_2801568 : Nat := 1438550970255400086015829

theorem tailTrace_2801568 : CollatzResearch.WordTrace tailWord_2801568 prefixEnd_2801568 1438550970255400086015829 := by
  unfold tailWord_2801568
  simp only [CollatzResearch.WordTrace]
  refine ⟨51090789757202540283294679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68121053009603387044392905 51090789757202540283294679)
  ·
    refine ⟨76636184635803810424942019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51090789757202540283294679 76636184635803810424942019)
    ·
      refine ⟨114954276953705715637413029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76636184635803810424942019 114954276953705715637413029)
      ·
        refine ⟨21553926928819821682014943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 114954276953705715637413029 21553926928819821682014943)
        ·
          refine ⟨32330890393229732523022415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21553926928819821682014943 32330890393229732523022415)
          ·
            refine ⟨48496335589844598784533623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32330890393229732523022415 48496335589844598784533623)
            ·
              refine ⟨72744503384766898176800435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48496335589844598784533623 72744503384766898176800435)
              ·
                refine ⟨109116755077150347265200653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 72744503384766898176800435 109116755077150347265200653)
                ·
                  refine ⟨40918783153931380224450245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 109116755077150347265200653 40918783153931380224450245)
                  ·
                    refine ⟨7672271841362133792084421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 40918783153931380224450245 7672271841362133792084421)
                    ·
                      refine ⟨1438550970255400086015829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7672271841362133792084421 1438550970255400086015829)
                      ·
                        rfl

theorem cell23_2801568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 1, 3, 4, 4].length) (baseStart_2801568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2801568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2801568 prefixEnd_2801568 := by exact prefixLift 2801568
  have htrace : WordTrace (prefixWord ++ tailWord_2801568) baseStart_2801568 baseEnd_2801568 := by
    simpa [prefixWord, tailWord_2801568, baseEnd_2801568] using wordTrace_append hprefix tailTrace_2801568
  have hstable : (prefixWord ++ tailWord_2801568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2801568).length < 2 ^ (prefixWord ++ tailWord_2801568).sum := by decide
  have hdescent : baseEnd_2801568 < baseStart_2801568 := by decide
  rcases family_descends (prefixWord ++ tailWord_2801568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2801572 : List Nat := [2, 3, 1, 2, 1, 3, 2, 2, 1, 4, 2]
def baseStart_2801572 : Nat := 118140960795 + 2801572 * 2 ^ 59
def prefixEnd_2801572 : Nat := 4983230072969 + 3 ^ 40 * 2801572 * 2
def baseEnd_2801572 : Nat := 1438553024178018070365811

theorem tailTrace_2801572 : CollatzResearch.WordTrace tailWord_2801572 prefixEnd_2801572 1438553024178018070365811 := by
  unfold tailWord_2801572
  simp only [CollatzResearch.WordTrace]
  refine ⟨51090862703195294624867485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68121150270927059499823313 51090862703195294624867485)
  ·
    refine ⟨19159073513698235484325307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51090862703195294624867485 19159073513698235484325307)
    ·
      refine ⟨28738610270547353226487961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19159073513698235484325307 28738610270547353226487961)
      ·
        refine ⟨21553957702910514919865971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28738610270547353226487961 21553957702910514919865971)
        ·
          refine ⟨32330936554365772379798957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21553957702910514919865971 32330936554365772379798957)
          ·
            refine ⟨12124101207887164642424609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32330936554365772379798957 12124101207887164642424609)
            ·
              refine ⟨9093075905915373481818457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12124101207887164642424609 9093075905915373481818457)
              ·
                refine ⟨6819806929436530111363843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9093075905915373481818457 6819806929436530111363843)
                ·
                  refine ⟨10229710394154795167045765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6819806929436530111363843 10229710394154795167045765)
                  ·
                    refine ⟨1918070698904024093821081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10229710394154795167045765 1918070698904024093821081)
                    ·
                      refine ⟨1438553024178018070365811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1918070698904024093821081 1438553024178018070365811)
                      ·
                        rfl

theorem cell23_2801572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 2, 2, 1, 4, 2].length) (baseStart_2801572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2801572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2801572 prefixEnd_2801572 := by exact prefixLift 2801572
  have htrace : WordTrace (prefixWord ++ tailWord_2801572) baseStart_2801572 baseEnd_2801572 := by
    simpa [prefixWord, tailWord_2801572, baseEnd_2801572] using wordTrace_append hprefix tailTrace_2801572
  have hstable : (prefixWord ++ tailWord_2801572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2801572).length < 2 ^ (prefixWord ++ tailWord_2801572).sum := by decide
  have hdescent : baseEnd_2801572 < baseStart_2801572 := by decide
  rcases family_descends (prefixWord ++ tailWord_2801572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2801585 : List Nat := [1, 2, 2, 4, 2, 1, 1, 2, 2, 2, 4]
def baseStart_2801585 : Nat := 118140960795 + 2801585 * 2 ^ 59
def prefixEnd_2801585 : Nat := 4983230072969 + 3 ^ 40 * 2801585 * 2
def baseEnd_2801585 : Nat := 1438559699426526519503251

theorem tailTrace_2801585 : CollatzResearch.WordTrace tailWord_2801585 prefixEnd_2801585 1438559699426526519503251 := by
  unfold tailWord_2801585
  simp only [CollatzResearch.WordTrace]
  refine ⟨102182199555343492469958209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68121466370228994979972139 102182199555343492469958209)
  ·
    refine ⟨76636649666507619352468657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102182199555343492469958209 76636649666507619352468657)
    ·
      refine ⟨57477487249880714514351493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76636649666507619352468657 57477487249880714514351493)
      ·
        refine ⟨10777028859352633971440905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 57477487249880714514351493 10777028859352633971440905)
        ·
          refine ⟨8082771644514475478580679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10777028859352633971440905 8082771644514475478580679)
          ·
            refine ⟨12124157466771713217871019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8082771644514475478580679 12124157466771713217871019)
            ·
              refine ⟨18186236200157569826806529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12124157466771713217871019 18186236200157569826806529)
              ·
                refine ⟨13639677150118177370104897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18186236200157569826806529 13639677150118177370104897)
                ·
                  refine ⟨10229757862588633027578673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13639677150118177370104897 10229757862588633027578673)
                  ·
                    refine ⟨7672318396941474770684005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10229757862588633027578673 7672318396941474770684005)
                    ·
                      refine ⟨1438559699426526519503251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7672318396941474770684005 1438559699426526519503251)
                      ·
                        rfl

theorem cell23_2801585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 1, 2, 2, 2, 4].length) (baseStart_2801585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2801585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2801585 prefixEnd_2801585 := by exact prefixLift 2801585
  have htrace : WordTrace (prefixWord ++ tailWord_2801585) baseStart_2801585 baseEnd_2801585 := by
    simpa [prefixWord, tailWord_2801585, baseEnd_2801585] using wordTrace_append hprefix tailTrace_2801585
  have hstable : (prefixWord ++ tailWord_2801585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2801585).length < 2 ^ (prefixWord ++ tailWord_2801585).sum := by decide
  have hdescent : baseEnd_2801585 < baseStart_2801585 := by decide
  rcases family_descends (prefixWord ++ tailWord_2801585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2801589 : List Nat := [1, 3, 3, 2, 1, 3, 1, 1, 4, 2, 2]
def baseStart_2801589 : Nat := 118140960795 + 2801589 * 2 ^ 59
def prefixEnd_2801589 : Nat := 4983230072969 + 3 ^ 40 * 2801589 * 2
def baseEnd_2801589 : Nat := 1438561753349144503853233

theorem tailTrace_2801589 : CollatzResearch.WordTrace tailWord_2801589 prefixEnd_2801589 1438561753349144503853233 := by
  unfold tailWord_2801589
  simp only [CollatzResearch.WordTrace]
  refine ⟨102182345447329001153103821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68121563631552667435402547 102182345447329001153103821)
  ·
    refine ⟨38318379542748375432413933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 102182345447329001153103821 38318379542748375432413933)
    ·
      refine ⟨14369392328530640787155225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38318379542748375432413933 14369392328530640787155225)
      ·
        refine ⟨10777044246397980590366419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14369392328530640787155225 10777044246397980590366419)
        ·
          refine ⟨16165566369596970885549629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10777044246397980590366419 16165566369596970885549629)
          ·
            refine ⟨6062087388598864082081111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16165566369596970885549629 6062087388598864082081111)
            ·
              refine ⟨9093131082898296123121667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6062087388598864082081111 9093131082898296123121667)
              ·
                refine ⟨13639696624347444184682501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9093131082898296123121667 13639696624347444184682501)
                ·
                  refine ⟨2557443117065145784627969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13639696624347444184682501 2557443117065145784627969)
                  ·
                    refine ⟨1918082337798859338470977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2557443117065145784627969 1918082337798859338470977)
                    ·
                      refine ⟨1438561753349144503853233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1918082337798859338470977 1438561753349144503853233)
                      ·
                        rfl

theorem cell23_2801589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 3, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 3, 1, 1, 4, 2, 2].length) (baseStart_2801589 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2801589 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2801589 prefixEnd_2801589 := by exact prefixLift 2801589
  have htrace : WordTrace (prefixWord ++ tailWord_2801589) baseStart_2801589 baseEnd_2801589 := by
    simpa [prefixWord, tailWord_2801589, baseEnd_2801589] using wordTrace_append hprefix tailTrace_2801589
  have hstable : (prefixWord ++ tailWord_2801589).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2801589).length < 2 ^ (prefixWord ++ tailWord_2801589).sum := by decide
  have hdescent : baseEnd_2801589 < baseStart_2801589 := by decide
  rcases family_descends (prefixWord ++ tailWord_2801589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2801706 : List Nat := [3, 1, 4, 1, 2, 2, 1, 4, 1, 4]
def baseStart_2801706 : Nat := 118140960795 + 2801706 * 2 ^ 59
def prefixEnd_2801706 : Nat := 4983230072969 + 3 ^ 40 * 2801706 * 2
def baseEnd_2801706 : Nat := 479540610195240182030065

theorem tailTrace_2801706 : CollatzResearch.WordTrace tailWord_2801706 prefixEnd_2801706 479540610195240182030065 := by
  unfold tailWord_2801706
  simp only [CollatzResearch.WordTrace]
  refine ⟨25546653196976282533778243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68124408525270086756741981 25546653196976282533778243)
  ·
    refine ⟨38319979795464423800667365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25546653196976282533778243 38319979795464423800667365)
    ·
      refine ⟨7184996211649579462625131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 38319979795464423800667365 7184996211649579462625131)
      ·
        refine ⟨10777494317474369193937697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7184996211649579462625131 10777494317474369193937697)
        ·
          refine ⟨8083120738105776895453273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10777494317474369193937697 8083120738105776895453273)
          ·
            refine ⟨6062340553579332671589955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8083120738105776895453273 6062340553579332671589955)
            ·
              refine ⟨9093510830368999007384933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6062340553579332671589955 9093510830368999007384933)
              ·
                refine ⟨1705033280694187313884675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9093510830368999007384933 1705033280694187313884675)
                ·
                  refine ⟨2557549921041280970827013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1705033280694187313884675 2557549921041280970827013)
                  ·
                    refine ⟨479540610195240182030065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2557549921041280970827013 479540610195240182030065)
                    ·
                      rfl

theorem cell23_2801706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 2, 1, 4, 1, 4].length) (baseStart_2801706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2801706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2801706 prefixEnd_2801706 := by exact prefixLift 2801706
  have htrace : WordTrace (prefixWord ++ tailWord_2801706) baseStart_2801706 baseEnd_2801706 := by
    simpa [prefixWord, tailWord_2801706, baseEnd_2801706] using wordTrace_append hprefix tailTrace_2801706
  have hstable : (prefixWord ++ tailWord_2801706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2801706).length < 2 ^ (prefixWord ++ tailWord_2801706).sum := by decide
  have hdescent : baseEnd_2801706 < baseStart_2801706 := by decide
  rcases family_descends (prefixWord ++ tailWord_2801706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2801715 : List Nat := [1, 1, 1, 2, 4, 1, 3, 2, 3, 5]
def baseStart_2801715 : Nat := 118140960795 + 2801715 * 2 ^ 59
def prefixEnd_2801715 : Nat := 4983230072969 + 3 ^ 40 * 2801715 * 2
def baseEnd_2801715 : Nat := 479542150637203670292551

theorem tailTrace_2801715 : CollatzResearch.WordTrace tailWord_2801715 prefixEnd_2801715 479542150637203670292551 := by
  unfold tailWord_2801715
  simp only [CollatzResearch.WordTrace]
  refine ⟨102186941044872524672190599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68124627363248349781460399 102186941044872524672190599)
  ·
    refine ⟨153280411567308787008285899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102186941044872524672190599 153280411567308787008285899)
    ·
      refine ⟨229920617350963180512428849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 153280411567308787008285899 229920617350963180512428849)
      ·
        refine ⟨172440463013222385384321637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 229920617350963180512428849 172440463013222385384321637)
        ·
          refine ⟨32332586814979197259560307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 172440463013222385384321637 32332586814979197259560307)
          ·
            refine ⟨48498880222468795889340461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32332586814979197259560307 48498880222468795889340461)
            ·
              refine ⟨18187080083425798458502673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 48498880222468795889340461 18187080083425798458502673)
              ·
                refine ⟨13640310062569348843877005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18187080083425798458502673 13640310062569348843877005)
                ·
                  refine ⟨5115116273463505816453877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13640310062569348843877005 5115116273463505816453877)
                  ·
                    refine ⟨479542150637203670292551, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5115116273463505816453877 479542150637203670292551)
                    ·
                      rfl

theorem cell23_2801715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 3, 2, 3, 5].length) (baseStart_2801715 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2801715 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2801715 prefixEnd_2801715 := by exact prefixLift 2801715
  have htrace : WordTrace (prefixWord ++ tailWord_2801715) baseStart_2801715 baseEnd_2801715 := by
    simpa [prefixWord, tailWord_2801715, baseEnd_2801715] using wordTrace_append hprefix tailTrace_2801715
  have hstable : (prefixWord ++ tailWord_2801715).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2801715).length < 2 ^ (prefixWord ++ tailWord_2801715).sum := by decide
  have hdescent : baseEnd_2801715 < baseStart_2801715 := by decide
  rcases family_descends (prefixWord ++ tailWord_2801715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2801722 : List Nat := [3, 1, 1, 1, 3, 1, 1, 4, 1, 5, 2]
def baseStart_2801722 : Nat := 118140960795 + 2801722 * 2 ^ 59
def prefixEnd_2801722 : Nat := 4983230072969 + 3 ^ 40 * 2801722 * 2
def baseEnd_2801722 : Nat := 1438630046276192483490121

theorem tailTrace_2801722 : CollatzResearch.WordTrace tailWord_2801722 prefixEnd_2801722 1438630046276192483490121 := by
  unfold tailWord_2801722
  simp only [CollatzResearch.WordTrace]
  refine ⟨25546799088961791216923855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68124797570564776578463613 25546799088961791216923855)
  ·
    refine ⟨38320198633442686825385783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25546799088961791216923855 38320198633442686825385783)
    ·
      refine ⟨57480297950164030238078675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38320198633442686825385783 57480297950164030238078675)
      ·
        refine ⟨86220446925246045357118013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57480297950164030238078675 86220446925246045357118013)
        ·
          refine ⟨32332667596967267008919255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 86220446925246045357118013 32332667596967267008919255)
          ·
            refine ⟨48499001395450900513378883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32332667596967267008919255 48499001395450900513378883)
            ·
              refine ⟨72748502093176350770068325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48499001395450900513378883 72748502093176350770068325)
              ·
                refine ⟨13640344142470565769387811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 72748502093176350770068325 13640344142470565769387811)
                ·
                  refine ⟨20460516213705848654081717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13640344142470565769387811 20460516213705848654081717)
                  ·
                    refine ⟨1918173395034923311320161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 20460516213705848654081717 1918173395034923311320161)
                    ·
                      refine ⟨1438630046276192483490121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1918173395034923311320161 1438630046276192483490121)
                      ·
                        rfl

theorem cell23_2801722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 4, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 4, 1, 5, 2].length) (baseStart_2801722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2801722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2801722 prefixEnd_2801722 := by exact prefixLift 2801722
  have htrace : WordTrace (prefixWord ++ tailWord_2801722) baseStart_2801722 baseEnd_2801722 := by
    simpa [prefixWord, tailWord_2801722, baseEnd_2801722] using wordTrace_append hprefix tailTrace_2801722
  have hstable : (prefixWord ++ tailWord_2801722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2801722).length < 2 ^ (prefixWord ++ tailWord_2801722).sum := by decide
  have hdescent : baseEnd_2801722 < baseStart_2801722 := by decide
  rcases family_descends (prefixWord ++ tailWord_2801722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2801725 : List Nat := [1, 4, 1, 3, 1, 1, 1, 1, 2, 1, 7]
def baseStart_2801725 : Nat := 118140960795 + 2801725 * 2 ^ 59
def prefixEnd_2801725 : Nat := 4983230072969 + 3 ^ 40 * 2801725 * 2
def baseEnd_2801725 : Nat := 1438631586718155971752607

theorem tailTrace_2801725 : CollatzResearch.WordTrace tailWord_2801725 prefixEnd_2801725 1438631586718155971752607 := by
  unfold tailWord_2801725
  simp only [CollatzResearch.WordTrace]
  refine ⟨102187305774836296380054629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68124870516557530920036419 102187305774836296380054629)
  ·
    refine ⟨19160119832781805571260243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 102187305774836296380054629 19160119832781805571260243)
    ·
      refine ⟨28740179749172708356890365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19160119832781805571260243 28740179749172708356890365)
      ·
        refine ⟨10777567405939765633833887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28740179749172708356890365 10777567405939765633833887)
        ·
          refine ⟨16166351108909648450750831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10777567405939765633833887 16166351108909648450750831)
          ·
            refine ⟨24249526663364472676126247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16166351108909648450750831 24249526663364472676126247)
            ·
              refine ⟨36374289995046709014189371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24249526663364472676126247 36374289995046709014189371)
              ·
                refine ⟨54561434992570063521284057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36374289995046709014189371 54561434992570063521284057)
                ·
                  refine ⟨40921076244427547640963043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 54561434992570063521284057 40921076244427547640963043)
                  ·
                    refine ⟨61381614366641321461444565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 40921076244427547640963043 61381614366641321461444565)
                    ·
                      refine ⟨1438631586718155971752607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 61381614366641321461444565 1438631586718155971752607)
                      ·
                        rfl

theorem cell23_2801725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 1, 1, 2, 1, 7].length) (baseStart_2801725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2801725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2801725 prefixEnd_2801725 := by exact prefixLift 2801725
  have htrace : WordTrace (prefixWord ++ tailWord_2801725) baseStart_2801725 baseEnd_2801725 := by
    simpa [prefixWord, tailWord_2801725, baseEnd_2801725] using wordTrace_append hprefix tailTrace_2801725
  have hstable : (prefixWord ++ tailWord_2801725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2801725).length < 2 ^ (prefixWord ++ tailWord_2801725).sum := by decide
  have hdescent : baseEnd_2801725 < baseStart_2801725 := by decide
  rcases family_descends (prefixWord ++ tailWord_2801725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2801729 : List Nat := [1, 2, 5, 1, 2, 1, 1, 1, 5, 1, 3]
def baseStart_2801729 : Nat := 118140960795 + 2801729 * 2 ^ 59
def prefixEnd_2801729 : Nat := 4983230072969 + 3 ^ 40 * 2801729 * 2
def baseEnd_2801729 : Nat := 1438633640640773956102589

theorem tailTrace_2801729 : CollatzResearch.WordTrace tailWord_2801729 prefixEnd_2801729 1438633640640773956102589 := by
  unfold tailWord_2801729
  simp only [CollatzResearch.WordTrace]
  refine ⟨102187451666821805063200241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68124967777881203375466827 102187451666821805063200241)
  ·
    refine ⟨76640588750116353797400181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102187451666821805063200241 76640588750116353797400181)
    ·
      refine ⟨7185055195323408168506267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 76640588750116353797400181 7185055195323408168506267)
      ·
        refine ⟨10777582792985112252759401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7185055195323408168506267 10777582792985112252759401)
        ·
          refine ⟨8083187094738834189569551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10777582792985112252759401 8083187094738834189569551)
          ·
            refine ⟨12124780642108251284354327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8083187094738834189569551 12124780642108251284354327)
            ·
              refine ⟨18187170963162376926531491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12124780642108251284354327 18187170963162376926531491)
              ·
                refine ⟨27280756444743565389797237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18187170963162376926531491 27280756444743565389797237)
                ·
                  refine ⟨2557570916694709255293491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 27280756444743565389797237 2557570916694709255293491)
                  ·
                    refine ⟨3836356375042063882940237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2557570916694709255293491 3836356375042063882940237)
                    ·
                      refine ⟨1438633640640773956102589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3836356375042063882940237 1438633640640773956102589)
                      ·
                        rfl

theorem cell23_2801729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 1, 1, 5, 1, 3].length) (baseStart_2801729 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2801729 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2801729 prefixEnd_2801729 := by exact prefixLift 2801729
  have htrace : WordTrace (prefixWord ++ tailWord_2801729) baseStart_2801729 baseEnd_2801729 := by
    simpa [prefixWord, tailWord_2801729, baseEnd_2801729] using wordTrace_append hprefix tailTrace_2801729
  have hstable : (prefixWord ++ tailWord_2801729).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2801729).length < 2 ^ (prefixWord ++ tailWord_2801729).sum := by decide
  have hdescent : baseEnd_2801729 < baseStart_2801729 := by decide
  rcases family_descends (prefixWord ++ tailWord_2801729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2801749 : List Nat := [1, 3, 2, 2, 1, 3, 4, 1, 1, 5]
def baseStart_2801749 : Nat := 118140960795 + 2801749 * 2 ^ 59
def prefixEnd_2801749 : Nat := 4983230072969 + 3 ^ 40 * 2801749 * 2
def baseEnd_2801749 : Nat := 479547970084621292617499

theorem tailTrace_2801749 : CollatzResearch.WordTrace tailWord_2801749 prefixEnd_2801749 479547970084621292617499 := by
  unfold tailWord_2801749
  simp only [CollatzResearch.WordTrace]
  refine ⟨102188181126749348478928301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68125454084499565652618867 102188181126749348478928301)
  ·
    refine ⟨38320567922531005679598113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 102188181126749348478928301 38320567922531005679598113)
    ·
      refine ⟨28740425941898254259698585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38320567922531005679598113 28740425941898254259698585)
      ·
        refine ⟨21555319456423690694773939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28740425941898254259698585 21555319456423690694773939)
        ·
          refine ⟨32332979184635536042160909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21555319456423690694773939 32332979184635536042160909)
          ·
            refine ⟨12124867194238326015810341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32332979184635536042160909 12124867194238326015810341)
            ·
              refine ⟨2273412598919686127964439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12124867194238326015810341 2273412598919686127964439)
              ·
                refine ⟨3410118898379529191946659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2273412598919686127964439 3410118898379529191946659)
                ·
                  refine ⟨5115178347569293787919989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3410118898379529191946659 5115178347569293787919989)
                  ·
                    refine ⟨479547970084621292617499, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5115178347569293787919989 479547970084621292617499)
                    ·
                      rfl

theorem cell23_2801749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 4, 1, 1, 5].length) (baseStart_2801749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2801749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2801749 prefixEnd_2801749 := by exact prefixLift 2801749
  have htrace : WordTrace (prefixWord ++ tailWord_2801749) baseStart_2801749 baseEnd_2801749 := by
    simpa [prefixWord, tailWord_2801749, baseEnd_2801749] using wordTrace_append hprefix tailTrace_2801749
  have hstable : (prefixWord ++ tailWord_2801749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2801749).length < 2 ^ (prefixWord ++ tailWord_2801749).sum := by decide
  have hdescent : baseEnd_2801749 < baseStart_2801749 := by decide
  rcases family_descends (prefixWord ++ tailWord_2801749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2801772 : List Nat := [2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 5]
def baseStart_2801772 : Nat := 118140960795 + 2801772 * 2 ^ 59
def prefixEnd_2801772 : Nat := 4983230072969 + 3 ^ 40 * 2801772 * 2
def baseEnd_2801772 : Nat := 1438655720308917287864891

theorem tailTrace_2801772 : CollatzResearch.WordTrace tailWord_2801772 prefixEnd_2801772 1438655720308917287864891 := by
  unfold tailWord_2801772
  simp only [CollatzResearch.WordTrace]
  refine ⟨51094510002833011703507785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68126013337110682271343713 51094510002833011703507785)
  ·
    refine ⟨38320882502124758777630839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51094510002833011703507785 38320882502124758777630839)
    ·
      refine ⟨57481323753187138166446259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38320882502124758777630839 57481323753187138166446259)
      ·
        refine ⟨86221985629780707249669389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57481323753187138166446259 86221985629780707249669389)
        ·
          refine ⟨32333244611167765218626021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 86221985629780707249669389 32333244611167765218626021)
          ·
            refine ⟨6062483364593955978492379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 32333244611167765218626021 6062483364593955978492379)
            ·
              refine ⟨9093725046890933967738569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6062483364593955978492379 9093725046890933967738569)
              ·
                refine ⟨6820293785168200475803927, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9093725046890933967738569 6820293785168200475803927)
                ·
                  refine ⟨10230440677752300713705891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6820293785168200475803927 10230440677752300713705891)
                  ·
                    refine ⟨15345661016628451070558837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10230440677752300713705891 15345661016628451070558837)
                    ·
                      refine ⟨1438655720308917287864891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15345661016628451070558837 1438655720308917287864891)
                      ·
                        rfl

theorem cell23_2801772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 5].length) (baseStart_2801772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2801772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2801772 prefixEnd_2801772 := by exact prefixLift 2801772
  have htrace : WordTrace (prefixWord ++ tailWord_2801772) baseStart_2801772 baseEnd_2801772 := by
    simpa [prefixWord, tailWord_2801772, baseEnd_2801772] using wordTrace_append hprefix tailTrace_2801772
  have hstable : (prefixWord ++ tailWord_2801772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2801772).length < 2 ^ (prefixWord ++ tailWord_2801772).sum := by decide
  have hdescent : baseEnd_2801772 < baseStart_2801772 := by decide
  rcases family_descends (prefixWord ++ tailWord_2801772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2801789 : List Nat := [1, 4, 1, 1, 3, 2, 1, 4, 1, 2, 3]
def baseStart_2801789 : Nat := 118140960795 + 2801789 * 2 ^ 59
def prefixEnd_2801789 : Nat := 4983230072969 + 3 ^ 40 * 2801789 * 2
def baseEnd_2801789 : Nat := 1438664449480043721352313

theorem tailTrace_2801789 : CollatzResearch.WordTrace tailWord_2801789 prefixEnd_2801789 1438664449480043721352313 := by
  unfold tailWord_2801789
  simp only [CollatzResearch.WordTrace]
  refine ⟨102189640046604435310384421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68126426697736290206922947 102189640046604435310384421)
  ·
    refine ⟨19160557508738331620697079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 102189640046604435310384421 19160557508738331620697079)
    ·
      refine ⟨28740836263107497431045619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19160557508738331620697079 28740836263107497431045619)
      ·
        refine ⟨43111254394661246146568429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28740836263107497431045619 43111254394661246146568429)
        ·
          refine ⟨16166720397997967304963161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43111254394661246146568429 16166720397997967304963161)
          ·
            refine ⟨12125040298498475478722371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16166720397997967304963161 12125040298498475478722371)
            ·
              refine ⟨18187560447747713218083557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12125040298498475478722371 18187560447747713218083557)
              ·
                refine ⟨3410167583952696228390667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18187560447747713218083557 3410167583952696228390667)
                ·
                  refine ⟨5115251375929044342586001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3410167583952696228390667 5115251375929044342586001)
                  ·
                    refine ⟨3836438531946783256939501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5115251375929044342586001 3836438531946783256939501)
                    ·
                      refine ⟨1438664449480043721352313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3836438531946783256939501 1438664449480043721352313)
                      ·
                        rfl

theorem cell23_2801789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 1, 4, 1, 2, 3].length) (baseStart_2801789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2801789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2801789 prefixEnd_2801789 := by exact prefixLift 2801789
  have htrace : WordTrace (prefixWord ++ tailWord_2801789) baseStart_2801789 baseEnd_2801789 := by
    simpa [prefixWord, tailWord_2801789, baseEnd_2801789] using wordTrace_append hprefix tailTrace_2801789
  have hstable : (prefixWord ++ tailWord_2801789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2801789).length < 2 ^ (prefixWord ++ tailWord_2801789).sum := by decide
  have hdescent : baseEnd_2801789 < baseStart_2801789 := by decide
  rcases family_descends (prefixWord ++ tailWord_2801789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2801814 : List Nat := [5, 3, 2, 1, 1, 2, 1, 1, 3, 1, 3]
def baseStart_2801814 : Nat := 118140960795 + 2801814 * 2 ^ 59
def prefixEnd_2801814 : Nat := 4983230072969 + 3 ^ 40 * 2801814 * 2
def baseEnd_2801814 : Nat := 1438677286496406123539699

theorem tailTrace_2801814 : CollatzResearch.WordTrace tailWord_2801814 prefixEnd_2801814 1438677286496406123539699 := by
  unfold tailWord_2801814
  simp only [CollatzResearch.WordTrace]
  refine ⟨6386909491969616536252781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 68127034581009243053362997 6386909491969616536252781)
  ·
    refine ⟨2395091059488606201094793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6386909491969616536252781 2395091059488606201094793)
    ·
      refine ⟨1796318294616454650821095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2395091059488606201094793 1796318294616454650821095)
      ·
        refine ⟨2694477441924681976231643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1796318294616454650821095 2694477441924681976231643)
        ·
          refine ⟨4041716162887022964347465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2694477441924681976231643 4041716162887022964347465)
          ·
            refine ⟨3031287122165267223260599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4041716162887022964347465 3031287122165267223260599)
            ·
              refine ⟨4546930683247900834890899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3031287122165267223260599 4546930683247900834890899)
              ·
                refine ⟨6820396024871851252336349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4546930683247900834890899 6820396024871851252336349)
                ·
                  refine ⟨2557648509326944219626131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6820396024871851252336349 2557648509326944219626131)
                  ·
                    refine ⟨3836472763990416329439197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2557648509326944219626131 3836472763990416329439197)
                    ·
                      refine ⟨1438677286496406123539699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3836472763990416329439197 1438677286496406123539699)
                      ·
                        rfl

theorem cell23_2801814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 2, 1, 1, 3, 1, 3].length) (baseStart_2801814 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2801814 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2801814 prefixEnd_2801814 := by exact prefixLift 2801814
  have htrace : WordTrace (prefixWord ++ tailWord_2801814) baseStart_2801814 baseEnd_2801814 := by
    simpa [prefixWord, tailWord_2801814, baseEnd_2801814] using wordTrace_append hprefix tailTrace_2801814
  have hstable : (prefixWord ++ tailWord_2801814).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2801814).length < 2 ^ (prefixWord ++ tailWord_2801814).sum := by decide
  have hdescent : baseEnd_2801814 < baseStart_2801814 := by decide
  rcases family_descends (prefixWord ++ tailWord_2801814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2801820 : List Nat := [2, 2, 3, 2, 1, 1, 5, 2, 1, 2, 2]
def baseStart_2801820 : Nat := 118140960795 + 2801820 * 2 ^ 59
def prefixEnd_2801820 : Nat := 4983230072969 + 3 ^ 40 * 2801820 * 2
def baseEnd_2801820 : Nat := 1438680367380333100064671

theorem tailTrace_2801820 : CollatzResearch.WordTrace tailWord_2801820 prefixEnd_2801820 1438680367380333100064671 := by
  unfold tailWord_2801820
  simp only [CollatzResearch.WordTrace]
  refine ⟨51095385354746063802381457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68127180472994751736508609 51095385354746063802381457)
  ·
    refine ⟨38321539016059547851786093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51095385354746063802381457 38321539016059547851786093)
    ·
      refine ⟨14370577131022330444419785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38321539016059547851786093 14370577131022330444419785)
      ·
        refine ⟨10777932848266747833314839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14370577131022330444419785 10777932848266747833314839)
        ·
          refine ⟨16166899272400121749972259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10777932848266747833314839 16166899272400121749972259)
          ·
            refine ⟨24250348908600182624958389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16166899272400121749972259 24250348908600182624958389)
            ·
              refine ⟨2273470210181267121089849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 24250348908600182624958389 2273470210181267121089849)
              ·
                refine ⟨1705102657635950340817387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2273470210181267121089849 1705102657635950340817387)
                ·
                  refine ⟨2557653986453925511226081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1705102657635950340817387 2557653986453925511226081)
                  ·
                    refine ⟨1918240489840444133419561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2557653986453925511226081 1918240489840444133419561)
                    ·
                      refine ⟨1438680367380333100064671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1918240489840444133419561 1438680367380333100064671)
                      ·
                        rfl

theorem cell23_2801820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 5, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 5, 2, 1, 2, 2].length) (baseStart_2801820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2801820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2801820 prefixEnd_2801820 := by exact prefixLift 2801820
  have htrace : WordTrace (prefixWord ++ tailWord_2801820) baseStart_2801820 baseEnd_2801820 := by
    simpa [prefixWord, tailWord_2801820, baseEnd_2801820] using wordTrace_append hprefix tailTrace_2801820
  have hstable : (prefixWord ++ tailWord_2801820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2801820).length < 2 ^ (prefixWord ++ tailWord_2801820).sum := by decide
  have hdescent : baseEnd_2801820 < baseStart_2801820 := by decide
  rcases family_descends (prefixWord ++ tailWord_2801820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2801829 : List Nat := [1, 3, 1, 2, 1, 3, 2, 2, 3, 3, 2]
def baseStart_2801829 : Nat := 118140960795 + 2801829 * 2 ^ 59
def prefixEnd_2801829 : Nat := 4983230072969 + 3 ^ 40 * 2801829 * 2
def baseEnd_2801829 : Nat := 1438684988706223564852129

theorem tailTrace_2801829 : CollatzResearch.WordTrace tailWord_2801829 prefixEnd_2801829 1438684988706223564852129 := by
  unfold tailWord_2801829
  simp only [CollatzResearch.WordTrace]
  refine ⟨102191098966459522141840541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68127399310973014761227027 102191098966459522141840541)
  ·
    refine ⟨38321662112422320803190203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 102191098966459522141840541 38321662112422320803190203)
    ·
      refine ⟨57482493168633481204785305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38321662112422320803190203 57482493168633481204785305)
      ·
        refine ⟨43111869876475110903588979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57482493168633481204785305 43111869876475110903588979)
        ·
          refine ⟨64667804814712666355383469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43111869876475110903588979 64667804814712666355383469)
          ·
            refine ⟨24250426805517249883268801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 64667804814712666355383469 24250426805517249883268801)
            ·
              refine ⟨18187820104137937412451601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24250426805517249883268801 18187820104137937412451601)
              ·
                refine ⟨13640865078103453059338701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18187820104137937412451601 13640865078103453059338701)
                ·
                  refine ⟨5115324404288794897252013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13640865078103453059338701 5115324404288794897252013)
                  ·
                    refine ⟨1918246651608298086469505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5115324404288794897252013 1918246651608298086469505)
                    ·
                      refine ⟨1438684988706223564852129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1918246651608298086469505 1438684988706223564852129)
                      ·
                        rfl

theorem cell23_2801829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 2, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 2, 2, 3, 3, 2].length) (baseStart_2801829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2801829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2801829 prefixEnd_2801829 := by exact prefixLift 2801829
  have htrace : WordTrace (prefixWord ++ tailWord_2801829) baseStart_2801829 baseEnd_2801829 := by
    simpa [prefixWord, tailWord_2801829, baseEnd_2801829] using wordTrace_append hprefix tailTrace_2801829
  have hstable : (prefixWord ++ tailWord_2801829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2801829).length < 2 ^ (prefixWord ++ tailWord_2801829).sum := by decide
  have hdescent : baseEnd_2801829 < baseStart_2801829 := by decide
  rcases family_descends (prefixWord ++ tailWord_2801829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2801835 : List Nat := [1, 1, 1, 1, 2, 1, 1, 1, 8, 6]
def baseStart_2801835 : Nat := 118140960795 + 2801835 * 2 ^ 59
def prefixEnd_2801835 : Nat := 4983230072969 + 3 ^ 40 * 2801835 * 2
def baseEnd_2801835 : Nat := 479562689863383513792367

theorem tailTrace_2801835 : CollatzResearch.WordTrace tailWord_2801835 prefixEnd_2801835 479562689863383513792367 := by
  unfold tailWord_2801835
  simp only [CollatzResearch.WordTrace]
  refine ⟨102191317804437785166558959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68127545202958523444372639 102191317804437785166558959)
  ·
    refine ⟨153286976706656677749838439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102191317804437785166558959 153286976706656677749838439)
    ·
      refine ⟨229930465059985016624757659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 153286976706656677749838439 229930465059985016624757659)
      ·
        refine ⟨344895697589977524937136489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 229930465059985016624757659 344895697589977524937136489)
        ·
          refine ⟨258671773192483143702852367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 344895697589977524937136489 258671773192483143702852367)
          ·
            refine ⟨388007659788724715554278551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 258671773192483143702852367 388007659788724715554278551)
            ·
              refine ⟨582011489683087073331417827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 388007659788724715554278551 582011489683087073331417827)
              ·
                refine ⟨873017234524630609997126741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 582011489683087073331417827 873017234524630609997126741)
                ·
                  refine ⟨10230670717085514960903829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 873017234524630609997126741 10230670717085514960903829)
                  ·
                    refine ⟨479562689863383513792367, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10230670717085514960903829 479562689863383513792367)
                    ·
                      rfl

theorem cell23_2801835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 8, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 8, 6].length) (baseStart_2801835 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2801835 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2801835 prefixEnd_2801835 := by exact prefixLift 2801835
  have htrace : WordTrace (prefixWord ++ tailWord_2801835) baseStart_2801835 baseEnd_2801835 := by
    simpa [prefixWord, tailWord_2801835, baseEnd_2801835] using wordTrace_append hprefix tailTrace_2801835
  have hstable : (prefixWord ++ tailWord_2801835).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2801835).length < 2 ^ (prefixWord ++ tailWord_2801835).sum := by decide
  have hdescent : baseEnd_2801835 < baseStart_2801835 := by decide
  rcases family_descends (prefixWord ++ tailWord_2801835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2801865 : List Nat := [1, 2, 1, 1, 2, 1, 1, 3, 11]
def baseStart_2801865 : Nat := 118140960795 + 2801865 * 2 ^ 59
def prefixEnd_2801865 : Nat := 4983230072969 + 3 ^ 40 * 2801865 * 2
def baseEnd_2801865 : Nat := 159855941556642824889107

theorem tailTrace_2801865 : CollatzResearch.WordTrace tailWord_2801865 prefixEnd_2801865 159855941556642824889107 := by
  unfold tailWord_2801865
  simp only [CollatzResearch.WordTrace]
  refine ⟨102192411994329100290151049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68128274662886066860100699 102192411994329100290151049)
  ·
    refine ⟨76644308995746825217613287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102192411994329100290151049 76644308995746825217613287)
    ·
      refine ⟨114966463493620237826419931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76644308995746825217613287 114966463493620237826419931)
      ·
        refine ⟨172449695240430356739629897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114966463493620237826419931 172449695240430356739629897)
        ·
          refine ⟨129337271430322767554722423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 172449695240430356739629897 129337271430322767554722423)
          ·
            refine ⟨194005907145484151332083635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 129337271430322767554722423 194005907145484151332083635)
            ·
              refine ⟨291008860718226226998125453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 194005907145484151332083635 291008860718226226998125453)
              ·
                refine ⟨109128322769334835124297045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 291008860718226226998125453 109128322769334835124297045)
                ·
                  refine ⟨159855941556642824889107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 109128322769334835124297045 159855941556642824889107)
                  ·
                    rfl

theorem cell23_2801865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 3, 11].length) (baseStart_2801865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2801865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2801865 prefixEnd_2801865 := by exact prefixLift 2801865
  have htrace : WordTrace (prefixWord ++ tailWord_2801865) baseStart_2801865 baseEnd_2801865 := by
    simpa [prefixWord, tailWord_2801865, baseEnd_2801865] using wordTrace_append hprefix tailTrace_2801865
  have hstable : (prefixWord ++ tailWord_2801865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2801865).length < 2 ^ (prefixWord ++ tailWord_2801865).sum := by decide
  have hdescent : baseEnd_2801865 < baseStart_2801865 := by decide
  rcases family_descends (prefixWord ++ tailWord_2801865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2801893 : List Nat := [1, 3, 1, 4, 2, 1, 2, 3, 2, 2, 2]
def baseStart_2801893 : Nat := 118140960795 + 2801893 * 2 ^ 59
def prefixEnd_2801893 : Nat := 4983230072969 + 3 ^ 40 * 2801893 * 2
def baseEnd_2801893 : Nat := 1438717851468111314451835

theorem tailTrace_2801893 : CollatzResearch.WordTrace tailWord_2801893 prefixEnd_2801893 1438717851468111314451835 := by
  unfold tailWord_2801893
  simp only [CollatzResearch.WordTrace]
  refine ⟨102193433238227661072170333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68128955492151774048113555 102193433238227661072170333)
  ·
    refine ⟨38322537464335372902063875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 102193433238227661072170333 38322537464335372902063875)
    ·
      refine ⟨57483806196503059353095813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38322537464335372902063875 57483806196503059353095813)
      ·
        refine ⟨10778213661844323628705465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 57483806196503059353095813 10778213661844323628705465)
        ·
          refine ⟨8083660246383242721529099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10778213661844323628705465 8083660246383242721529099)
          ·
            refine ⟨12125490369574864082293649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8083660246383242721529099 12125490369574864082293649)
            ·
              refine ⟨9094117777181148061720237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12125490369574864082293649 9094117777181148061720237)
              ·
                refine ⟨3410294166442930523145089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9094117777181148061720237 3410294166442930523145089)
                ·
                  refine ⟨2557720624832197892358817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3410294166442930523145089 2557720624832197892358817)
                  ·
                    refine ⟨1918290468624148419269113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2557720624832197892358817 1918290468624148419269113)
                    ·
                      refine ⟨1438717851468111314451835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1918290468624148419269113 1438717851468111314451835)
                      ·
                        rfl

theorem cell23_2801893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 2, 3, 2, 2, 2].length) (baseStart_2801893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2801893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2801893 prefixEnd_2801893 := by exact prefixLift 2801893
  have htrace : WordTrace (prefixWord ++ tailWord_2801893) baseStart_2801893 baseEnd_2801893 := by
    simpa [prefixWord, tailWord_2801893, baseEnd_2801893] using wordTrace_append hprefix tailTrace_2801893
  have hstable : (prefixWord ++ tailWord_2801893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2801893).length < 2 ^ (prefixWord ++ tailWord_2801893).sum := by decide
  have hdescent : baseEnd_2801893 < baseStart_2801893 := by decide
  rcases family_descends (prefixWord ++ tailWord_2801893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2801916 : List Nat := [2, 2, 2, 1, 4, 2, 2, 3, 5]
def baseStart_2801916 : Nat := 118140960795 + 2801916 * 2 ^ 59
def prefixEnd_2801916 : Nat := 4983230072969 + 3 ^ 40 * 2801916 * 2
def baseEnd_2801916 : Nat := 159858851280351636051581

theorem tailTrace_2801916 : CollatzResearch.WordTrace tailWord_2801916 prefixEnd_2801916 159858851280351636051581 := by
  unfold tailWord_2801916
  simp only [CollatzResearch.WordTrace]
  refine ⟨51097136058572168000128801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68129514744762890666838401 51097136058572168000128801)
  ·
    refine ⟨38322852043929126000096601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51097136058572168000128801 38322852043929126000096601)
    ·
      refine ⟨28742139032946844500072451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38322852043929126000096601 28742139032946844500072451)
      ·
        refine ⟨43113208549420266750108677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28742139032946844500072451 43113208549420266750108677)
        ·
          refine ⟨8083726603016300015645377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 43113208549420266750108677 8083726603016300015645377)
          ·
            refine ⟨6062794952262225011734033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8083726603016300015645377 6062794952262225011734033)
            ·
              refine ⟨4547096214196668758800525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6062794952262225011734033 4547096214196668758800525)
              ·
                refine ⟨1705161080323750784550197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4547096214196668758800525 1705161080323750784550197)
                ·
                  refine ⟨159858851280351636051581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1705161080323750784550197 159858851280351636051581)
                  ·
                    rfl

theorem cell23_2801916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 2, 2, 3, 5].length) (baseStart_2801916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2801916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2801916 prefixEnd_2801916 := by exact prefixLift 2801916
  have htrace : WordTrace (prefixWord ++ tailWord_2801916) baseStart_2801916 baseEnd_2801916 := by
    simpa [prefixWord, tailWord_2801916, baseEnd_2801916] using wordTrace_append hprefix tailTrace_2801916
  have hstable : (prefixWord ++ tailWord_2801916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2801916).length < 2 ^ (prefixWord ++ tailWord_2801916).sum := by decide
  have hdescent : baseEnd_2801916 < baseStart_2801916 := by decide
  rcases family_descends (prefixWord ++ tailWord_2801916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2801927 : List Nat := [1, 1, 4, 5, 1, 2, 1, 2, 2, 2, 2]
def baseStart_2801927 : Nat := 118140960795 + 2801927 * 2 ^ 59
def prefixEnd_2801927 : Nat := 4983230072969 + 3 ^ 40 * 2801927 * 2
def baseEnd_2801927 : Nat := 1438735309810364181426679

theorem tailTrace_2801927 : CollatzResearch.WordTrace tailWord_2801927 prefixEnd_2801927 1438735309810364181426679 := by
  unfold tailWord_2801927
  simp only [CollatzResearch.WordTrace]
  refine ⟨102194673320104484878908035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68129782213402989919272023 102194673320104484878908035)
  ·
    refine ⟨153292009980156727318362053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102194673320104484878908035 153292009980156727318362053)
    ·
      refine ⟨28742251871279386372192885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 153292009980156727318362053 28742251871279386372192885)
      ·
        refine ⟨2694586112932442472393083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 28742251871279386372192885 2694586112932442472393083)
        ·
          refine ⟨4041879169398663708589625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2694586112932442472393083 4041879169398663708589625)
          ·
            refine ⟨3031409377048997781442219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4041879169398663708589625 3031409377048997781442219)
            ·
              refine ⟨4547114065573496672163329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3031409377048997781442219 4547114065573496672163329)
              ·
                refine ⟨3410335549180122504122497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4547114065573496672163329 3410335549180122504122497)
                ·
                  refine ⟨2557751661885091878091873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3410335549180122504122497 2557751661885091878091873)
                  ·
                    refine ⟨1918313746413818908568905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2557751661885091878091873 1918313746413818908568905)
                    ·
                      refine ⟨1438735309810364181426679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1918313746413818908568905 1438735309810364181426679)
                      ·
                        rfl

theorem cell23_2801927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 2, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 2, 1, 2, 2, 2, 2].length) (baseStart_2801927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2801927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2801927 prefixEnd_2801927 := by exact prefixLift 2801927
  have htrace : WordTrace (prefixWord ++ tailWord_2801927) baseStart_2801927 baseEnd_2801927 := by
    simpa [prefixWord, tailWord_2801927, baseEnd_2801927] using wordTrace_append hprefix tailTrace_2801927
  have hstable : (prefixWord ++ tailWord_2801927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2801927).length < 2 ^ (prefixWord ++ tailWord_2801927).sum := by decide
  have hdescent : baseEnd_2801927 < baseStart_2801927 := by decide
  rcases family_descends (prefixWord ++ tailWord_2801927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2801992 : List Nat := [2, 1, 3, 1, 1, 2, 2, 1, 1, 1, 8]
def baseStart_2801992 : Nat := 118140960795 + 2801992 * 2 ^ 59
def prefixEnd_2801992 : Nat := 4983230072969 + 3 ^ 40 * 2801992 * 2
def baseEnd_2801992 : Nat := 1438768686052906427113879

theorem tailTrace_2801992 : CollatzResearch.WordTrace tailWord_2801992 prefixEnd_2801992 1438768686052906427113879 := by
  unfold tailWord_2801992
  simp only [CollatzResearch.WordTrace]
  refine ⟨51098522032434500490012115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68131362709912667320016153 51098522032434500490012115)
  ·
    refine ⟨76647783048651750735018173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51098522032434500490012115 76647783048651750735018173)
    ·
      refine ⟨28742918643244406525631815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 76647783048651750735018173 28742918643244406525631815)
      ·
        refine ⟨43114377964866609788447723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28742918643244406525631815 43114377964866609788447723)
        ·
          refine ⟨64671566947299914682671585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43114377964866609788447723 64671566947299914682671585)
          ·
            refine ⟨48503675210474936012003689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64671566947299914682671585 48503675210474936012003689)
            ·
              refine ⟨36377756407856202009002767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48503675210474936012003689 36377756407856202009002767)
              ·
                refine ⟨54566634611784303013504151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36377756407856202009002767 54566634611784303013504151)
                ·
                  refine ⟨81849951917676454520256227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 54566634611784303013504151 81849951917676454520256227)
                  ·
                    refine ⟨122774927876514681780384341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 81849951917676454520256227 122774927876514681780384341)
                    ·
                      refine ⟨1438768686052906427113879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 122774927876514681780384341 1438768686052906427113879)
                      ·
                        rfl

theorem cell23_2801992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 2, 1, 1, 1, 8].length) (baseStart_2801992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2801992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2801992 prefixEnd_2801992 := by exact prefixLift 2801992
  have htrace : WordTrace (prefixWord ++ tailWord_2801992) baseStart_2801992 baseEnd_2801992 := by
    simpa [prefixWord, tailWord_2801992, baseEnd_2801992] using wordTrace_append hprefix tailTrace_2801992
  have hstable : (prefixWord ++ tailWord_2801992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2801992).length < 2 ^ (prefixWord ++ tailWord_2801992).sum := by decide
  have hdescent : baseEnd_2801992 < baseStart_2801992 := by decide
  rcases family_descends (prefixWord ++ tailWord_2801992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2802019 : List Nat := [1, 1, 1, 5, 2, 1, 3, 1, 3, 5]
def baseStart_2802019 : Nat := 118140960795 + 2802019 * 2 ^ 59
def prefixEnd_2802019 : Nat := 4983230072969 + 3 ^ 40 * 2802019 * 2
def baseEnd_2802019 : Nat := 479594183343525940492085

theorem tailTrace_2802019 : CollatzResearch.WordTrace tailWord_2802019 prefixEnd_2802019 479594183343525940492085 := by
  unfold tailWord_2802019
  simp only [CollatzResearch.WordTrace]
  refine ⟨102198028835771184591257111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68132019223847456394171407 102198028835771184591257111)
  ·
    refine ⟨153297043253656776886885667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102198028835771184591257111 153297043253656776886885667)
    ·
      refine ⟨229945564880485165330328501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 153297043253656776886885667 229945564880485165330328501)
      ·
        refine ⟨21557396707545484249718297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 229945564880485165330328501 21557396707545484249718297)
        ·
          refine ⟨16168047530659113187288723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21557396707545484249718297 16168047530659113187288723)
          ·
            refine ⟨24252071295988669780933085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16168047530659113187288723 24252071295988669780933085)
            ·
              refine ⟨9094526735995751167849907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24252071295988669780933085 9094526735995751167849907)
              ·
                refine ⟨13641790103993626751774861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9094526735995751167849907 13641790103993626751774861)
                ·
                  refine ⟨5115671288997610031915573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13641790103993626751774861 5115671288997610031915573)
                  ·
                    refine ⟨479594183343525940492085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5115671288997610031915573 479594183343525940492085)
                    ·
                      rfl

theorem cell23_2802019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 3, 1, 3, 5].length) (baseStart_2802019 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2802019 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2802019 prefixEnd_2802019 := by exact prefixLift 2802019
  have htrace : WordTrace (prefixWord ++ tailWord_2802019) baseStart_2802019 baseEnd_2802019 := by
    simpa [prefixWord, tailWord_2802019, baseEnd_2802019] using wordTrace_append hprefix tailTrace_2802019
  have hstable : (prefixWord ++ tailWord_2802019).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2802019).length < 2 ^ (prefixWord ++ tailWord_2802019).sum := by decide
  have hdescent : baseEnd_2802019 < baseStart_2802019 := by decide
  rcases family_descends (prefixWord ++ tailWord_2802019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2802033 : List Nat := [1, 2, 2, 2, 1, 2, 1, 7, 1, 1, 3]
def baseStart_2802033 : Nat := 118140960795 + 2802033 * 2 ^ 59
def prefixEnd_2802033 : Nat := 4983230072969 + 3 ^ 40 * 2802033 * 2
def baseEnd_2802033 : Nat := 1438789738759740766701191

theorem tailTrace_2802033 : CollatzResearch.WordTrace tailWord_2802033 prefixEnd_2802033 1438789738759740766701191 := by
  unfold tailWord_2802033
  simp only [CollatzResearch.WordTrace]
  refine ⟨102198539457720464982266753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68132359638480309988177835 102198539457720464982266753)
  ·
    refine ⟨76648904593290348736700065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102198539457720464982266753 76648904593290348736700065)
    ·
      refine ⟨57486678444967761552525049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76648904593290348736700065 57486678444967761552525049)
      ·
        refine ⟨43115008833725821164393787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57486678444967761552525049 43115008833725821164393787)
        ·
          refine ⟨64672513250588731746590681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43115008833725821164393787 64672513250588731746590681)
          ·
            refine ⟨48504384937941548809943011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64672513250588731746590681 48504384937941548809943011)
            ·
              refine ⟨72756577406912323214914517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48504384937941548809943011 72756577406912323214914517)
              ·
                refine ⟨1705232282974507575349559, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 72756577406912323214914517 1705232282974507575349559)
                ·
                  refine ⟨2557848424461761363024339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1705232282974507575349559 2557848424461761363024339)
                  ·
                    refine ⟨3836772636692642044536509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2557848424461761363024339 3836772636692642044536509)
                    ·
                      refine ⟨1438789738759740766701191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3836772636692642044536509 1438789738759740766701191)
                      ·
                        rfl

theorem cell23_2802033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 7, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 7, 1, 1, 3].length) (baseStart_2802033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2802033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2802033 prefixEnd_2802033 := by exact prefixLift 2802033
  have htrace : WordTrace (prefixWord ++ tailWord_2802033) baseStart_2802033 baseEnd_2802033 := by
    simpa [prefixWord, tailWord_2802033, baseEnd_2802033] using wordTrace_append hprefix tailTrace_2802033
  have hstable : (prefixWord ++ tailWord_2802033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2802033).length < 2 ^ (prefixWord ++ tailWord_2802033).sum := by decide
  have hdescent : baseEnd_2802033 < baseStart_2802033 := by decide
  rcases family_descends (prefixWord ++ tailWord_2802033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2802073 : List Nat := [1, 2, 1, 2, 1, 4, 3, 2, 3, 2, 2]
def baseStart_2802073 : Nat := 118140960795 + 2802073 * 2 ^ 59
def prefixEnd_2802073 : Nat := 4983230072969 + 3 ^ 40 * 2802073 * 2
def baseEnd_2802073 : Nat := 1438810277985920610201007

theorem tailTrace_2802073 : CollatzResearch.WordTrace tailWord_2802073 prefixEnd_2802073 1438810277985920610201007 := by
  unfold tailWord_2802073
  simp only [CollatzResearch.WordTrace]
  refine ⟨102199998377575551813722873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68133332251717034542481915 102199998377575551813722873)
  ·
    refine ⟨76649998783181663860292155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102199998377575551813722873 76649998783181663860292155)
    ·
      refine ⟨114974998174772495790438233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76649998783181663860292155 114974998174772495790438233)
      ·
        refine ⟨86231248631079371842828675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 114974998174772495790438233 86231248631079371842828675)
        ·
          refine ⟨129346872946619057764243013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86231248631079371842828675 129346872946619057764243013)
          ·
            refine ⟨24252538677491073330795565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 129346872946619057764243013 24252538677491073330795565)
            ·
              refine ⟨9094702004059152499048337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24252538677491073330795565 9094702004059152499048337)
              ·
                refine ⟨6821026503044364374286253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9094702004059152499048337 6821026503044364374286253)
                ·
                  refine ⟨2557884938641636640357345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6821026503044364374286253 2557884938641636640357345)
                  ·
                    refine ⟨1918413703981227480268009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2557884938641636640357345 1918413703981227480268009)
                    ·
                      refine ⟨1438810277985920610201007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1918413703981227480268009 1438810277985920610201007)
                      ·
                        rfl

theorem cell23_2802073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 3, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 3, 2, 3, 2, 2].length) (baseStart_2802073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2802073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2802073 prefixEnd_2802073 := by exact prefixLift 2802073
  have htrace : WordTrace (prefixWord ++ tailWord_2802073) baseStart_2802073 baseEnd_2802073 := by
    simpa [prefixWord, tailWord_2802073, baseEnd_2802073] using wordTrace_append hprefix tailTrace_2802073
  have hstable : (prefixWord ++ tailWord_2802073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2802073).length < 2 ^ (prefixWord ++ tailWord_2802073).sum := by decide
  have hdescent : baseEnd_2802073 < baseStart_2802073 := by decide
  rcases family_descends (prefixWord ++ tailWord_2802073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2802077 : List Nat := [1, 4, 2, 1, 5, 1, 1, 1, 2, 3, 2]
def baseStart_2802077 : Nat := 118140960795 + 2802077 * 2 ^ 59
def prefixEnd_2802077 : Nat := 4983230072969 + 3 ^ 40 * 2802077 * 2
def baseEnd_2802077 : Nat := 1438812331908538594550989

theorem tailTrace_2802077 : CollatzResearch.WordTrace tailWord_2802077 prefixEnd_2802077 1438812331908538594550989 := by
  unfold tailWord_2802077
  simp only [CollatzResearch.WordTrace]
  refine ⟨102200144269561060496868485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68133429513040706997912323 102200144269561060496868485)
  ·
    refine ⟨19162527050542698843162841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 102200144269561060496868485 19162527050542698843162841)
    ·
      refine ⟨14371895287907024132372131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19162527050542698843162841 14371895287907024132372131)
      ·
        refine ⟨21557842931860536198558197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14371895287907024132372131 21557842931860536198558197)
        ·
          refine ⟨2021047774861925268614831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 21557842931860536198558197 2021047774861925268614831)
          ·
            refine ⟨3031571662292887902922247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2021047774861925268614831 3031571662292887902922247)
            ·
              refine ⟨4547357493439331854383371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3031571662292887902922247 4547357493439331854383371)
              ·
                refine ⟨6821036240158997781575057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4547357493439331854383371 6821036240158997781575057)
                ·
                  refine ⟨5115777180119248336181293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6821036240158997781575057 5115777180119248336181293)
                  ·
                    refine ⟨1918416442544718126067985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5115777180119248336181293 1918416442544718126067985)
                    ·
                      refine ⟨1438812331908538594550989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1918416442544718126067985 1438812331908538594550989)
                      ·
                        rfl

theorem cell23_2802077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 5, 1, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 5, 1, 1, 1, 2, 3, 2].length) (baseStart_2802077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2802077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2802077 prefixEnd_2802077 := by exact prefixLift 2802077
  have htrace : WordTrace (prefixWord ++ tailWord_2802077) baseStart_2802077 baseEnd_2802077 := by
    simpa [prefixWord, tailWord_2802077, baseEnd_2802077] using wordTrace_append hprefix tailTrace_2802077
  have hstable : (prefixWord ++ tailWord_2802077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2802077).length < 2 ^ (prefixWord ++ tailWord_2802077).sum := by decide
  have hdescent : baseEnd_2802077 < baseStart_2802077 := by decide
  rcases family_descends (prefixWord ++ tailWord_2802077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2802129 : List Nat := [1, 2, 2, 1, 2, 1, 1, 4, 2, 3, 4]
def baseStart_2802129 : Nat := 118140960795 + 2802129 * 2 ^ 59
def prefixEnd_2802129 : Nat := 4983230072969 + 3 ^ 40 * 2802129 * 2
def baseEnd_2802129 : Nat := 1438839032902572391100749

theorem tailTrace_2802129 : CollatzResearch.WordTrace tailWord_2802129 prefixEnd_2802129 1438839032902572391100749 := by
  unfold tailWord_2802129
  simp only [CollatzResearch.WordTrace]
  refine ⟨102202040865372673377761441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68134693910248448918507627 102202040865372673377761441)
  ·
    refine ⟨76651530649029505033321081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102202040865372673377761441 76651530649029505033321081)
    ·
      refine ⟨57488647986772128774990811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76651530649029505033321081 57488647986772128774990811)
      ·
        refine ⟨86232971980158193162486217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57488647986772128774990811 86232971980158193162486217)
        ·
          refine ⟨64674728985118644871864663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 86232971980158193162486217 64674728985118644871864663)
          ·
            refine ⟨97012093477677967307796995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64674728985118644871864663 97012093477677967307796995)
            ·
              refine ⟨145518140216516950961695493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 97012093477677967307796995 145518140216516950961695493)
              ·
                refine ⟨27284651290596928305317905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 145518140216516950961695493 27284651290596928305317905)
                ·
                  refine ⟨20463488467947696228988429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27284651290596928305317905 20463488467947696228988429)
                  ·
                    refine ⟨7673808175480386085870661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20463488467947696228988429 7673808175480386085870661)
                    ·
                      refine ⟨1438839032902572391100749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7673808175480386085870661 1438839032902572391100749)
                      ·
                        rfl

theorem cell23_2802129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 4, 2, 3, 4].length) (baseStart_2802129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2802129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2802129 prefixEnd_2802129 := by exact prefixLift 2802129
  have htrace : WordTrace (prefixWord ++ tailWord_2802129) baseStart_2802129 baseEnd_2802129 := by
    simpa [prefixWord, tailWord_2802129, baseEnd_2802129] using wordTrace_append hprefix tailTrace_2802129
  have hstable : (prefixWord ++ tailWord_2802129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2802129).length < 2 ^ (prefixWord ++ tailWord_2802129).sum := by decide
  have hdescent : baseEnd_2802129 < baseStart_2802129 := by decide
  rcases family_descends (prefixWord ++ tailWord_2802129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2802130 : List Nat := [3, 2, 2, 4, 1, 2, 2, 7]
def baseStart_2802130 : Nat := 118140960795 + 2802130 * 2 ^ 59
def prefixEnd_2802130 : Nat := 4983230072969 + 3 ^ 40 * 2802130 * 2
def baseEnd_2802130 : Nat := 53290353569749143969935

theorem tailTrace_2802130 : CollatzResearch.WordTrace tailWord_2802130 prefixEnd_2802130 53290353569749143969935 := by
  unfold tailWord_2802130
  simp only [CollatzResearch.WordTrace]
  refine ⟨25550519334592262637136961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68134718225579367032365229 25550519334592262637136961)
  ·
    refine ⟨19162889500944196977852721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25550519334592262637136961 19162889500944196977852721)
    ·
      refine ⟨14372167125708147733389541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19162889500944196977852721 14372167125708147733389541)
      ·
        refine ⟨2694781336070277700010539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14372167125708147733389541 2694781336070277700010539)
        ·
          refine ⟨4042172004105416550015809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2694781336070277700010539 4042172004105416550015809)
          ·
            refine ⟨3031629003079062412511857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4042172004105416550015809 3031629003079062412511857)
            ·
              refine ⟨2273721752309296809383893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3031629003079062412511857 2273721752309296809383893)
              ·
                refine ⟨53290353569749143969935, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2273721752309296809383893 53290353569749143969935)
                ·
                  rfl

theorem cell23_2802130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 2, 2, 7].length) (baseStart_2802130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2802130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2802130 prefixEnd_2802130 := by exact prefixLift 2802130
  have htrace : WordTrace (prefixWord ++ tailWord_2802130) baseStart_2802130 baseEnd_2802130 := by
    simpa [prefixWord, tailWord_2802130, baseEnd_2802130] using wordTrace_append hprefix tailTrace_2802130
  have hstable : (prefixWord ++ tailWord_2802130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2802130).length < 2 ^ (prefixWord ++ tailWord_2802130).sum := by decide
  have hdescent : baseEnd_2802130 < baseStart_2802130 := by decide
  rcases family_descends (prefixWord ++ tailWord_2802130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2802163 : List Nat := [1, 1, 1, 2, 2, 2, 3, 3, 4, 2, 2]
def baseStart_2802163 : Nat := 118140960795 + 2802163 * 2 ^ 59
def prefixEnd_2802163 : Nat := 4983230072969 + 3 ^ 40 * 2802163 * 2
def baseEnd_2802163 : Nat := 1438856491244825258075593

theorem tailTrace_2802163 : CollatzResearch.WordTrace tailWord_2802163 prefixEnd_2802163 1438856491244825258075593 := by
  unfold tailWord_2802163
  simp only [CollatzResearch.WordTrace]
  refine ⟨102203280947249497184499143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68135520631499664789666095 102203280947249497184499143)
  ·
    refine ⟨153304921420874245776748715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102203280947249497184499143 153304921420874245776748715)
    ·
      refine ⟨229957382131311368665123073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 153304921420874245776748715 229957382131311368665123073)
      ·
        refine ⟨172468036598483526498842305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 229957382131311368665123073 172468036598483526498842305)
        ·
          refine ⟨129351027448862644874131729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 172468036598483526498842305 129351027448862644874131729)
          ·
            refine ⟨97013270586646983655598797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 129351027448862644874131729 97013270586646983655598797)
            ·
              refine ⟨36379976469992618870849549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 97013270586646983655598797 36379976469992618870849549)
              ·
                refine ⟨13642491176247232076568581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36379976469992618870849549 13642491176247232076568581)
                ·
                  refine ⟨2557967095546356014356609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13642491176247232076568581 2557967095546356014356609)
                  ·
                    refine ⟨1918475321659767010767457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2557967095546356014356609 1918475321659767010767457)
                    ·
                      refine ⟨1438856491244825258075593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1918475321659767010767457 1438856491244825258075593)
                      ·
                        rfl

theorem cell23_2802163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 3, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 3, 3, 4, 2, 2].length) (baseStart_2802163 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2802163 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2802163 prefixEnd_2802163 := by exact prefixLift 2802163
  have htrace : WordTrace (prefixWord ++ tailWord_2802163) baseStart_2802163 baseEnd_2802163 := by
    simpa [prefixWord, tailWord_2802163, baseEnd_2802163] using wordTrace_append hprefix tailTrace_2802163
  have hstable : (prefixWord ++ tailWord_2802163).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2802163).length < 2 ^ (prefixWord ++ tailWord_2802163).sum := by decide
  have hdescent : baseEnd_2802163 < baseStart_2802163 := by decide
  rcases family_descends (prefixWord ++ tailWord_2802163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2802166 : List Nat := [5, 1, 1, 1, 2, 1, 1, 2, 1, 3, 5]
def baseStart_2802166 : Nat := 118140960795 + 2802166 * 2 ^ 59
def prefixEnd_2802166 : Nat := 4983230072969 + 3 ^ 40 * 2802166 * 2
def baseEnd_2802166 : Nat := 1438858031686788746338079

theorem tailTrace_2802166 : CollatzResearch.WordTrace tailWord_2802166 prefixEnd_2802166 1438858031686788746338079 := by
  unfold tailWord_2802166
  simp only [CollatzResearch.WordTrace]
  refine ⟨6387711897889914293553647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 68135593577492419131238901 6387711897889914293553647)
  ·
    refine ⟨9581567846834871440330471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6387711897889914293553647 9581567846834871440330471)
    ·
      refine ⟨14372351770252307160495707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9581567846834871440330471 14372351770252307160495707)
      ·
        refine ⟨21558527655378460740743561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14372351770252307160495707 21558527655378460740743561)
        ·
          refine ⟨16168895741533845555557671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21558527655378460740743561 16168895741533845555557671)
          ·
            refine ⟨24253343612300768333336507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16168895741533845555557671 24253343612300768333336507)
            ·
              refine ⟨36380015418451152500004761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24253343612300768333336507 36380015418451152500004761)
              ·
                refine ⟨27285011563838364375003571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36380015418451152500004761 27285011563838364375003571)
                ·
                  refine ⟨40927517345757546562505357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27285011563838364375003571 40927517345757546562505357)
                  ·
                    refine ⟨15347819004659079960939509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 40927517345757546562505357 15347819004659079960939509)
                    ·
                      refine ⟨1438858031686788746338079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15347819004659079960939509 1438858031686788746338079)
                      ·
                        rfl

theorem cell23_2802166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 1, 2, 1, 3, 5].length) (baseStart_2802166 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2802166 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2802166 prefixEnd_2802166 := by exact prefixLift 2802166
  have htrace : WordTrace (prefixWord ++ tailWord_2802166) baseStart_2802166 baseEnd_2802166 := by
    simpa [prefixWord, tailWord_2802166, baseEnd_2802166] using wordTrace_append hprefix tailTrace_2802166
  have hstable : (prefixWord ++ tailWord_2802166).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2802166).length < 2 ^ (prefixWord ++ tailWord_2802166).sum := by decide
  have hdescent : baseEnd_2802166 < baseStart_2802166 := by decide
  rcases family_descends (prefixWord ++ tailWord_2802166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2802226 : List Nat := [3, 2, 1, 1, 2, 1, 4, 1, 1, 2, 5]
def baseStart_2802226 : Nat := 118140960795 + 2802226 * 2 ^ 59
def prefixEnd_2802226 : Nat := 4983230072969 + 3 ^ 40 * 2802226 * 2
def baseEnd_2802226 : Nat := 1438888840526058511587803

theorem tailTrace_2802226 : CollatzResearch.WordTrace tailWord_2802226 prefixEnd_2802226 1438888840526058511587803 := by
  unfold tailWord_2802226
  simp only [CollatzResearch.WordTrace]
  refine ⟨25551394686505314736010633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68137052497347505962695021 25551394686505314736010633)
  ·
    refine ⟨19163546014878986052007975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25551394686505314736010633 19163546014878986052007975)
    ·
      refine ⟨28745319022318479078011963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19163546014878986052007975 28745319022318479078011963)
      ·
        refine ⟨43117978533477718617017945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28745319022318479078011963 43117978533477718617017945)
        ·
          refine ⟨32338483900108288962763459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43117978533477718617017945 32338483900108288962763459)
          ·
            refine ⟨48507725850162433444145189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32338483900108288962763459 48507725850162433444145189)
            ·
              refine ⟨9095198596905456270777223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 48507725850162433444145189 9095198596905456270777223)
              ·
                refine ⟨13642797895358184406165835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9095198596905456270777223 13642797895358184406165835)
                ·
                  refine ⟨20464196843037276609248753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13642797895358184406165835 20464196843037276609248753)
                  ·
                    refine ⟨15348147632277957456936565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20464196843037276609248753 15348147632277957456936565)
                    ·
                      refine ⟨1438888840526058511587803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15348147632277957456936565 1438888840526058511587803)
                      ·
                        rfl

theorem cell23_2802226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 4, 1, 1, 2, 5].length) (baseStart_2802226 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2802226 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2802226 prefixEnd_2802226 := by exact prefixLift 2802226
  have htrace : WordTrace (prefixWord ++ tailWord_2802226) baseStart_2802226 baseEnd_2802226 := by
    simpa [prefixWord, tailWord_2802226, baseEnd_2802226] using wordTrace_append hprefix tailTrace_2802226
  have hstable : (prefixWord ++ tailWord_2802226).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2802226).length < 2 ^ (prefixWord ++ tailWord_2802226).sum := by decide
  have hdescent : baseEnd_2802226 < baseStart_2802226 := by decide
  rcases family_descends (prefixWord ++ tailWord_2802226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2802230 : List Nat := [5, 1, 2, 1, 2, 2, 1, 1, 2, 3, 3]
def baseStart_2802230 : Nat := 118140960795 + 2802230 * 2 ^ 59
def prefixEnd_2802230 : Nat := 4983230072969 + 3 ^ 40 * 2802230 * 2
def baseEnd_2802230 : Nat := 1438890894448676495937785

theorem tailTrace_2802230 : CollatzResearch.WordTrace tailWord_2802230 prefixEnd_2802230 1438890894448676495937785 := by
  unfold tailWord_2802230
  simp only [CollatzResearch.WordTrace]
  refine ⟨6387857789875422976699259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 68137149758671178418125429 6387857789875422976699259)
  ·
    refine ⟨9581786684813134465048889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6387857789875422976699259 9581786684813134465048889)
    ·
      refine ⟨7186340013609850848786667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9581786684813134465048889 7186340013609850848786667)
      ·
        refine ⟨10779510020414776273180001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7186340013609850848786667 10779510020414776273180001)
        ·
          refine ⟨8084632515311082204885001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10779510020414776273180001 8084632515311082204885001)
          ·
            refine ⟨6063474386483311653663751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8084632515311082204885001 6063474386483311653663751)
            ·
              refine ⟨9095211579724967480495627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6063474386483311653663751 9095211579724967480495627)
              ·
                refine ⟨13642817369587451220743441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9095211579724967480495627 13642817369587451220743441)
                ·
                  refine ⟨10232113027190588415557581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13642817369587451220743441 10232113027190588415557581)
                  ·
                    refine ⟨3837042385196470655834093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10232113027190588415557581 3837042385196470655834093)
                    ·
                      refine ⟨1438890894448676495937785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3837042385196470655834093 1438890894448676495937785)
                      ·
                        rfl

theorem cell23_2802230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 2, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 2, 1, 1, 2, 3, 3].length) (baseStart_2802230 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2802230 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2802230 prefixEnd_2802230 := by exact prefixLift 2802230
  have htrace : WordTrace (prefixWord ++ tailWord_2802230) baseStart_2802230 baseEnd_2802230 := by
    simpa [prefixWord, tailWord_2802230, baseEnd_2802230] using wordTrace_append hprefix tailTrace_2802230
  have hstable : (prefixWord ++ tailWord_2802230).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2802230).length < 2 ^ (prefixWord ++ tailWord_2802230).sum := by decide
  have hdescent : baseEnd_2802230 < baseStart_2802230 := by decide
  rcases family_descends (prefixWord ++ tailWord_2802230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2802276 : List Nat := [2, 3, 1, 1, 2, 2, 3, 1, 8]
def baseStart_2802276 : Nat := 118140960795 + 2802276 * 2 ^ 59
def prefixEnd_2802276 : Nat := 4983230072969 + 3 ^ 40 * 2802276 * 2
def baseEnd_2802276 : Nat := 159879390506531479551397

theorem tailTrace_2802276 : CollatzResearch.WordTrace tailWord_2802276 prefixEnd_2802276 159879390506531479551397 := by
  unfold tailWord_2802276
  simp only [CollatzResearch.WordTrace]
  refine ⟨51103701197920058741681341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68138268263893411655575121 51103701197920058741681341)
  ·
    refine ⟨19163887949220022028130503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51103701197920058741681341 19163887949220022028130503)
    ·
      refine ⟨28745831923830033042195755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19163887949220022028130503 28745831923830033042195755)
      ·
        refine ⟨43118747885745049563293633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28745831923830033042195755 43118747885745049563293633)
        ·
          refine ⟨32339060914308787172470225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43118747885745049563293633 32339060914308787172470225)
          ·
            refine ⟨24254295685731590379352669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32339060914308787172470225 24254295685731590379352669)
            ·
              refine ⟨9095360882149346392257251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24254295685731590379352669 9095360882149346392257251)
              ·
                refine ⟨13643041323224019588385877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9095360882149346392257251 13643041323224019588385877)
                ·
                  refine ⟨159879390506531479551397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 13643041323224019588385877 159879390506531479551397)
                  ·
                    rfl

theorem cell23_2802276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 3, 1, 8].length) (baseStart_2802276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2802276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2802276 prefixEnd_2802276 := by exact prefixLift 2802276
  have htrace : WordTrace (prefixWord ++ tailWord_2802276) baseStart_2802276 baseEnd_2802276 := by
    simpa [prefixWord, tailWord_2802276, baseEnd_2802276] using wordTrace_append hprefix tailTrace_2802276
  have hstable : (prefixWord ++ tailWord_2802276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2802276).length < 2 ^ (prefixWord ++ tailWord_2802276).sum := by decide
  have hdescent : baseEnd_2802276 < baseStart_2802276 := by decide
  rcases family_descends (prefixWord ++ tailWord_2802276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2802303 : List Nat := [1, 1, 2, 2, 1, 1, 1, 5, 5, 1, 3]
def baseStart_2802303 : Nat := 118140960795 + 2802303 * 2 ^ 59
def prefixEnd_2802303 : Nat := 4983230072969 + 3 ^ 40 * 2802303 * 2
def baseEnd_2802303 : Nat := 1438928378536454710324949

theorem tailTrace_2802303 : CollatzResearch.WordTrace tailWord_2802303 prefixEnd_2802303 1438928378536454710324949 := by
  unfold tailWord_2802303
  simp only [CollatzResearch.WordTrace]
  refine ⟨102208387166742301094595563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68138924777828200729730375 102208387166742301094595563)
  ·
    refine ⟨153312580750113451641893345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102208387166742301094595563 153312580750113451641893345)
    ·
      refine ⟨114984435562585088731420009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 153312580750113451641893345 114984435562585088731420009)
      ·
        refine ⟨86238326671938816548565007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 114984435562585088731420009 86238326671938816548565007)
        ·
          refine ⟨129357490007908224822847511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86238326671938816548565007 129357490007908224822847511)
          ·
            refine ⟨194036235011862337234271267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 129357490007908224822847511 194036235011862337234271267)
            ·
              refine ⟨291054352517793505851406901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 194036235011862337234271267 291054352517793505851406901)
              ·
                refine ⟨27286345548543141173569397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 291054352517793505851406901 27286345548543141173569397)
                ·
                  refine ⟨2558094895175919485022131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 27286345548543141173569397 2558094895175919485022131)
                  ·
                    refine ⟨3837142342763879227533197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2558094895175919485022131 3837142342763879227533197)
                    ·
                      refine ⟨1438928378536454710324949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3837142342763879227533197 1438928378536454710324949)
                      ·
                        rfl

theorem cell23_2802303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 5, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 5, 5, 1, 3].length) (baseStart_2802303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2802303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2802303 prefixEnd_2802303 := by exact prefixLift 2802303
  have htrace : WordTrace (prefixWord ++ tailWord_2802303) baseStart_2802303 baseEnd_2802303 := by
    simpa [prefixWord, tailWord_2802303, baseEnd_2802303] using wordTrace_append hprefix tailTrace_2802303
  have hstable : (prefixWord ++ tailWord_2802303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2802303).length < 2 ^ (prefixWord ++ tailWord_2802303).sum := by decide
  have hdescent : baseEnd_2802303 < baseStart_2802303 := by decide
  rcases family_descends (prefixWord ++ tailWord_2802303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2802314 : List Nat := [3, 1, 2, 3, 3, 2, 1, 3, 1, 4]
def baseStart_2802314 : Nat := 118140960795 + 2802314 * 2 ^ 59
def prefixEnd_2802314 : Nat := 4983230072969 + 3 ^ 40 * 2802314 * 2
def baseEnd_2802314 : Nat := 479644675607884722429133

theorem tailTrace_2802314 : CollatzResearch.WordTrace tailWord_2802314 prefixEnd_2802314 479644675607884722429133 := by
  unfold tailWord_2802314
  simp only [CollatzResearch.WordTrace]
  refine ⟨25552197092425612493311499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68139192246468299982163997 25552197092425612493311499)
  ·
    refine ⟨38328295638638418739967249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25552197092425612493311499 38328295638638418739967249)
    ·
      refine ⟨28746221728978814054975437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38328295638638418739967249 28746221728978814054975437)
      ·
        refine ⟨10779833148367055270615789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28746221728978814054975437 10779833148367055270615789)
        ·
          refine ⟨4042437430637645726480921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10779833148367055270615789 4042437430637645726480921)
          ·
            refine ⟨3031828072978234294860691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4042437430637645726480921 3031828072978234294860691)
            ·
              refine ⟨4547742109467351442291037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3031828072978234294860691 4547742109467351442291037)
              ·
                refine ⟨1705403291050256790859139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4547742109467351442291037 1705403291050256790859139)
                ·
                  refine ⟨2558104936575385186288709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1705403291050256790859139 2558104936575385186288709)
                  ·
                    refine ⟨479644675607884722429133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2558104936575385186288709 479644675607884722429133)
                    ·
                      rfl

theorem cell23_2802314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 2, 1, 3, 1, 4].length) (baseStart_2802314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2802314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2802314 prefixEnd_2802314 := by exact prefixLift 2802314
  have htrace : WordTrace (prefixWord ++ tailWord_2802314) baseStart_2802314 baseEnd_2802314 := by
    simpa [prefixWord, tailWord_2802314, baseEnd_2802314] using wordTrace_append hprefix tailTrace_2802314
  have hstable : (prefixWord ++ tailWord_2802314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2802314).length < 2 ^ (prefixWord ++ tailWord_2802314).sum := by decide
  have hdescent : baseEnd_2802314 < baseStart_2802314 := by decide
  rcases family_descends (prefixWord ++ tailWord_2802314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2802357 : List Nat := [1, 3, 3, 3, 1, 3, 1, 2, 1, 5]
def baseStart_2802357 : Nat := 118140960795 + 2802357 * 2 ^ 59
def prefixEnd_2802357 : Nat := 4983230072969 + 3 ^ 40 * 2802357 * 2
def baseEnd_2802357 : Nat := 479652035497265833016567

theorem tailTrace_2802357 : CollatzResearch.WordTrace tailWord_2802357 prefixEnd_2802357 479652035497265833016567 := by
  unfold tailWord_2802357
  simp only [CollatzResearch.WordTrace]
  refine ⟨102210356708546668317061325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68140237805697778878040883 102210356708546668317061325)
  ·
    refine ⟨38328883765705000618897997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 102210356708546668317061325 38328883765705000618897997)
    ·
      refine ⟨14373331412139375232086749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38328883765705000618897997 14373331412139375232086749)
      ·
        refine ⟨5389999279552265712032531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14373331412139375232086749 5389999279552265712032531)
        ·
          refine ⟨8084998919328398568048797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5389999279552265712032531 8084998919328398568048797)
          ·
            refine ⟨3031874594748149463018299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8084998919328398568048797 3031874594748149463018299)
            ·
              refine ⟨4547811892122224194527449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3031874594748149463018299 4547811892122224194527449)
              ·
                refine ⟨3410858919091668145895587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4547811892122224194527449 3410858919091668145895587)
                ·
                  refine ⟨5116288378637502218843381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3410858919091668145895587 5116288378637502218843381)
                  ·
                    refine ⟨479652035497265833016567, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5116288378637502218843381 479652035497265833016567)
                    ·
                      rfl

theorem cell23_2802357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 3, 1, 2, 1, 5].length) (baseStart_2802357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2802357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2802357 prefixEnd_2802357 := by exact prefixLift 2802357
  have htrace : WordTrace (prefixWord ++ tailWord_2802357) baseStart_2802357 baseEnd_2802357 := by
    simpa [prefixWord, tailWord_2802357, baseEnd_2802357] using wordTrace_append hprefix tailTrace_2802357
  have hstable : (prefixWord ++ tailWord_2802357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2802357).length < 2 ^ (prefixWord ++ tailWord_2802357).sum := by decide
  have hdescent : baseEnd_2802357 < baseStart_2802357 := by decide
  rcases family_descends (prefixWord ++ tailWord_2802357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2802380 : List Nat := [2, 2, 1, 5, 1, 1, 3, 1, 1, 1, 5]
def baseStart_2802380 : Nat := 118140960795 + 2802380 * 2 ^ 59
def prefixEnd_2802380 : Nat := 4983230072969 + 3 ^ 40 * 2802380 * 2
def baseEnd_2802380 : Nat := 1438967916546850909062095

theorem tailTrace_2802380 : CollatzResearch.WordTrace tailWord_2802380 prefixEnd_2802380 1438967916546850909062095 := by
  unfold tailWord_2802380
  simp only [CollatzResearch.WordTrace]
  refine ⟨51105597793731671622574297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68140797058308895496765729 51105597793731671622574297)
  ·
    refine ⟨38329198345298753716930723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51105597793731671622574297 38329198345298753716930723)
    ·
      refine ⟨57493797517948130575396085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38329198345298753716930723 57493797517948130575396085)
      ·
        refine ⟨5390043517307637241443383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 57493797517948130575396085 5390043517307637241443383)
        ·
          refine ⟨8085065275961455862165075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5390043517307637241443383 8085065275961455862165075)
          ·
            refine ⟨12127597913942183793247613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8085065275961455862165075 12127597913942183793247613)
            ·
              refine ⟨4547849217728318922467855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12127597913942183793247613 4547849217728318922467855)
              ·
                refine ⟨6821773826592478383701783, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4547849217728318922467855 6821773826592478383701783)
                ·
                  refine ⟨10232660739888717575552675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6821773826592478383701783 10232660739888717575552675)
                  ·
                    refine ⟨15348991109833076363329013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10232660739888717575552675 15348991109833076363329013)
                    ·
                      refine ⟨1438967916546850909062095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15348991109833076363329013 1438967916546850909062095)
                      ·
                        rfl

theorem cell23_2802380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 3, 1, 1, 1, 5].length) (baseStart_2802380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2802380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2802380 prefixEnd_2802380 := by exact prefixLift 2802380
  have htrace : WordTrace (prefixWord ++ tailWord_2802380) baseStart_2802380 baseEnd_2802380 := by
    simpa [prefixWord, tailWord_2802380, baseEnd_2802380] using wordTrace_append hprefix tailTrace_2802380
  have hstable : (prefixWord ++ tailWord_2802380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2802380).length < 2 ^ (prefixWord ++ tailWord_2802380).sum := by decide
  have hdescent : baseEnd_2802380 < baseStart_2802380 := by decide
  rcases family_descends (prefixWord ++ tailWord_2802380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2802388 : List Nat := [2, 4, 1, 3, 2, 2, 2, 2, 1, 1, 3]
def baseStart_2802388 : Nat := 118140960795 + 2802388 * 2 ^ 59
def prefixEnd_2802388 : Nat := 4983230072969 + 3 ^ 40 * 2802388 * 2
def baseEnd_2802388 : Nat := 1438972024392086877762059

theorem tailTrace_2802388 : CollatzResearch.WordTrace tailWord_2802388 prefixEnd_2802388 1438972024392086877762059 := by
  unfold tailWord_2802388
  simp only [CollatzResearch.WordTrace]
  refine ⟨51105743685717180305719909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68140991580956240407626545 51105743685717180305719909)
  ·
    refine ⟨9582326941071971307322483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 51105743685717180305719909 9582326941071971307322483)
    ·
      refine ⟨14373490411607956960983725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9582326941071971307322483 14373490411607956960983725)
      ·
        refine ⟨5390058904352983860368897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14373490411607956960983725 5390058904352983860368897)
        ·
          refine ⟨4042544178264737895276673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5390058904352983860368897 4042544178264737895276673)
          ·
            refine ⟨3031908133698553421457505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4042544178264737895276673 3031908133698553421457505)
            ·
              refine ⟨2273931100273915066093129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3031908133698553421457505 2273931100273915066093129)
              ·
                refine ⟨1705448325205436299569847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2273931100273915066093129 1705448325205436299569847)
                ·
                  refine ⟨2558172487808154449354771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1705448325205436299569847 2558172487808154449354771)
                  ·
                    refine ⟨3837258731712231674032157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2558172487808154449354771 3837258731712231674032157)
                    ·
                      refine ⟨1438972024392086877762059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3837258731712231674032157 1438972024392086877762059)
                      ·
                        rfl

theorem cell23_2802388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 2, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 2, 2, 2, 1, 1, 3].length) (baseStart_2802388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2802388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2802388 prefixEnd_2802388 := by exact prefixLift 2802388
  have htrace : WordTrace (prefixWord ++ tailWord_2802388) baseStart_2802388 baseEnd_2802388 := by
    simpa [prefixWord, tailWord_2802388, baseEnd_2802388] using wordTrace_append hprefix tailTrace_2802388
  have hstable : (prefixWord ++ tailWord_2802388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2802388).length < 2 ^ (prefixWord ++ tailWord_2802388).sum := by decide
  have hdescent : baseEnd_2802388 < baseStart_2802388 := by decide
  rcases family_descends (prefixWord ++ tailWord_2802388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2802393 : List Nat := [1, 2, 1, 2, 3, 2, 1, 2, 3, 3, 3]
def baseStart_2802393 : Nat := 118140960795 + 2802393 * 2 ^ 59
def prefixEnd_2802393 : Nat := 4983230072969 + 3 ^ 40 * 2802393 * 2
def baseEnd_2802393 : Nat := 1438974591795359358199535

theorem tailTrace_2802393 : CollatzResearch.WordTrace tailWord_2802393 prefixEnd_2802393 1438974591795359358199535 := by
  unfold tailWord_2802393
  simp only [CollatzResearch.WordTrace]
  refine ⟨102211669736416246465371833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68141113157610830976914555 102211669736416246465371833)
  ·
    refine ⟨76658752302312184849028875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102211669736416246465371833 76658752302312184849028875)
    ·
      refine ⟨114988128453468277273543313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76658752302312184849028875 114988128453468277273543313)
      ·
        refine ⟨86241096340101207955157485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 114988128453468277273543313 86241096340101207955157485)
        ·
          refine ⟨32340411127537952983184057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 86241096340101207955157485 32340411127537952983184057)
          ·
            refine ⟨24255308345653464737388043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32340411127537952983184057 24255308345653464737388043)
            ·
              refine ⟨36382962518480197106082065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24255308345653464737388043 36382962518480197106082065)
              ·
                refine ⟨27287221888860147829561549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36382962518480197106082065 27287221888860147829561549)
                ·
                  refine ⟨10232708208322555436085581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27287221888860147829561549 10232708208322555436085581)
                  ·
                    refine ⟨3837265578120958288532093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10232708208322555436085581 3837265578120958288532093)
                    ·
                      refine ⟨1438974591795359358199535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3837265578120958288532093 1438974591795359358199535)
                      ·
                        rfl

theorem cell23_2802393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 1, 2, 3, 3, 3].length) (baseStart_2802393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2802393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2802393 prefixEnd_2802393 := by exact prefixLift 2802393
  have htrace : WordTrace (prefixWord ++ tailWord_2802393) baseStart_2802393 baseEnd_2802393 := by
    simpa [prefixWord, tailWord_2802393, baseEnd_2802393] using wordTrace_append hprefix tailTrace_2802393
  have hstable : (prefixWord ++ tailWord_2802393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2802393).length < 2 ^ (prefixWord ++ tailWord_2802393).sum := by decide
  have hdescent : baseEnd_2802393 < baseStart_2802393 := by decide
  rcases family_descends (prefixWord ++ tailWord_2802393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2802394 : List Nat := [3, 1, 1, 2, 2, 2, 3, 4, 1, 2, 2]
def baseStart_2802394 : Nat := 118140960795 + 2802394 * 2 ^ 59
def prefixEnd_2802394 : Nat := 4983230072969 + 3 ^ 40 * 2802394 * 2
def baseEnd_2802394 : Nat := 1438975105276013854287031

theorem tailTrace_2802394 : CollatzResearch.WordTrace tailWord_2802394 prefixEnd_2802394 1438975105276013854287031 := by
  unfold tailWord_2802394
  simp only [CollatzResearch.WordTrace]
  refine ⟨25552926552353155909039559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68141137472941749090772157 25552926552353155909039559)
  ·
    refine ⟨38329389828529733863559339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25552926552353155909039559 38329389828529733863559339)
    ·
      refine ⟨57494084742794600795339009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38329389828529733863559339 57494084742794600795339009)
      ·
        refine ⟨43120563557095950596504257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57494084742794600795339009 43120563557095950596504257)
        ·
          refine ⟨32340422667821962947378193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43120563557095950596504257 32340422667821962947378193)
          ·
            refine ⟨24255317000866472210533645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32340422667821962947378193 24255317000866472210533645)
            ·
              refine ⟨9095743875324927078950117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24255317000866472210533645 9095743875324927078950117)
              ·
                refine ⟨1705451976623423827303147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9095743875324927078950117 1705451976623423827303147)
                ·
                  refine ⟨2558177964935135740954721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1705451976623423827303147 2558177964935135740954721)
                  ·
                    refine ⟨1918633473701351805716041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2558177964935135740954721 1918633473701351805716041)
                    ·
                      refine ⟨1438975105276013854287031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1918633473701351805716041 1438975105276013854287031)
                      ·
                        rfl

theorem cell23_2802394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 3, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 3, 4, 1, 2, 2].length) (baseStart_2802394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2802394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2802394 prefixEnd_2802394 := by exact prefixLift 2802394
  have htrace : WordTrace (prefixWord ++ tailWord_2802394) baseStart_2802394 baseEnd_2802394 := by
    simpa [prefixWord, tailWord_2802394, baseEnd_2802394] using wordTrace_append hprefix tailTrace_2802394
  have hstable : (prefixWord ++ tailWord_2802394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2802394).length < 2 ^ (prefixWord ++ tailWord_2802394).sum := by decide
  have hdescent : baseEnd_2802394 < baseStart_2802394 := by decide
  rcases family_descends (prefixWord ++ tailWord_2802394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2802410 : List Nat := [3, 1, 3, 1, 1, 1, 1, 2, 6, 1, 3]
def baseStart_2802410 : Nat := 118140960795 + 2802410 * 2 ^ 59
def prefixEnd_2802410 : Nat := 4983230072969 + 3 ^ 40 * 2802410 * 2
def baseEnd_2802410 : Nat := 1438983320966485791686957

theorem tailTrace_2802410 : CollatzResearch.WordTrace tailWord_2802410 prefixEnd_2802410 1438983320966485791686957 := by
  unfold tailWord_2802410
  simp only [CollatzResearch.WordTrace]
  refine ⟨25553072444338664592185171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68141526518236438912493789 25553072444338664592185171)
  ·
    refine ⟨38329608666507996888277757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25553072444338664592185171 38329608666507996888277757)
    ·
      refine ⟨14373603249940498833104159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38329608666507996888277757 14373603249940498833104159)
      ·
        refine ⟨21560404874910748249656239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14373603249940498833104159 21560404874910748249656239)
        ·
          refine ⟨32340607312366122374484359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21560404874910748249656239 32340607312366122374484359)
          ·
            refine ⟨48510910968549183561726539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32340607312366122374484359 48510910968549183561726539)
            ·
              refine ⟨72766366452823775342589809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48510910968549183561726539 72766366452823775342589809)
              ·
                refine ⟨54574774839617831506942357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 72766366452823775342589809 54574774839617831506942357)
                ·
                  refine ⟨2558192570607085851887923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 54574774839617831506942357 2558192570607085851887923)
                  ·
                    refine ⟨3837288855910628777831885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2558192570607085851887923 3837288855910628777831885)
                    ·
                      refine ⟨1438983320966485791686957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3837288855910628777831885 1438983320966485791686957)
                      ·
                        rfl

theorem cell23_2802410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 2, 6, 1, 3].length) (baseStart_2802410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2802410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2802410 prefixEnd_2802410 := by exact prefixLift 2802410
  have htrace : WordTrace (prefixWord ++ tailWord_2802410) baseStart_2802410 baseEnd_2802410 := by
    simpa [prefixWord, tailWord_2802410, baseEnd_2802410] using wordTrace_append hprefix tailTrace_2802410
  have hstable : (prefixWord ++ tailWord_2802410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2802410).length < 2 ^ (prefixWord ++ tailWord_2802410).sum := by decide
  have hdescent : baseEnd_2802410 < baseStart_2802410 := by decide
  rcases family_descends (prefixWord ++ tailWord_2802410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2802413 : List Nat := [1, 5, 1, 2, 1, 1, 1, 2, 2, 7]
def baseStart_2802413 : Nat := 118140960795 + 2802413 * 2 ^ 59
def prefixEnd_2802413 : Nat := 4983230072969 + 3 ^ 40 * 2802413 * 2
def baseEnd_2802413 : Nat := 479661620469483093316481

theorem tailTrace_2802413 : CollatzResearch.WordTrace tailWord_2802413 prefixEnd_2802413 479661620469483093316481 := by
  unfold tailWord_2802413
  simp only [CollatzResearch.WordTrace]
  refine ⟨102212399196343789881099893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68141599464229193254066595 102212399196343789881099893)
  ·
    refine ⟨9582412424657230301353115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 102212399196343789881099893 9582412424657230301353115)
    ·
      refine ⟨14373618636985845452029673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9582412424657230301353115 14373618636985845452029673)
      ·
        refine ⟨10780213977739384089022255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14373618636985845452029673 10780213977739384089022255)
        ·
          refine ⟨16170320966609076133533383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10780213977739384089022255 16170320966609076133533383)
          ·
            refine ⟨24255481449913614200300075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16170320966609076133533383 24255481449913614200300075)
            ·
              refine ⟨36383222174870421300450113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24255481449913614200300075 36383222174870421300450113)
              ·
                refine ⟨27287416631152815975337585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36383222174870421300450113 27287416631152815975337585)
                ·
                  refine ⟨20465562473364611981503189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27287416631152815975337585 20465562473364611981503189)
                  ·
                    refine ⟨479661620469483093316481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 20465562473364611981503189 479661620469483093316481)
                    ·
                      rfl

theorem cell23_2802413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 1, 2, 2, 7].length) (baseStart_2802413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2802413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2802413 prefixEnd_2802413 := by exact prefixLift 2802413
  have htrace : WordTrace (prefixWord ++ tailWord_2802413) baseStart_2802413 baseEnd_2802413 := by
    simpa [prefixWord, tailWord_2802413, baseEnd_2802413] using wordTrace_append hprefix tailTrace_2802413
  have hstable : (prefixWord ++ tailWord_2802413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2802413).length < 2 ^ (prefixWord ++ tailWord_2802413).sum := by decide
  have hdescent : baseEnd_2802413 < baseStart_2802413 := by decide
  rcases family_descends (prefixWord ++ tailWord_2802413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2802461 : List Nat := [1, 4, 2, 4, 2, 1, 1, 1, 1, 3, 3]
def baseStart_2802461 : Nat := 118140960795 + 2802461 * 2 ^ 59
def prefixEnd_2802461 : Nat := 4983230072969 + 3 ^ 40 * 2802461 * 2
def baseEnd_2802461 : Nat := 1439009508479865092149223

theorem tailTrace_2802461 : CollatzResearch.WordTrace tailWord_2802461 prefixEnd_2802461 1439009508479865092149223 := by
  unfold tailWord_2802461
  simp only [CollatzResearch.WordTrace]
  refine ⟨102214149900169894078847237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68142766600113262719231491 102214149900169894078847237)
  ·
    refine ⟨19165153106281855139783857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 102214149900169894078847237 19165153106281855139783857)
    ·
      refine ⟨14373864829711391354837893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19165153106281855139783857 14373864829711391354837893)
      ·
        refine ⟨2695099655570885879032105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14373864829711391354837893 2695099655570885879032105)
        ·
          refine ⟨2021324741678164409274079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2695099655570885879032105 2021324741678164409274079)
          ·
            refine ⟨3031987112517246613911119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2021324741678164409274079 3031987112517246613911119)
            ·
              refine ⟨4547980668775869920866679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3031987112517246613911119 4547980668775869920866679)
              ·
                refine ⟨6821971003163804881300019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4547980668775869920866679 6821971003163804881300019)
                ·
                  refine ⟨10232956504745707321950029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6821971003163804881300019 10232956504745707321950029)
                  ·
                    refine ⟨3837358689279640245731261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10232956504745707321950029 3837358689279640245731261)
                    ·
                      refine ⟨1439009508479865092149223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3837358689279640245731261 1439009508479865092149223)
                      ·
                        rfl

theorem cell23_2802461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 2, 1, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 2, 1, 1, 1, 1, 3, 3].length) (baseStart_2802461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2802461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2802461 prefixEnd_2802461 := by exact prefixLift 2802461
  have htrace : WordTrace (prefixWord ++ tailWord_2802461) baseStart_2802461 baseEnd_2802461 := by
    simpa [prefixWord, tailWord_2802461, baseEnd_2802461] using wordTrace_append hprefix tailTrace_2802461
  have hstable : (prefixWord ++ tailWord_2802461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2802461).length < 2 ^ (prefixWord ++ tailWord_2802461).sum := by decide
  have hdescent : baseEnd_2802461 < baseStart_2802461 := by decide
  rcases family_descends (prefixWord ++ tailWord_2802461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2802533 : List Nat := [1, 3, 1, 3, 1, 1, 2, 1, 2, 8]
def baseStart_2802533 : Nat := 118140960795 + 2802533 * 2 ^ 59
def prefixEnd_2802533 : Nat := 4983230072969 + 3 ^ 40 * 2802533 * 2
def baseEnd_2802533 : Nat := 479682159695662936816297

theorem tailTrace_2802533 : CollatzResearch.WordTrace tailWord_2802533 prefixEnd_2802533 479682159695662936816297 := by
  unfold tailWord_2802533
  simp only [CollatzResearch.WordTrace]
  refine ⟨102216775955909050375468253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68144517303939366916978835 102216775955909050375468253)
  ·
    refine ⟨38331290983465893890800595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 102216775955909050375468253 38331290983465893890800595)
    ·
      refine ⟨57496936475198840836200893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38331290983465893890800595 57496936475198840836200893)
      ·
        refine ⟨21561351178199565313575335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 57496936475198840836200893 21561351178199565313575335)
        ·
          refine ⟨32342026767299347970363003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21561351178199565313575335 32342026767299347970363003)
          ·
            refine ⟨48513040150949021955544505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32342026767299347970363003 48513040150949021955544505)
            ·
              refine ⟨36384780113211766466658379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48513040150949021955544505 36384780113211766466658379)
              ·
                refine ⟨54577170169817649699987569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36384780113211766466658379 54577170169817649699987569)
                ·
                  refine ⟨40932877627363237274990677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 54577170169817649699987569 40932877627363237274990677)
                  ·
                    refine ⟨479682159695662936816297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 40932877627363237274990677 479682159695662936816297)
                    ·
                      rfl

theorem cell23_2802533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 2, 1, 2, 8].length) (baseStart_2802533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2802533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2802533 prefixEnd_2802533 := by exact prefixLift 2802533
  have htrace : WordTrace (prefixWord ++ tailWord_2802533) baseStart_2802533 baseEnd_2802533 := by
    simpa [prefixWord, tailWord_2802533, baseEnd_2802533] using wordTrace_append hprefix tailTrace_2802533
  have hstable : (prefixWord ++ tailWord_2802533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2802533).length < 2 ^ (prefixWord ++ tailWord_2802533).sum := by decide
  have hdescent : baseEnd_2802533 < baseStart_2802533 := by decide
  rcases family_descends (prefixWord ++ tailWord_2802533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2802558 : List Nat := [4, 2, 3, 1, 2, 2, 2, 2, 5]
def baseStart_2802558 : Nat := 118140960795 + 2802558 * 2 ^ 59
def prefixEnd_2802558 : Nat := 4983230072969 + 3 ^ 40 * 2802558 * 2
def baseEnd_2802558 : Nat := 159895479567039023626253

theorem tailTrace_2802558 : CollatzResearch.WordTrace tailWord_2802558 prefixEnd_2802558 159895479567039023626253 := by
  unfold tailWord_2802558
  simp only [CollatzResearch.WordTrace]
  refine ⟨12777210972602309955641041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 68145125187212319763418885 12777210972602309955641041)
  ·
    refine ⟨9582908229451732466730781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12777210972602309955641041 9582908229451732466730781)
    ·
      refine ⟨3593590586044399675024043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9582908229451732466730781 3593590586044399675024043)
      ·
        refine ⟨5390385879066599512536065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3593590586044399675024043 5390385879066599512536065)
        ·
          refine ⟨4042789409299949634402049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5390385879066599512536065 4042789409299949634402049)
          ·
            refine ⟨3032092056974962225801537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4042789409299949634402049 3032092056974962225801537)
            ·
              refine ⟨2274069042731221669351153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3032092056974962225801537 2274069042731221669351153)
              ·
                refine ⟨1705551782048416252013365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2274069042731221669351153 1705551782048416252013365)
                ·
                  refine ⟨159895479567039023626253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1705551782048416252013365 159895479567039023626253)
                  ·
                    rfl

theorem cell23_2802558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 2, 2, 2, 5].length) (baseStart_2802558 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2802558 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2802558 prefixEnd_2802558 := by exact prefixLift 2802558
  have htrace : WordTrace (prefixWord ++ tailWord_2802558) baseStart_2802558 baseEnd_2802558 := by
    simpa [prefixWord, tailWord_2802558, baseEnd_2802558] using wordTrace_append hprefix tailTrace_2802558
  have hstable : (prefixWord ++ tailWord_2802558).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2802558).length < 2 ^ (prefixWord ++ tailWord_2802558).sum := by decide
  have hdescent : baseEnd_2802558 < baseStart_2802558 := by decide
  rcases family_descends (prefixWord ++ tailWord_2802558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2802560 : List Nat := [2, 1, 1, 2, 1, 2, 2, 3, 4, 2, 3]
def baseStart_2802560 : Nat := 118140960795 + 2802560 * 2 ^ 59
def prefixEnd_2802560 : Nat := 4983230072969 + 3 ^ 40 * 2802560 * 2
def baseEnd_2802560 : Nat := 1439060343064660204811267

theorem tailTrace_2802560 : CollatzResearch.WordTrace tailWord_2802560 prefixEnd_2802560 1439060343064660204811267 := by
  unfold tailWord_2802560
  simp only [CollatzResearch.WordTrace]
  refine ⟨51108880363405616993350567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68145173817874155991134089 51108880363405616993350567)
  ·
    refine ⟨76663320545108425490025851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51108880363405616993350567 76663320545108425490025851)
    ·
      refine ⟨114994980817662638235038777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76663320545108425490025851 114994980817662638235038777)
      ·
        refine ⟨86246235613246978676279083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 114994980817662638235038777 86246235613246978676279083)
        ·
          refine ⟨129369353419870468014418625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86246235613246978676279083 129369353419870468014418625)
          ·
            refine ⟨97027015064902851010813969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 129369353419870468014418625 97027015064902851010813969)
            ·
              refine ⟨72770261298677138258110477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 97027015064902851010813969 72770261298677138258110477)
              ·
                refine ⟨27288847987003926846791429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 72770261298677138258110477 27288847987003926846791429)
                ·
                  refine ⟨5116658997563236283773393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27288847987003926846791429 5116658997563236283773393)
                  ·
                    refine ⟨3837494248172427212830045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5116658997563236283773393 3837494248172427212830045)
                    ·
                      refine ⟨1439060343064660204811267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3837494248172427212830045 1439060343064660204811267)
                      ·
                        rfl

theorem cell23_2802560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 3, 4, 2, 3].length) (baseStart_2802560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2802560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2802560 prefixEnd_2802560 := by exact prefixLift 2802560
  have htrace : WordTrace (prefixWord ++ tailWord_2802560) baseStart_2802560 baseEnd_2802560 := by
    simpa [prefixWord, tailWord_2802560, baseEnd_2802560] using wordTrace_append hprefix tailTrace_2802560
  have hstable : (prefixWord ++ tailWord_2802560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2802560).length < 2 ^ (prefixWord ++ tailWord_2802560).sum := by decide
  have hdescent : baseEnd_2802560 < baseStart_2802560 := by decide
  rcases family_descends (prefixWord ++ tailWord_2802560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2802594 : List Nat := [3, 3, 1, 2, 2, 1, 3, 1, 2, 2, 3]
def baseStart_2802594 : Nat := 118140960795 + 2802594 * 2 ^ 59
def prefixEnd_2802594 : Nat := 4983230072969 + 3 ^ 40 * 2802594 * 2
def baseEnd_2802594 : Nat := 1439077801406913071786111

theorem tailTrace_2802594 : CollatzResearch.WordTrace tailWord_2802594 prefixEnd_2802594 1439077801406913071786111 := by
  unfold tailWord_2802594
  simp only [CollatzResearch.WordTrace]
  refine ⟨25554750202172014448359709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68146000539125371862292557 25554750202172014448359709)
  ·
    refine ⟨9583031325814505418134891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25554750202172014448359709 9583031325814505418134891)
    ·
      refine ⟨14374546988721758127202337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9583031325814505418134891 14374546988721758127202337)
      ·
        refine ⟨10780910241541318595401753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14374546988721758127202337 10780910241541318595401753)
        ·
          refine ⟨8085682681155988946551315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10780910241541318595401753 8085682681155988946551315)
          ·
            refine ⟨12128524021733983419826973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8085682681155988946551315 12128524021733983419826973)
            ·
              refine ⟨4548196508150243782435115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12128524021733983419826973 4548196508150243782435115)
              ·
                refine ⟨6822294762225365673652673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4548196508150243782435115 6822294762225365673652673)
                ·
                  refine ⟨5116721071669024255239505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6822294762225365673652673 5116721071669024255239505)
                  ·
                    refine ⟨3837540803751768191429629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5116721071669024255239505 3837540803751768191429629)
                    ·
                      refine ⟨1439077801406913071786111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3837540803751768191429629 1439077801406913071786111)
                      ·
                        rfl

theorem cell23_2802594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 3, 1, 2, 2, 3].length) (baseStart_2802594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2802594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2802594 prefixEnd_2802594 := by exact prefixLift 2802594
  have htrace : WordTrace (prefixWord ++ tailWord_2802594) baseStart_2802594 baseEnd_2802594 := by
    simpa [prefixWord, tailWord_2802594, baseEnd_2802594] using wordTrace_append hprefix tailTrace_2802594
  have hstable : (prefixWord ++ tailWord_2802594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2802594).length < 2 ^ (prefixWord ++ tailWord_2802594).sum := by decide
  have hdescent : baseEnd_2802594 < baseStart_2802594 := by decide
  rcases family_descends (prefixWord ++ tailWord_2802594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2802603 : List Nat := [1, 1, 1, 1, 2, 1, 1, 4, 1, 3, 7]
def baseStart_2802603 : Nat := 118140960795 + 2802603 * 2 ^ 59
def prefixEnd_2802603 : Nat := 4983230072969 + 3 ^ 40 * 2802603 * 2
def baseEnd_2802603 : Nat := 1439082422732803536573569

theorem tailTrace_2802603 : CollatzResearch.WordTrace tailWord_2802603 prefixEnd_2802603 1439082422732803536573569 := by
  unfold tailWord_2802603
  simp only [CollatzResearch.WordTrace]
  refine ⟨102219329065655452330516463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68146219377103634887010975 102219329065655452330516463)
  ·
    refine ⟨153328993598483178495774695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102219329065655452330516463 153328993598483178495774695)
    ·
      refine ⟨229993490397724767743662043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 153328993598483178495774695 229993490397724767743662043)
      ·
        refine ⟨344990235596587151615493065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 229993490397724767743662043 344990235596587151615493065)
        ·
          refine ⟨258742676697440363711619799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 344990235596587151615493065 258742676697440363711619799)
          ·
            refine ⟨388114015046160545567429699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 258742676697440363711619799 388114015046160545567429699)
            ·
              refine ⟨582171022569240818351144549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 388114015046160545567429699 582171022569240818351144549)
              ·
                refine ⟨109157066731732653440839603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 582171022569240818351144549 109157066731732653440839603)
                ·
                  refine ⟨163735600097598980161259405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 109157066731732653440839603 163735600097598980161259405)
                  ·
                    refine ⟨61400850036599617560472277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 163735600097598980161259405 61400850036599617560472277)
                    ·
                      refine ⟨1439082422732803536573569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 61400850036599617560472277 1439082422732803536573569)
                      ·
                        rfl

theorem cell23_2802603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 4, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 4, 1, 3, 7].length) (baseStart_2802603 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2802603 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2802603 prefixEnd_2802603 := by exact prefixLift 2802603
  have htrace : WordTrace (prefixWord ++ tailWord_2802603) baseStart_2802603 baseEnd_2802603 := by
    simpa [prefixWord, tailWord_2802603, baseEnd_2802603] using wordTrace_append hprefix tailTrace_2802603
  have hstable : (prefixWord ++ tailWord_2802603).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2802603).length < 2 ^ (prefixWord ++ tailWord_2802603).sum := by decide
  have hdescent : baseEnd_2802603 < baseStart_2802603 := by decide
  rcases family_descends (prefixWord ++ tailWord_2802603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2802624 : List Nat := [2, 1, 1, 2, 3, 4, 2, 1, 3, 1, 3]
def baseStart_2802624 : Nat := 118140960795 + 2802624 * 2 ^ 59
def prefixEnd_2802624 : Nat := 4983230072969 + 3 ^ 40 * 2802624 * 2
def baseEnd_2802624 : Nat := 1439093205826547954410973

theorem tailTrace_2802624 : CollatzResearch.WordTrace tailWord_2802624 prefixEnd_2802624 1439093205826547954410973 := by
  unfold tailWord_2802624
  simp only [CollatzResearch.WordTrace]
  refine ⟨51110047499289686458515463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68146729999052915278020617 51110047499289686458515463)
  ·
    refine ⟨76665071248934529687773195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51110047499289686458515463 76665071248934529687773195)
    ·
      refine ⟨114997606873401794531659793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76665071248934529687773195 114997606873401794531659793)
      ·
        refine ⟨86248205155051345898744845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 114997606873401794531659793 86248205155051345898744845)
        ·
          refine ⟨32343076933144254712029317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 86248205155051345898744845 32343076933144254712029317)
          ·
            refine ⟨6064326924964547758505497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 32343076933144254712029317 6064326924964547758505497)
            ·
              refine ⟨4548245193723410818879123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6064326924964547758505497 4548245193723410818879123)
              ·
                refine ⟨6822367790585116228318685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4548245193723410818879123 6822367790585116228318685)
                ·
                  refine ⟨2558387921469418585619507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6822367790585116228318685 2558387921469418585619507)
                  ·
                    refine ⟨3837581882204127878429261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2558387921469418585619507 3837581882204127878429261)
                    ·
                      refine ⟨1439093205826547954410973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3837581882204127878429261 1439093205826547954410973)
                      ·
                        rfl

theorem cell23_2802624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 4, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 4, 2, 1, 3, 1, 3].length) (baseStart_2802624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2802624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2802624 prefixEnd_2802624 := by exact prefixLift 2802624
  have htrace : WordTrace (prefixWord ++ tailWord_2802624) baseStart_2802624 baseEnd_2802624 := by
    simpa [prefixWord, tailWord_2802624, baseEnd_2802624] using wordTrace_append hprefix tailTrace_2802624
  have hstable : (prefixWord ++ tailWord_2802624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2802624).length < 2 ^ (prefixWord ++ tailWord_2802624).sum := by decide
  have hdescent : baseEnd_2802624 < baseStart_2802624 := by decide
  rcases family_descends (prefixWord ++ tailWord_2802624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2802644 : List Nat := [2, 4, 1, 2, 1, 3, 2, 2, 1, 5]
def baseStart_2802644 : Nat := 118140960795 + 2802644 * 2 ^ 59
def prefixEnd_2802644 : Nat := 4983230072969 + 3 ^ 40 * 2802644 * 2
def baseEnd_2802644 : Nat := 479701158479879292053627

theorem tailTrace_2802644 : CollatzResearch.WordTrace tailWord_2802644 prefixEnd_2802644 479701158479879292053627 := by
  unfold tailWord_2802644
  simp only [CollatzResearch.WordTrace]
  refine ⟨51110412229253458166379493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68147216305671277555172657 51110412229253458166379493)
  ·
    refine ⟨9583202292985023406196155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 51110412229253458166379493 9583202292985023406196155)
    ·
      refine ⟨14374803439477535109294233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9583202292985023406196155 14374803439477535109294233)
      ·
        refine ⟨10781102579608151331970675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14374803439477535109294233 10781102579608151331970675)
        ·
          refine ⟨16171653869412226997956013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10781102579608151331970675 16171653869412226997956013)
          ·
            refine ⟨6064370201029585124233505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16171653869412226997956013 6064370201029585124233505)
            ·
              refine ⟨4548277650772188843175129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6064370201029585124233505 4548277650772188843175129)
              ·
                refine ⟨3411208238079141632381347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4548277650772188843175129 3411208238079141632381347)
                ·
                  refine ⟨5116812357118712448572021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3411208238079141632381347 5116812357118712448572021)
                  ·
                    refine ⟨479701158479879292053627, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5116812357118712448572021 479701158479879292053627)
                    ·
                      rfl

theorem cell23_2802644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 3, 2, 2, 1, 5].length) (baseStart_2802644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2802644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2802644 prefixEnd_2802644 := by exact prefixLift 2802644
  have htrace : WordTrace (prefixWord ++ tailWord_2802644) baseStart_2802644 baseEnd_2802644 := by
    simpa [prefixWord, tailWord_2802644, baseEnd_2802644] using wordTrace_append hprefix tailTrace_2802644
  have hstable : (prefixWord ++ tailWord_2802644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2802644).length < 2 ^ (prefixWord ++ tailWord_2802644).sum := by decide
  have hdescent : baseEnd_2802644 < baseStart_2802644 := by decide
  rcases family_descends (prefixWord ++ tailWord_2802644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2802664 : List Nat := [2, 1, 4, 1, 1, 1, 2, 2, 5, 2, 2]
def baseStart_2802664 : Nat := 118140960795 + 2802664 * 2 ^ 59
def prefixEnd_2802664 : Nat := 4983230072969 + 3 ^ 40 * 2802664 * 2
def baseEnd_2802664 : Nat := 1439113745052727797910789

theorem tailTrace_2802664 : CollatzResearch.WordTrace tailWord_2802664 prefixEnd_2802664 1439113745052727797910789 := by
  unfold tailWord_2802664
  simp only [CollatzResearch.WordTrace]
  refine ⟨51110776959217229874243523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68147702612289639832324697 51110776959217229874243523)
  ·
    refine ⟨76666165438825844811365285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51110776959217229874243523 76666165438825844811365285)
    ·
      refine ⟨14374906019779845902130991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 76666165438825844811365285 14374906019779845902130991)
      ·
        refine ⟨21562359029669768853196487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14374906019779845902130991 21562359029669768853196487)
        ·
          refine ⟨32343538544504653279794731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21562359029669768853196487 32343538544504653279794731)
          ·
            refine ⟨48515307816756979919692097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32343538544504653279794731 48515307816756979919692097)
            ·
              refine ⟨36386480862567734939769073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48515307816756979919692097 36386480862567734939769073)
              ·
                refine ⟨27289860646925801204826805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36386480862567734939769073 27289860646925801204826805)
                ·
                  refine ⟨2558424435649293862952513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 27289860646925801204826805 2558424435649293862952513)
                  ·
                    refine ⟨1918818326736970397214385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2558424435649293862952513 1918818326736970397214385)
                    ·
                      refine ⟨1439113745052727797910789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1918818326736970397214385 1439113745052727797910789)
                      ·
                        rfl

theorem cell23_2802664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 2, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 2, 2, 5, 2, 2].length) (baseStart_2802664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2802664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2802664 prefixEnd_2802664 := by exact prefixLift 2802664
  have htrace : WordTrace (prefixWord ++ tailWord_2802664) baseStart_2802664 baseEnd_2802664 := by
    simpa [prefixWord, tailWord_2802664, baseEnd_2802664] using wordTrace_append hprefix tailTrace_2802664
  have hstable : (prefixWord ++ tailWord_2802664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2802664).length < 2 ^ (prefixWord ++ tailWord_2802664).sum := by decide
  have hdescent : baseEnd_2802664 < baseStart_2802664 := by decide
  rcases family_descends (prefixWord ++ tailWord_2802664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2802758 : List Nat := [6, 1, 1, 1, 1, 2, 2, 1, 3, 3, 2]
def baseStart_2802758 : Nat := 118140960795 + 2802758 * 2 ^ 59
def prefixEnd_2802758 : Nat := 4983230072969 + 3 ^ 40 * 2802758 * 2
def baseEnd_2802758 : Nat := 1439162012234250430135357

theorem tailTrace_2802758 : CollatzResearch.WordTrace tailWord_2802758 prefixEnd_2802758 1439162012234250430135357 := by
  unfold tailWord_2802758
  simp only [CollatzResearch.WordTrace]
  refine ⟨3194530699377934806325279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 68149988253395942534939285 3194530699377934806325279)
  ·
    refine ⟨4791796049066902209487919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3194530699377934806325279 4791796049066902209487919)
    ·
      refine ⟨7187694073600353314231879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4791796049066902209487919 7187694073600353314231879)
      ·
        refine ⟨10781541110400529971347819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7187694073600353314231879 10781541110400529971347819)
        ·
          refine ⟨16172311665600794957021729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10781541110400529971347819 16172311665600794957021729)
          ·
            refine ⟨12129233749200596217766297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16172311665600794957021729 12129233749200596217766297)
            ·
              refine ⟨9096925311900447163324723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12129233749200596217766297 9096925311900447163324723)
              ·
                refine ⟨13645387967850670744987085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9096925311900447163324723 13645387967850670744987085)
                ·
                  refine ⟨5117020487944001529370157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13645387967850670744987085 5117020487944001529370157)
                  ·
                    refine ⟨1918882682979000573513809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5117020487944001529370157 1918882682979000573513809)
                    ·
                      refine ⟨1439162012234250430135357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1918882682979000573513809 1439162012234250430135357)
                      ·
                        rfl

theorem cell23_2802758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 2, 1, 3, 3, 2].length) (baseStart_2802758 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2802758 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2802758 prefixEnd_2802758 := by exact prefixLift 2802758
  have htrace : WordTrace (prefixWord ++ tailWord_2802758) baseStart_2802758 baseEnd_2802758 := by
    simpa [prefixWord, tailWord_2802758, baseEnd_2802758] using wordTrace_append hprefix tailTrace_2802758
  have hstable : (prefixWord ++ tailWord_2802758).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2802758).length < 2 ^ (prefixWord ++ tailWord_2802758).sum := by decide
  have hdescent : baseEnd_2802758 < baseStart_2802758 := by decide
  rcases family_descends (prefixWord ++ tailWord_2802758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2802782 : List Nat := [4, 4, 1, 1, 1, 3, 1, 2, 2, 1, 3]
def baseStart_2802782 : Nat := 118140960795 + 2802782 * 2 ^ 59
def prefixEnd_2802782 : Nat := 4983230072969 + 3 ^ 40 * 2802782 * 2
def baseEnd_2802782 : Nat := 1439174335769958336235247

theorem tailTrace_2802782 : CollatzResearch.WordTrace tailWord_2802782 prefixEnd_2802782 1439174335769958336235247 := by
  unfold tailWord_2802782
  simp only [CollatzResearch.WordTrace]
  refine ⟨12778232216500870737660325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 68150571821337977267521733 12778232216500870737660325)
  ·
    refine ⟨2395918540593913263311311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12778232216500870737660325 2395918540593913263311311)
    ·
      refine ⟨3593877810890869894966967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2395918540593913263311311 3593877810890869894966967)
      ·
        refine ⟨5390816716336304842450451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3593877810890869894966967 5390816716336304842450451)
        ·
          refine ⟨8086225074504457263675677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5390816716336304842450451 8086225074504457263675677)
          ·
            refine ⟨3032334402939171473878379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8086225074504457263675677 3032334402939171473878379)
            ·
              refine ⟨4548501604408757210817569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3032334402939171473878379 4548501604408757210817569)
              ·
                refine ⟨3411376203306567908113177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4548501604408757210817569 3411376203306567908113177)
                ·
                  refine ⟨2558532152479925931084883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3411376203306567908113177 2558532152479925931084883)
                  ·
                    refine ⟨3837798228719888896627325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2558532152479925931084883 3837798228719888896627325)
                    ·
                      refine ⟨1439174335769958336235247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3837798228719888896627325 1439174335769958336235247)
                      ·
                        rfl

theorem cell23_2802782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 3, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 3, 1, 2, 2, 1, 3].length) (baseStart_2802782 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2802782 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2802782 prefixEnd_2802782 := by exact prefixLift 2802782
  have htrace : WordTrace (prefixWord ++ tailWord_2802782) baseStart_2802782 baseEnd_2802782 := by
    simpa [prefixWord, tailWord_2802782, baseEnd_2802782] using wordTrace_append hprefix tailTrace_2802782
  have hstable : (prefixWord ++ tailWord_2802782).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2802782).length < 2 ^ (prefixWord ++ tailWord_2802782).sum := by decide
  have hdescent : baseEnd_2802782 < baseStart_2802782 := by decide
  rcases family_descends (prefixWord ++ tailWord_2802782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2802794 : List Nat := [3, 1, 3, 2, 2, 2, 2, 1, 7]
def baseStart_2802794 : Nat := 118140960795 + 2802794 * 2 ^ 59
def prefixEnd_2802794 : Nat := 4983230072969 + 3 ^ 40 * 2802794 * 2
def baseEnd_2802794 : Nat := 159908944170868032142799

theorem tailTrace_2802794 : CollatzResearch.WordTrace tailWord_2802794 prefixEnd_2802794 159908944170868032142799 := by
  unfold tailWord_2802794
  simp only [CollatzResearch.WordTrace]
  refine ⟨25556573851990872987679859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68150863605308994633812957 25556573851990872987679859)
  ·
    refine ⟨38334860777986309481519789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25556573851990872987679859 38334860777986309481519789)
    ·
      refine ⟨14375572791744866055569921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38334860777986309481519789 14375572791744866055569921)
      ·
        refine ⟨10781679593808649541677441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14375572791744866055569921 10781679593808649541677441)
        ·
          refine ⟨8086259695356487156258081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10781679593808649541677441 8086259695356487156258081)
          ·
            refine ⟨6064694771517365367193561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8086259695356487156258081 6064694771517365367193561)
            ·
              refine ⟨4548521078638024025395171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6064694771517365367193561 4548521078638024025395171)
              ·
                refine ⟨6822781617957036038092757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4548521078638024025395171 6822781617957036038092757)
                ·
                  refine ⟨159908944170868032142799, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6822781617957036038092757 159908944170868032142799)
                  ·
                    rfl

theorem cell23_2802794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 2, 2, 1, 7].length) (baseStart_2802794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2802794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2802794 prefixEnd_2802794 := by exact prefixLift 2802794
  have htrace : WordTrace (prefixWord ++ tailWord_2802794) baseStart_2802794 baseEnd_2802794 := by
    simpa [prefixWord, tailWord_2802794, baseEnd_2802794] using wordTrace_append hprefix tailTrace_2802794
  have hstable : (prefixWord ++ tailWord_2802794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2802794).length < 2 ^ (prefixWord ++ tailWord_2802794).sum := by decide
  have hdescent : baseEnd_2802794 < baseStart_2802794 := by decide
  rcases family_descends (prefixWord ++ tailWord_2802794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2802805 : List Nat := [1, 3, 4, 3, 1, 2, 1, 1, 1, 4, 2]
def baseStart_2802805 : Nat := 118140960795 + 2802805 * 2 ^ 59
def prefixEnd_2802805 : Nat := 4983230072969 + 3 ^ 40 * 2802805 * 2
def baseEnd_2802805 : Nat := 1439186145825011746247641

theorem tailTrace_2802805 : CollatzResearch.WordTrace tailWord_2802805 prefixEnd_2802805 1439186145825011746247641 := by
  unfold tailWord_2802805
  simp only [CollatzResearch.WordTrace]
  refine ⟨102226696610923640829369869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68151131073949093886246579 102226696610923640829369869)
  ·
    refine ⟨38335011229096365311013701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 102226696610923640829369869 38335011229096365311013701)
    ·
      refine ⟨7187814605455568495815069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 38335011229096365311013701 7187814605455568495815069)
      ·
        refine ⟨2695430477045838185930651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7187814605455568495815069 2695430477045838185930651)
        ·
          refine ⟨4043145715568757278895977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2695430477045838185930651 4043145715568757278895977)
          ·
            refine ⟨3032359286676567959171983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4043145715568757278895977 3032359286676567959171983)
            ·
              refine ⟨4548538930014851938757975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3032359286676567959171983 4548538930014851938757975)
              ·
                refine ⟨6822808395022277908136963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4548538930014851938757975 6822808395022277908136963)
                ·
                  refine ⟨10234212592533416862205445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6822808395022277908136963 10234212592533416862205445)
                  ·
                    refine ⟨1918914861100015661663521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10234212592533416862205445 1918914861100015661663521)
                    ·
                      refine ⟨1439186145825011746247641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1918914861100015661663521 1439186145825011746247641)
                      ·
                        rfl

theorem cell23_2802805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 2, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 2, 1, 1, 1, 4, 2].length) (baseStart_2802805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2802805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2802805 prefixEnd_2802805 := by exact prefixLift 2802805
  have htrace : WordTrace (prefixWord ++ tailWord_2802805) baseStart_2802805 baseEnd_2802805 := by
    simpa [prefixWord, tailWord_2802805, baseEnd_2802805] using wordTrace_append hprefix tailTrace_2802805
  have hstable : (prefixWord ++ tailWord_2802805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2802805).length < 2 ^ (prefixWord ++ tailWord_2802805).sum := by decide
  have hdescent : baseEnd_2802805 < baseStart_2802805 := by decide
  rcases family_descends (prefixWord ++ tailWord_2802805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2802827 : List Nat := [1, 1, 1, 1, 4, 1, 1, 2, 6, 1, 4]
def baseStart_2802827 : Nat := 118140960795 + 2802827 * 2 ^ 59
def prefixEnd_2802827 : Nat := 4983230072969 + 3 ^ 40 * 2802827 * 2
def baseEnd_2802827 : Nat := 1439197442399410660172539

theorem tailTrace_2802827 : CollatzResearch.WordTrace tailWord_2802827 prefixEnd_2802827 1439197442399410660172539 := by
  unfold tailWord_2802827
  simp only [CollatzResearch.WordTrace]
  refine ⟨102227499016843938586670735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68151666011229292391113823 102227499016843938586670735)
  ·
    refine ⟨153341248525265907880006103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102227499016843938586670735 153341248525265907880006103)
    ·
      refine ⟨230011872787898861820009155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 153341248525265907880006103 230011872787898861820009155)
      ·
        refine ⟨345017809181848292730013733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 230011872787898861820009155 345017809181848292730013733)
        ·
          refine ⟨64690839221596554886877575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 345017809181848292730013733 64690839221596554886877575)
          ·
            refine ⟨97036258832394832330316363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64690839221596554886877575 97036258832394832330316363)
            ·
              refine ⟨145554388248592248495474545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 97036258832394832330316363 145554388248592248495474545)
              ·
                refine ⟨109165791186444186371605909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 145554388248592248495474545 109165791186444186371605909)
                ·
                  refine ⟨5117146461864571236169027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 109165791186444186371605909 5117146461864571236169027)
                  ·
                    refine ⟨7675719692796856854253541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5117146461864571236169027 7675719692796856854253541)
                    ·
                      refine ⟨1439197442399410660172539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7675719692796856854253541 1439197442399410660172539)
                      ·
                        rfl

theorem cell23_2802827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 2, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 2, 6, 1, 4].length) (baseStart_2802827 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2802827 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2802827 prefixEnd_2802827 := by exact prefixLift 2802827
  have htrace : WordTrace (prefixWord ++ tailWord_2802827) baseStart_2802827 baseEnd_2802827 := by
    simpa [prefixWord, tailWord_2802827, baseEnd_2802827] using wordTrace_append hprefix tailTrace_2802827
  have hstable : (prefixWord ++ tailWord_2802827).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2802827).length < 2 ^ (prefixWord ++ tailWord_2802827).sum := by decide
  have hdescent : baseEnd_2802827 < baseStart_2802827 := by decide
  rcases family_descends (prefixWord ++ tailWord_2802827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2802844 : List Nat := [2, 2, 3, 2, 1, 2, 1, 1, 4, 1, 4]
def baseStart_2802844 : Nat := 118140960795 + 2802844 * 2 ^ 59
def prefixEnd_2802844 : Nat := 4983230072969 + 3 ^ 40 * 2802844 * 2
def baseEnd_2802844 : Nat := 1439206171570537093659961

theorem tailTrace_2802844 : CollatzResearch.WordTrace tailWord_2802844 prefixEnd_2802844 1439206171570537093659961 := by
  unfold tailWord_2802844
  simp only [CollatzResearch.WordTrace]
  refine ⟨51114059528891175245019793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68152079371854900326693057 51114059528891175245019793)
  ·
    refine ⟨38335544646668381433764845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51114059528891175245019793 38335544646668381433764845)
    ·
      refine ⟨14375829242500643037661817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38335544646668381433764845 14375829242500643037661817)
      ·
        refine ⟨10781871931875482278246363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14375829242500643037661817 10781871931875482278246363)
        ·
          refine ⟨16172807897813223417369545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10781871931875482278246363 16172807897813223417369545)
          ·
            refine ⟨12129605923359917563027159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16172807897813223417369545 12129605923359917563027159)
            ·
              refine ⟨18194408885039876344540739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12129605923359917563027159 18194408885039876344540739)
              ·
                refine ⟨27291613327559814516811109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18194408885039876344540739 27291613327559814516811109)
                ·
                  refine ⟨5117177498917465221902083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27291613327559814516811109 5117177498917465221902083)
                  ·
                    refine ⟨7675766248376197832853125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5117177498917465221902083 7675766248376197832853125)
                    ·
                      refine ⟨1439206171570537093659961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7675766248376197832853125 1439206171570537093659961)
                      ·
                        rfl

theorem cell23_2802844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 1, 1, 4, 1, 4].length) (baseStart_2802844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2802844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2802844 prefixEnd_2802844 := by exact prefixLift 2802844
  have htrace : WordTrace (prefixWord ++ tailWord_2802844) baseStart_2802844 baseEnd_2802844 := by
    simpa [prefixWord, tailWord_2802844, baseEnd_2802844] using wordTrace_append hprefix tailTrace_2802844
  have hstable : (prefixWord ++ tailWord_2802844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2802844).length < 2 ^ (prefixWord ++ tailWord_2802844).sum := by decide
  have hdescent : baseEnd_2802844 < baseStart_2802844 := by decide
  rcases family_descends (prefixWord ++ tailWord_2802844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2802901 : List Nat := [1, 3, 2, 4, 1, 2, 2, 2, 6]
def baseStart_2802901 : Nat := 118140960795 + 2802901 * 2 ^ 59
def prefixEnd_2802901 : Nat := 4983230072969 + 3 ^ 40 * 2802901 * 2
def baseEnd_2802901 : Nat := 159915048885315930071911

theorem tailTrace_2802901 : CollatzResearch.WordTrace tailWord_2802901 prefixEnd_2802901 159915048885315930071911 := by
  unfold tailWord_2802901
  simp only [CollatzResearch.WordTrace]
  refine ⟨102230198018575849224864557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68153465345717232816576371 102230198018575849224864557)
  ·
    refine ⟨38336324256965943459324209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 102230198018575849224864557 38336324256965943459324209)
    ·
      refine ⟨28752243192724457594493157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38336324256965943459324209 28752243192724457594493157)
      ·
        refine ⟨5391045598635835798967467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 28752243192724457594493157 5391045598635835798967467)
        ·
          refine ⟨8086568397953753698451201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5391045598635835798967467 8086568397953753698451201)
          ·
            refine ⟨6064926298465315273838401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8086568397953753698451201 6064926298465315273838401)
            ·
              refine ⟨4548694723848986455378801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6064926298465315273838401 4548694723848986455378801)
              ·
                refine ⟨3411521042886739841534101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4548694723848986455378801 3411521042886739841534101)
                ·
                  refine ⟨159915048885315930071911, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3411521042886739841534101 159915048885315930071911)
                  ·
                    rfl

theorem cell23_2802901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 2, 2, 2, 6].length) (baseStart_2802901 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2802901 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2802901 prefixEnd_2802901 := by exact prefixLift 2802901
  have htrace : WordTrace (prefixWord ++ tailWord_2802901) baseStart_2802901 baseEnd_2802901 := by
    simpa [prefixWord, tailWord_2802901, baseEnd_2802901] using wordTrace_append hprefix tailTrace_2802901
  have hstable : (prefixWord ++ tailWord_2802901).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2802901).length < 2 ^ (prefixWord ++ tailWord_2802901).sum := by decide
  have hdescent : baseEnd_2802901 < baseStart_2802901 := by decide
  rcases family_descends (prefixWord ++ tailWord_2802901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2802944 : List Nat := [2, 1, 1, 2, 1, 1, 3, 4, 4, 4]
def baseStart_2802944 : Nat := 118140960795 + 2802944 * 2 ^ 59
def prefixEnd_2802944 : Nat := 4983230072969 + 3 ^ 40 * 2802944 * 2
def baseEnd_2802944 : Nat := 479752506545328900803167

theorem tailTrace_2802944 : CollatzResearch.WordTrace tailWord_2802944 prefixEnd_2802944 479752506545328900803167 := by
  unfold tailWord_2802944
  simp only [CollatzResearch.WordTrace]
  refine ⟨51115883178710033784339943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68154510904946711712453257 51115883178710033784339943)
  ·
    refine ⟨76673824768065050676509915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51115883178710033784339943 76673824768065050676509915)
    ·
      refine ⟨115010737152097576014764873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76673824768065050676509915 115010737152097576014764873)
      ·
        refine ⟨86258052864073182011073655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 115010737152097576014764873 86258052864073182011073655)
        ·
          refine ⟨129387079296109773016610483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86258052864073182011073655 129387079296109773016610483)
          ·
            refine ⟨194080618944164659524915725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 129387079296109773016610483 194080618944164659524915725)
            ·
              refine ⟨72780232104061747321843397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 194080618944164659524915725 72780232104061747321843397)
              ·
                refine ⟨13646293519511577622845637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 72780232104061747321843397 13646293519511577622845637)
                ·
                  refine ⟨2558680034908420804283557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13646293519511577622845637 2558680034908420804283557)
                  ·
                    refine ⟨479752506545328900803167, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2558680034908420804283557 479752506545328900803167)
                    ·
                      rfl

theorem cell23_2802944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 4, 4, 4].length) (baseStart_2802944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2802944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2802944 prefixEnd_2802944 := by exact prefixLift 2802944
  have htrace : WordTrace (prefixWord ++ tailWord_2802944) baseStart_2802944 baseEnd_2802944 := by
    simpa [prefixWord, tailWord_2802944, baseEnd_2802944] using wordTrace_append hprefix tailTrace_2802944
  have hstable : (prefixWord ++ tailWord_2802944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2802944).length < 2 ^ (prefixWord ++ tailWord_2802944).sum := by decide
  have hdescent : baseEnd_2802944 < baseStart_2802944 := by decide
  rcases family_descends (prefixWord ++ tailWord_2802944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2802945 : List Nat := [1, 2, 4, 1, 1, 4, 2, 3, 1, 1, 3]
def baseStart_2802945 : Nat := 118140960795 + 2802945 * 2 ^ 59
def prefixEnd_2802945 : Nat := 4983230072969 + 3 ^ 40 * 2802945 * 2
def baseEnd_2802945 : Nat := 1439258033116641198496997

theorem tailTrace_2802945 : CollatzResearch.WordTrace tailWord_2802945 prefixEnd_2802945 1439258033116641198496997 := by
  unfold tailWord_2802945
  simp only [CollatzResearch.WordTrace]
  refine ⟨102231802830416444739466289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68154535220277629826310859 102231802830416444739466289)
  ·
    refine ⟨76673852122812333554599717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102231802830416444739466289 76673852122812333554599717)
    ·
      refine ⟨14376347273027312541487447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 76673852122812333554599717 14376347273027312541487447)
      ·
        refine ⟨21564520909540968812231171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14376347273027312541487447 21564520909540968812231171)
        ·
          refine ⟨32346781364311453218346757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21564520909540968812231171 32346781364311453218346757)
          ·
            refine ⟨6065021505808397478440017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 32346781364311453218346757 6065021505808397478440017)
            ·
              refine ⟨4548766129356298108830013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6065021505808397478440017 4548766129356298108830013)
              ·
                refine ⟨1705787298508611790811255, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4548766129356298108830013 1705787298508611790811255)
                ·
                  refine ⟨2558680947762917686216883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1705787298508611790811255 2558680947762917686216883)
                  ·
                    refine ⟨3838021421644376529325325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2558680947762917686216883 3838021421644376529325325)
                    ·
                      refine ⟨1439258033116641198496997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3838021421644376529325325 1439258033116641198496997)
                      ·
                        rfl

theorem cell23_2802945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 4, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 4, 2, 3, 1, 1, 3].length) (baseStart_2802945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2802945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2802945 prefixEnd_2802945 := by exact prefixLift 2802945
  have htrace : WordTrace (prefixWord ++ tailWord_2802945) baseStart_2802945 baseEnd_2802945 := by
    simpa [prefixWord, tailWord_2802945, baseEnd_2802945] using wordTrace_append hprefix tailTrace_2802945
  have hstable : (prefixWord ++ tailWord_2802945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2802945).length < 2 ^ (prefixWord ++ tailWord_2802945).sum := by decide
  have hdescent : baseEnd_2802945 < baseStart_2802945 := by decide
  rcases family_descends (prefixWord ++ tailWord_2802945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2802948 : List Nat := [2, 3, 2, 2, 2, 1, 4, 1, 1, 5]
def baseStart_2802948 : Nat := 118140960795 + 2802948 * 2 ^ 59
def prefixEnd_2802948 : Nat := 4983230072969 + 3 ^ 40 * 2802948 * 2
def baseEnd_2802948 : Nat := 479753191186201562253161

theorem tailTrace_2802948 : CollatzResearch.WordTrace tailWord_2802948 prefixEnd_2802948 479753191186201562253161 := by
  unfold tailWord_2802948
  simp only [CollatzResearch.WordTrace]
  refine ⟨51115956124702788125912749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68154608166270384167883665 51115956124702788125912749)
  ·
    refine ⟨19168483546763545547217281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51115956124702788125912749 19168483546763545547217281)
    ·
      refine ⟨14376362660072659160412961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19168483546763545547217281 14376362660072659160412961)
      ·
        refine ⟨10782271995054494370309721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14376362660072659160412961 10782271995054494370309721)
        ·
          refine ⟨8086703996290870777732291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10782271995054494370309721 8086703996290870777732291)
          ·
            refine ⟨12130055994436306166598437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8086703996290870777732291 12130055994436306166598437)
            ·
              refine ⟨2274385498956807406237207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12130055994436306166598437 2274385498956807406237207)
              ·
                refine ⟨3411578248435211109355811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2274385498956807406237207 3411578248435211109355811)
                ·
                  refine ⟨5117367372652816664033717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3411578248435211109355811 5117367372652816664033717)
                  ·
                    refine ⟨479753191186201562253161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5117367372652816664033717 479753191186201562253161)
                    ·
                      rfl

theorem cell23_2802948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 4, 1, 1, 5].length) (baseStart_2802948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2802948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2802948 prefixEnd_2802948 := by exact prefixLift 2802948
  have htrace : WordTrace (prefixWord ++ tailWord_2802948) baseStart_2802948 baseEnd_2802948 := by
    simpa [prefixWord, tailWord_2802948, baseEnd_2802948] using wordTrace_append hprefix tailTrace_2802948
  have hstable : (prefixWord ++ tailWord_2802948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2802948).length < 2 ^ (prefixWord ++ tailWord_2802948).sum := by decide
  have hdescent : baseEnd_2802948 < baseStart_2802948 := by decide
  rcases family_descends (prefixWord ++ tailWord_2802948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2802954 : List Nat := [3, 1, 2, 2, 1, 1, 1, 5, 1, 1, 5]
def baseStart_2802954 : Nat := 118140960795 + 2802954 * 2 ^ 59
def prefixEnd_2802954 : Nat := 4983230072969 + 3 ^ 40 * 2802954 * 2
def baseEnd_2802954 : Nat := 1439262654442531663284455

theorem tailTrace_2802954 : CollatzResearch.WordTrace tailWord_2802954 prefixEnd_2802954 1439262654442531663284455 := by
  unfold tailWord_2802954
  simp only [CollatzResearch.WordTrace]
  refine ⟨25558032771845959819135979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68154754058255892851029277 25558032771845959819135979)
  ·
    refine ⟨38337049157768939728703969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25558032771845959819135979 38337049157768939728703969)
    ·
      refine ⟨28752786868326704796527977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38337049157768939728703969 28752786868326704796527977)
      ·
        refine ⟨21564590151245028597395983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28752786868326704796527977 21564590151245028597395983)
        ·
          refine ⟨32346885226867542896093975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21564590151245028597395983 32346885226867542896093975)
          ·
            refine ⟨48520327840301314344140963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32346885226867542896093975 48520327840301314344140963)
            ·
              refine ⟨72780491760451971516211445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48520327840301314344140963 72780491760451971516211445)
              ·
                refine ⟨6823171102542372329644823, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 72780491760451971516211445 6823171102542372329644823)
                ·
                  refine ⟨10234756653813558494467235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6823171102542372329644823 10234756653813558494467235)
                  ·
                    refine ⟨15352134980720337741700853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10234756653813558494467235 15352134980720337741700853)
                    ·
                      refine ⟨1439262654442531663284455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15352134980720337741700853 1439262654442531663284455)
                      ·
                        rfl

theorem cell23_2802954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 5, 1, 1, 5].length) (baseStart_2802954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2802954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2802954 prefixEnd_2802954 := by exact prefixLift 2802954
  have htrace : WordTrace (prefixWord ++ tailWord_2802954) baseStart_2802954 baseEnd_2802954 := by
    simpa [prefixWord, tailWord_2802954, baseEnd_2802954] using wordTrace_append hprefix tailTrace_2802954
  have hstable : (prefixWord ++ tailWord_2802954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2802954).length < 2 ^ (prefixWord ++ tailWord_2802954).sum := by decide
  have hdescent : baseEnd_2802954 < baseStart_2802954 := by decide
  rcases family_descends (prefixWord ++ tailWord_2802954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2802962 : List Nat := [3, 2, 4, 2, 1, 1, 2, 1, 3, 1, 3]
def baseStart_2802962 : Nat := 118140960795 + 2802962 * 2 ^ 59
def prefixEnd_2802962 : Nat := 4983230072969 + 3 ^ 40 * 2802962 * 2
def baseEnd_2802962 : Nat := 1439266762287767631984419

theorem tailTrace_2802962 : CollatzResearch.WordTrace tailWord_2802962 prefixEnd_2802962 1439266762287767631984419 := by
  unfold tailWord_2802962
  simp only [CollatzResearch.WordTrace]
  refine ⟨25558105717838714160708785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68154948580903237761890093 25558105717838714160708785)
  ·
    refine ⟨19168579288379035620531589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25558105717838714160708785 19168579288379035620531589)
    ·
      refine ⟨3594108616571069178849673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19168579288379035620531589 3594108616571069178849673)
      ·
        refine ⟨2695581462428301884137255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3594108616571069178849673 2695581462428301884137255)
        ·
          refine ⟨4043372193642452826205883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2695581462428301884137255 4043372193642452826205883)
          ·
            refine ⟨6065058290463679239308825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4043372193642452826205883 6065058290463679239308825)
            ·
              refine ⟨4548793717847759429481619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6065058290463679239308825 4548793717847759429481619)
              ·
                refine ⟨6823190576771639144222429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4548793717847759429481619 6823190576771639144222429)
                ·
                  refine ⟨2558696466289364679083411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6823190576771639144222429 2558696466289364679083411)
                  ·
                    refine ⟨3838044699434047018625117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2558696466289364679083411 3838044699434047018625117)
                    ·
                      refine ⟨1439266762287767631984419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3838044699434047018625117 1439266762287767631984419)
                      ·
                        rfl

theorem cell23_2802962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 1, 2, 1, 3, 1, 3].length) (baseStart_2802962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2802962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2802962 prefixEnd_2802962 := by exact prefixLift 2802962
  have htrace : WordTrace (prefixWord ++ tailWord_2802962) baseStart_2802962 baseEnd_2802962 := by
    simpa [prefixWord, tailWord_2802962, baseEnd_2802962] using wordTrace_append hprefix tailTrace_2802962
  have hstable : (prefixWord ++ tailWord_2802962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2802962).length < 2 ^ (prefixWord ++ tailWord_2802962).sum := by decide
  have hdescent : baseEnd_2802962 < baseStart_2802962 := by decide
  rcases family_descends (prefixWord ++ tailWord_2802962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2802968 : List Nat := [2, 1, 2, 3, 1, 3, 1, 3, 3, 2, 2]
def baseStart_2802968 : Nat := 118140960795 + 2802968 * 2 ^ 59
def prefixEnd_2802968 : Nat := 4983230072969 + 3 ^ 40 * 2802968 * 2
def baseEnd_2802968 : Nat := 1439269843171694608509391

theorem tailTrace_2802968 : CollatzResearch.WordTrace tailWord_2802968 prefixEnd_2802968 1439269843171694608509391 := by
  unfold tailWord_2802968
  simp only [CollatzResearch.WordTrace]
  refine ⟨51116320854666559833776779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68155094472888746445035705 51116320854666559833776779)
  ·
    refine ⟨76674481281999839750665169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51116320854666559833776779 76674481281999839750665169)
    ·
      refine ⟨57505860961499879812998877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76674481281999839750665169 57505860961499879812998877)
      ·
        refine ⟨21564697860562454929874579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 57505860961499879812998877 21564697860562454929874579)
        ·
          refine ⟨32347046790843682394811869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21564697860562454929874579 32347046790843682394811869)
          ·
            refine ⟨12130142546566380898054451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32347046790843682394811869 12130142546566380898054451)
            ·
              refine ⟨18195213819849571347081677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12130142546566380898054451 18195213819849571347081677)
              ·
                refine ⟨6823205182443589255155629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18195213819849571347081677 6823205182443589255155629)
                ·
                  refine ⟨2558701943416345970683361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6823205182443589255155629 2558701943416345970683361)
                  ·
                    refine ⟨1919026457562259478012521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2558701943416345970683361 1919026457562259478012521)
                    ·
                      refine ⟨1439269843171694608509391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1919026457562259478012521 1439269843171694608509391)
                      ·
                        rfl

theorem cell23_2802968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 1, 3, 3, 2, 2].length) (baseStart_2802968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2802968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2802968 prefixEnd_2802968 := by exact prefixLift 2802968
  have htrace : WordTrace (prefixWord ++ tailWord_2802968) baseStart_2802968 baseEnd_2802968 := by
    simpa [prefixWord, tailWord_2802968, baseEnd_2802968] using wordTrace_append hprefix tailTrace_2802968
  have hstable : (prefixWord ++ tailWord_2802968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2802968).length < 2 ^ (prefixWord ++ tailWord_2802968).sum := by decide
  have hdescent : baseEnd_2802968 < baseStart_2802968 := by decide
  rcases family_descends (prefixWord ++ tailWord_2802968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2802978 : List Nat := [3, 3, 1, 1, 4, 2, 1, 1, 1, 6]
def baseStart_2802978 : Nat := 118140960795 + 2802978 * 2 ^ 59
def prefixEnd_2802978 : Nat := 4983230072969 + 3 ^ 40 * 2802978 * 2
def baseEnd_2802978 : Nat := 479758325992746523128115

theorem tailTrace_2802978 : CollatzResearch.WordTrace tailWord_2802978 prefixEnd_2802978 479758325992746523128115 := by
  unfold tailWord_2802978
  simp only [CollatzResearch.WordTrace]
  refine ⟨25558251609824222843854397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68155337626197927583611725 25558251609824222843854397)
  ·
    refine ⟨9584344353684083566445399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25558251609824222843854397 9584344353684083566445399)
    ·
      refine ⟨14376516530526125349668099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9584344353684083566445399 14376516530526125349668099)
      ·
        refine ⟨21564774795789188024502149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14376516530526125349668099 21564774795789188024502149)
        ·
          refine ⟨4043395274210472754594153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21564774795789188024502149 4043395274210472754594153)
          ·
            refine ⟨3032546455657854565945615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4043395274210472754594153 3032546455657854565945615)
            ·
              refine ⟨4548819683486781848918423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3032546455657854565945615 4548819683486781848918423)
              ·
                refine ⟨6823229525230172773377635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4548819683486781848918423 6823229525230172773377635)
                ·
                  refine ⟨10234844287845259160066453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6823229525230172773377635 10234844287845259160066453)
                  ·
                    refine ⟨479758325992746523128115, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10234844287845259160066453 479758325992746523128115)
                    ·
                      rfl

theorem cell23_2802978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 2, 1, 1, 1, 6].length) (baseStart_2802978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2802978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2802978 prefixEnd_2802978 := by exact prefixLift 2802978
  have htrace : WordTrace (prefixWord ++ tailWord_2802978) baseStart_2802978 baseEnd_2802978 := by
    simpa [prefixWord, tailWord_2802978, baseEnd_2802978] using wordTrace_append hprefix tailTrace_2802978
  have hstable : (prefixWord ++ tailWord_2802978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2802978).length < 2 ^ (prefixWord ++ tailWord_2802978).sum := by decide
  have hdescent : baseEnd_2802978 < baseStart_2802978 := by decide
  rcases family_descends (prefixWord ++ tailWord_2802978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2802981 : List Nat := [1, 3, 1, 2, 4, 1, 3, 1, 1, 2, 4]
def baseStart_2802981 : Nat := 118140960795 + 2802981 * 2 ^ 59
def prefixEnd_2802981 : Nat := 4983230072969 + 3 ^ 40 * 2802981 * 2
def baseEnd_2802981 : Nat := 1439276518420203057646831

theorem tailTrace_2802981 : CollatzResearch.WordTrace tailWord_2802981 prefixEnd_2802981 1439276518420203057646831 := by
  unfold tailWord_2802981
  simp only [CollatzResearch.WordTrace]
  refine ⟨102233115858286022887776797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68155410572190681925184531 102233115858286022887776797)
  ·
    refine ⟨38337418446857258582916299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 102233115858286022887776797 38337418446857258582916299)
    ·
      refine ⟨57506127670285887874374449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38337418446857258582916299 57506127670285887874374449)
      ·
        refine ⟨43129595752714415905780837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57506127670285887874374449 43129595752714415905780837)
        ·
          refine ⟨8086799203633952982333907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 43129595752714415905780837 8086799203633952982333907)
          ·
            refine ⟨12130198805450929473500861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8086799203633952982333907 12130198805450929473500861)
            ·
              refine ⟨4548824552044098552562823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12130198805450929473500861 4548824552044098552562823)
              ·
                refine ⟨6823236828066147828844235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4548824552044098552562823 6823236828066147828844235)
                ·
                  refine ⟨10234855242099221743266353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6823236828066147828844235 10234855242099221743266353)
                  ·
                    refine ⟨7676141431574416307449765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10234855242099221743266353 7676141431574416307449765)
                    ·
                      refine ⟨1439276518420203057646831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7676141431574416307449765 1439276518420203057646831)
                      ·
                        rfl

theorem cell23_2802981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 3, 1, 1, 2, 4].length) (baseStart_2802981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2802981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2802981 prefixEnd_2802981 := by exact prefixLift 2802981
  have htrace : WordTrace (prefixWord ++ tailWord_2802981) baseStart_2802981 baseEnd_2802981 := by
    simpa [prefixWord, tailWord_2802981, baseEnd_2802981] using wordTrace_append hprefix tailTrace_2802981
  have hstable : (prefixWord ++ tailWord_2802981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2802981).length < 2 ^ (prefixWord ++ tailWord_2802981).sum := by decide
  have hdescent : baseEnd_2802981 < baseStart_2802981 := by decide
  rcases family_descends (prefixWord ++ tailWord_2802981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2803011 : List Nat := [1, 1, 1, 3, 1, 3, 1, 2, 5, 3, 2]
def baseStart_2803011 : Nat := 118140960795 + 2803011 * 2 ^ 59
def prefixEnd_2803011 : Nat := 4983230072969 + 3 ^ 40 * 2803011 * 2
def baseEnd_2803011 : Nat := 1439291922839837940271693

theorem tailTrace_2803011 : CollatzResearch.WordTrace tailWord_2803011 prefixEnd_2803011 1439291922839837940271693 := by
  unfold tailWord_2803011
  simp only [CollatzResearch.WordTrace]
  refine ⟨102234210048177338011368887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68156140032118225340912591 102234210048177338011368887)
  ·
    refine ⟨153351315072266007017053331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102234210048177338011368887 153351315072266007017053331)
    ·
      refine ⟨230026972608399010525579997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 153351315072266007017053331 230026972608399010525579997)
      ·
        refine ⟨86260114728149628947092499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 230026972608399010525579997 86260114728149628947092499)
        ·
          refine ⟨129390172092224443420638749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86260114728149628947092499 129390172092224443420638749)
          ·
            refine ⟨48521314534584166282739531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 129390172092224443420638749 48521314534584166282739531)
            ·
              refine ⟨72781971801876249424109297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48521314534584166282739531 72781971801876249424109297)
              ·
                refine ⟨54586478851407187068081973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 72781971801876249424109297 54586478851407187068081973)
                ·
                  refine ⟨5117482392319423787632685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 54586478851407187068081973 5117482392319423787632685)
                  ·
                    refine ⟨1919055897119783920362257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5117482392319423787632685 1919055897119783920362257)
                    ·
                      refine ⟨1439291922839837940271693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1919055897119783920362257 1439291922839837940271693)
                      ·
                        rfl

theorem cell23_2803011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 2, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 2, 5, 3, 2].length) (baseStart_2803011 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2803011 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2803011 prefixEnd_2803011 := by exact prefixLift 2803011
  have htrace : WordTrace (prefixWord ++ tailWord_2803011) baseStart_2803011 baseEnd_2803011 := by
    simpa [prefixWord, tailWord_2803011, baseEnd_2803011] using wordTrace_append hprefix tailTrace_2803011
  have hstable : (prefixWord ++ tailWord_2803011).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2803011).length < 2 ^ (prefixWord ++ tailWord_2803011).sum := by decide
  have hdescent : baseEnd_2803011 < baseStart_2803011 := by decide
  rcases family_descends (prefixWord ++ tailWord_2803011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2803024 : List Nat := [2, 1, 1, 1, 1, 5, 2, 1, 2, 3, 4]
def baseStart_2803024 : Nat := 118140960795 + 2803024 * 2 ^ 59
def prefixEnd_2803024 : Nat := 4983230072969 + 3 ^ 40 * 2803024 * 2
def baseEnd_2803024 : Nat := 1439298598088346389409133

theorem tailTrace_2803024 : CollatzResearch.WordTrace tailWord_2803024 prefixEnd_2803024 1439298598088346389409133 := by
  unfold tailWord_2803024
  simp only [CollatzResearch.WordTrace]
  refine ⟨51117342098565120615796063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68156456131420160821061417 51117342098565120615796063)
  ·
    refine ⟨76676013147847680923694095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51117342098565120615796063 76676013147847680923694095)
    ·
      refine ⟨115014019721771521385541143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76676013147847680923694095 115014019721771521385541143)
      ·
        refine ⟨172521029582657282078311715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115014019721771521385541143 172521029582657282078311715)
        ·
          refine ⟨258781544373985923117467573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 172521029582657282078311715 258781544373985923117467573)
          ·
            refine ⟨24260769785061180292262585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 258781544373985923117467573 24260769785061180292262585)
            ·
              refine ⟨18195577338795885219196939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24260769785061180292262585 18195577338795885219196939)
              ·
                refine ⟨27293366008193827828795409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18195577338795885219196939 27293366008193827828795409)
                ·
                  refine ⟨20470024506145370871596557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27293366008193827828795409 20470024506145370871596557)
                  ·
                    refine ⟨7676259189804514076848709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20470024506145370871596557 7676259189804514076848709)
                    ·
                      refine ⟨1439298598088346389409133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7676259189804514076848709 1439298598088346389409133)
                      ·
                        rfl

theorem cell23_2803024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 2, 1, 2, 3, 4].length) (baseStart_2803024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2803024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2803024 prefixEnd_2803024 := by exact prefixLift 2803024
  have htrace : WordTrace (prefixWord ++ tailWord_2803024) baseStart_2803024 baseEnd_2803024 := by
    simpa [prefixWord, tailWord_2803024, baseEnd_2803024] using wordTrace_append hprefix tailTrace_2803024
  have hstable : (prefixWord ++ tailWord_2803024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2803024).length < 2 ^ (prefixWord ++ tailWord_2803024).sum := by decide
  have hdescent : baseEnd_2803024 < baseStart_2803024 := by decide
  rcases family_descends (prefixWord ++ tailWord_2803024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2803028 : List Nat := [2, 4, 1, 1, 2, 1, 2, 2, 3, 3, 2]
def baseStart_2803028 : Nat := 118140960795 + 2803028 * 2 ^ 59
def prefixEnd_2803028 : Nat := 4983230072969 + 3 ^ 40 * 2803028 * 2
def baseEnd_2803028 : Nat := 1439300652010964373759115

theorem tailTrace_2803028 : CollatzResearch.WordTrace tailWord_2803028 prefixEnd_2803028 1439300652010964373759115 := by
  unfold tailWord_2803028
  simp only [CollatzResearch.WordTrace]
  refine ⟨51117415044557874957368869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68156553392743833276491825 51117415044557874957368869)
  ·
    refine ⟨9584515320854601554506663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 51117415044557874957368869 9584515320854601554506663)
    ·
      refine ⟨14376772981281902331759995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9584515320854601554506663 14376772981281902331759995)
      ·
        refine ⟨21565159471922853497639993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14376772981281902331759995 21565159471922853497639993)
        ·
          refine ⟨16173869603942140123229995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21565159471922853497639993 16173869603942140123229995)
          ·
            refine ⟨24260804405913210184844993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16173869603942140123229995 24260804405913210184844993)
            ·
              refine ⟨18195603304434907638633745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24260804405913210184844993 18195603304434907638633745)
              ·
                refine ⟨13646702478326180728975309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18195603304434907638633745 13646702478326180728975309)
                ·
                  refine ⟨5117513429372317773365741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13646702478326180728975309 5117513429372317773365741)
                  ·
                    refine ⟨1919067536014619165012153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5117513429372317773365741 1919067536014619165012153)
                    ·
                      refine ⟨1439300652010964373759115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1919067536014619165012153 1439300652010964373759115)
                      ·
                        rfl

theorem cell23_2803028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 2, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 2, 2, 3, 3, 2].length) (baseStart_2803028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2803028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2803028 prefixEnd_2803028 := by exact prefixLift 2803028
  have htrace : WordTrace (prefixWord ++ tailWord_2803028) baseStart_2803028 baseEnd_2803028 := by
    simpa [prefixWord, tailWord_2803028, baseEnd_2803028] using wordTrace_append hprefix tailTrace_2803028
  have hstable : (prefixWord ++ tailWord_2803028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2803028).length < 2 ^ (prefixWord ++ tailWord_2803028).sum := by decide
  have hdescent : baseEnd_2803028 < baseStart_2803028 := by decide
  rcases family_descends (prefixWord ++ tailWord_2803028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2803034 : List Nat := [3, 1, 1, 2, 1, 2, 2, 3, 2, 6]
def baseStart_2803034 : Nat := 118140960795 + 2803034 * 2 ^ 59
def prefixEnd_2803034 : Nat := 4983230072969 + 3 ^ 40 * 2803034 * 2
def baseEnd_2803034 : Nat := 479767910964963783428029

theorem tailTrace_2803034 : CollatzResearch.WordTrace tailWord_2803034 prefixEnd_2803034 479767910964963783428029 := by
  unfold tailWord_2803034
  simp only [CollatzResearch.WordTrace]
  refine ⟨25558762231773503234864039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68156699284729341959637437 25558762231773503234864039)
  ·
    refine ⟨38338143347660254852296059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25558762231773503234864039 38338143347660254852296059)
    ·
      refine ⟨57507215021490382278444089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38338143347660254852296059 57507215021490382278444089)
      ·
        refine ⟨43130411266117786708833067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57507215021490382278444089 43130411266117786708833067)
        ·
          refine ⟨64695616899176680063249601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43130411266117786708833067 64695616899176680063249601)
          ·
            refine ⟨48521712674382510047437201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64695616899176680063249601 48521712674382510047437201)
            ·
              refine ⟨36391284505786882535577901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48521712674382510047437201 36391284505786882535577901)
              ·
                refine ⟨13646731689670080950841713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36391284505786882535577901 13646731689670080950841713)
                ·
                  refine ⟨10235048767252560713131285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13646731689670080950841713 10235048767252560713131285)
                  ·
                    refine ⟨479767910964963783428029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10235048767252560713131285 479767910964963783428029)
                    ·
                      rfl

theorem cell23_2803034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 2, 3, 2, 6].length) (baseStart_2803034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2803034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2803034 prefixEnd_2803034 := by exact prefixLift 2803034
  have htrace : WordTrace (prefixWord ++ tailWord_2803034) baseStart_2803034 baseEnd_2803034 := by
    simpa [prefixWord, tailWord_2803034, baseEnd_2803034] using wordTrace_append hprefix tailTrace_2803034
  have hstable : (prefixWord ++ tailWord_2803034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2803034).length < 2 ^ (prefixWord ++ tailWord_2803034).sum := by decide
  have hdescent : baseEnd_2803034 < baseStart_2803034 := by decide
  rcases family_descends (prefixWord ++ tailWord_2803034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2803041 : List Nat := [1, 2, 3, 1, 1, 1, 1, 2, 5, 4, 2]
def baseStart_2803041 : Nat := 118140960795 + 2803041 * 2 ^ 59
def prefixEnd_2803041 : Nat := 4983230072969 + 3 ^ 40 * 2803041 * 2
def baseEnd_2803041 : Nat := 1439307327259472822896555

theorem tailTrace_2803041 : CollatzResearch.WordTrace tailWord_2803041 prefixEnd_2803041 1439307327259472822896555 := by
  unfold tailWord_2803041
  simp only [CollatzResearch.WordTrace]
  refine ⟨102235304238068653134960977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68156869492045768756640651 102235304238068653134960977)
  ·
    refine ⟨76676478178551489851220733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102235304238068653134960977 76676478178551489851220733)
    ·
      refine ⟨28753679316956808694207775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 76676478178551489851220733 28753679316956808694207775)
      ·
        refine ⟨43130518975435213041311663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28753679316956808694207775 43130518975435213041311663)
        ·
          refine ⟨64695778463152819561967495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43130518975435213041311663 64695778463152819561967495)
          ·
            refine ⟨97043667694729229342951243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64695778463152819561967495 97043667694729229342951243)
            ·
              refine ⟨145565501542093844014426865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 97043667694729229342951243 145565501542093844014426865)
              ·
                refine ⟨109174126156570383010820149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 145565501542093844014426865 109174126156570383010820149)
                ·
                  refine ⟨10235074327178473407264389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 109174126156570383010820149 10235074327178473407264389)
                  ·
                    refine ⟨1919076436345963763862073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10235074327178473407264389 1919076436345963763862073)
                    ·
                      refine ⟨1439307327259472822896555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1919076436345963763862073 1439307327259472822896555)
                      ·
                        rfl

theorem cell23_2803041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 2, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 2, 5, 4, 2].length) (baseStart_2803041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2803041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2803041 prefixEnd_2803041 := by exact prefixLift 2803041
  have htrace : WordTrace (prefixWord ++ tailWord_2803041) baseStart_2803041 baseEnd_2803041 := by
    simpa [prefixWord, tailWord_2803041, baseEnd_2803041] using wordTrace_append hprefix tailTrace_2803041
  have hstable : (prefixWord ++ tailWord_2803041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2803041).length < 2 ^ (prefixWord ++ tailWord_2803041).sum := by decide
  have hdescent : baseEnd_2803041 < baseStart_2803041 := by decide
  rcases family_descends (prefixWord ++ tailWord_2803041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2803058 : List Nat := [3, 2, 1, 2, 1, 2, 3, 2, 1, 4, 2]
def baseStart_2803058 : Nat := 118140960795 + 2803058 * 2 ^ 59
def prefixEnd_2803058 : Nat := 4983230072969 + 3 ^ 40 * 2803058 * 2
def baseEnd_2803058 : Nat := 1439316056430599256383977

theorem tailTrace_2803058 : CollatzResearch.WordTrace tailWord_2803058 prefixEnd_2803058 1439316056430599256383977 := by
  unfold tailWord_2803058
  simp only [CollatzResearch.WordTrace]
  refine ⟨25558981069751766259582457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68157282852671376692219885 25558981069751766259582457)
  ·
    refine ⟨19169235802313824694686843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25558981069751766259582457 19169235802313824694686843)
    ·
      refine ⟨28753853703470737042030265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19169235802313824694686843 28753853703470737042030265)
      ·
        refine ⟨21565390277603052781522699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28753853703470737042030265 21565390277603052781522699)
        ·
          refine ⟨32348085416404579172284049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21565390277603052781522699 32348085416404579172284049)
          ·
            refine ⟨24261064062303434379213037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32348085416404579172284049 24261064062303434379213037)
            ·
              refine ⟨9097899023363787892204889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24261064062303434379213037 9097899023363787892204889)
              ·
                refine ⟨6823424267522840919153667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9097899023363787892204889 6823424267522840919153667)
                ·
                  refine ⟨10235136401284261378730501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6823424267522840919153667 10235136401284261378730501)
                  ·
                    refine ⟨1919088075240799008511969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10235136401284261378730501 1919088075240799008511969)
                    ·
                      refine ⟨1439316056430599256383977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1919088075240799008511969 1439316056430599256383977)
                      ·
                        rfl

theorem cell23_2803058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 3, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 3, 2, 1, 4, 2].length) (baseStart_2803058 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2803058 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2803058 prefixEnd_2803058 := by exact prefixLift 2803058
  have htrace : WordTrace (prefixWord ++ tailWord_2803058) baseStart_2803058 baseEnd_2803058 := by
    simpa [prefixWord, tailWord_2803058, baseEnd_2803058] using wordTrace_append hprefix tailTrace_2803058
  have hstable : (prefixWord ++ tailWord_2803058).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2803058).length < 2 ^ (prefixWord ++ tailWord_2803058).sum := by decide
  have hdescent : baseEnd_2803058 < baseStart_2803058 := by decide
  rcases family_descends (prefixWord ++ tailWord_2803058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2803070 : List Nat := [4, 2, 3, 2, 2, 1, 2, 2, 1, 2, 2]
def baseStart_2803070 : Nat := 118140960795 + 2803070 * 2 ^ 59
def prefixEnd_2803070 : Nat := 4983230072969 + 3 ^ 40 * 2803070 * 2
def baseEnd_2803070 : Nat := 1439322218198453209433923

theorem tailTrace_2803070 : CollatzResearch.WordTrace tailWord_2803070 prefixEnd_2803070 1439322218198453209433923 := by
  unfold tailWord_2803070
  simp only [CollatzResearch.WordTrace]
  refine ⟨12779545244370448885970833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 68157574636642394058511109 12779545244370448885970833)
  ·
    refine ⟨9584658933277836664478125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12779545244370448885970833 9584658933277836664478125)
    ·
      refine ⟨3594247099979188749179297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9584658933277836664478125 3594247099979188749179297)
      ·
        refine ⟨2695685324984391561884473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3594247099979188749179297 2695685324984391561884473)
        ·
          refine ⟨2021763993738293671413355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2695685324984391561884473 2021763993738293671413355)
          ·
            refine ⟨3032645990607440507120033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2021763993738293671413355 3032645990607440507120033)
            ·
              refine ⟨2274484492955580380340025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3032645990607440507120033 2274484492955580380340025)
              ·
                refine ⟨1705863369716685285255019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2274484492955580380340025 1705863369716685285255019)
                ·
                  refine ⟨2558795054575027927882529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1705863369716685285255019 2558795054575027927882529)
                  ·
                    refine ⟨1919096290931270945911897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2558795054575027927882529 1919096290931270945911897)
                    ·
                      refine ⟨1439322218198453209433923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1919096290931270945911897 1439322218198453209433923)
                      ·
                        rfl

theorem cell23_2803070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 2, 1, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 2, 1, 2, 2, 1, 2, 2].length) (baseStart_2803070 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2803070 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2803070 prefixEnd_2803070 := by exact prefixLift 2803070
  have htrace : WordTrace (prefixWord ++ tailWord_2803070) baseStart_2803070 baseEnd_2803070 := by
    simpa [prefixWord, tailWord_2803070, baseEnd_2803070] using wordTrace_append hprefix tailTrace_2803070
  have hstable : (prefixWord ++ tailWord_2803070).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2803070).length < 2 ^ (prefixWord ++ tailWord_2803070).sum := by decide
  have hdescent : baseEnd_2803070 < baseStart_2803070 := by decide
  rcases family_descends (prefixWord ++ tailWord_2803070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2803075 : List Nat := [1, 1, 1, 3, 5, 1, 1, 4, 2, 2, 2]
def baseStart_2803075 : Nat := 118140960795 + 2803075 * 2 ^ 59
def prefixEnd_2803075 : Nat := 4983230072969 + 3 ^ 40 * 2803075 * 2
def baseEnd_2803075 : Nat := 1439324785601725689871399

theorem tailTrace_2803075 : CollatzResearch.WordTrace tailWord_2803075 prefixEnd_2803075 1439324785601725689871399 := by
  unfold tailWord_2803075
  simp only [CollatzResearch.WordTrace]
  refine ⟨102236544319945476941698679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68157696213296984627799119 102236544319945476941698679)
  ·
    refine ⟨153354816479918215412548019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102236544319945476941698679 153354816479918215412548019)
    ·
      refine ⟨230032224719877323118822029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 153354816479918215412548019 230032224719877323118822029)
      ·
        refine ⟨86262084269953996169558261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 230032224719877323118822029 86262084269953996169558261)
        ·
          refine ⟨8087070400308187140896087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 86262084269953996169558261 8087070400308187140896087)
          ·
            refine ⟨12130605600462280711344131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8087070400308187140896087 12130605600462280711344131)
            ·
              refine ⟨18195908400693421067016197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12130605600462280711344131 18195908400693421067016197)
              ·
                refine ⟨3411732825130016450065537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18195908400693421067016197 3411732825130016450065537)
                ·
                  refine ⟨2558799618847512337549153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3411732825130016450065537 2558799618847512337549153)
                  ·
                    refine ⟨1919099714135634253161865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2558799618847512337549153 1919099714135634253161865)
                    ·
                      refine ⟨1439324785601725689871399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1919099714135634253161865 1439324785601725689871399)
                      ·
                        rfl

theorem cell23_2803075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 1, 4, 2, 2, 2].length) (baseStart_2803075 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2803075 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2803075 prefixEnd_2803075 := by exact prefixLift 2803075
  have htrace : WordTrace (prefixWord ++ tailWord_2803075) baseStart_2803075 baseEnd_2803075 := by
    simpa [prefixWord, tailWord_2803075, baseEnd_2803075] using wordTrace_append hprefix tailTrace_2803075
  have hstable : (prefixWord ++ tailWord_2803075).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2803075).length < 2 ^ (prefixWord ++ tailWord_2803075).sum := by decide
  have hdescent : baseEnd_2803075 < baseStart_2803075 := by decide
  rcases family_descends (prefixWord ++ tailWord_2803075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2803092 : List Nat := [2, 4, 2, 1, 2, 1, 2, 3, 2, 2, 2]
def baseStart_2803092 : Nat := 118140960795 + 2803092 * 2 ^ 59
def prefixEnd_2803092 : Nat := 4983230072969 + 3 ^ 40 * 2803092 * 2
def baseEnd_2803092 : Nat := 1439333514772852123358821

theorem tailTrace_2803092 : CollatzResearch.WordTrace tailWord_2803092 prefixEnd_2803092 1439333514772852123358821 := by
  unfold tailWord_2803092
  simp only [CollatzResearch.WordTrace]
  refine ⟨51118582180441944422533765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68158109573922592563378353 51118582180441944422533765)
  ·
    refine ⟨9584734158832864579225081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 51118582180441944422533765 9584734158832864579225081)
    ·
      refine ⟨7188550619124648434418811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9584734158832864579225081 7188550619124648434418811)
      ·
        refine ⟨10782825928686972651628217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7188550619124648434418811 10782825928686972651628217)
        ·
          refine ⟨8087119446515229488721163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10782825928686972651628217 8087119446515229488721163)
          ·
            refine ⟨12130679169772844233081745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8087119446515229488721163 12130679169772844233081745)
            ·
              refine ⟨9098009377329633174811309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12130679169772844233081745 9098009377329633174811309)
              ·
                refine ⟨3411753516498612440554241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9098009377329633174811309 3411753516498612440554241)
                ·
                  refine ⟨2558815137373959330415681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3411753516498612440554241 2558815137373959330415681)
                  ·
                    refine ⟨1919111353030469497811761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2558815137373959330415681 1919111353030469497811761)
                    ·
                      refine ⟨1439333514772852123358821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1919111353030469497811761 1439333514772852123358821)
                      ·
                        rfl

theorem cell23_2803092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 2, 3, 2, 2, 2].length) (baseStart_2803092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2803092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2803092 prefixEnd_2803092 := by exact prefixLift 2803092
  have htrace : WordTrace (prefixWord ++ tailWord_2803092) baseStart_2803092 baseEnd_2803092 := by
    simpa [prefixWord, tailWord_2803092, baseEnd_2803092] using wordTrace_append hprefix tailTrace_2803092
  have hstable : (prefixWord ++ tailWord_2803092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2803092).length < 2 ^ (prefixWord ++ tailWord_2803092).sum := by decide
  have hdescent : baseEnd_2803092 < baseStart_2803092 := by decide
  rcases family_descends (prefixWord ++ tailWord_2803092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2803111 : List Nat := [1, 1, 6, 1, 1, 1, 3, 1, 1, 7]
def baseStart_2803111 : Nat := 118140960795 + 2803111 * 2 ^ 59
def prefixEnd_2803111 : Nat := 4983230072969 + 3 ^ 40 * 2803111 * 2
def baseEnd_2803111 : Nat := 479781090301762516340411

theorem tailTrace_2803111 : CollatzResearch.WordTrace tailWord_2803111 prefixEnd_2803111 479781090301762516340411 := by
  unfold tailWord_2803111
  simp only [CollatzResearch.WordTrace]
  refine ⟨102237857347815055090009187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68158571565210036726672791 102237857347815055090009187)
  ·
    refine ⟨153356786021722582635013781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102237857347815055090009187 153356786021722582635013781)
    ·
      refine ⟨7188599344768246061016271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 153356786021722582635013781 7188599344768246061016271)
      ·
        refine ⟨10782899017152369091524407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7188599344768246061016271 10782899017152369091524407)
        ·
          refine ⟨16174348525728553637286611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10782899017152369091524407 16174348525728553637286611)
          ·
            refine ⟨24261522788592830455929917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16174348525728553637286611 24261522788592830455929917)
            ·
              refine ⟨9098071045722311420973719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24261522788592830455929917 9098071045722311420973719)
              ·
                refine ⟨13647106568583467131460579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9098071045722311420973719 13647106568583467131460579)
                ·
                  refine ⟨20470659852875200697190869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13647106568583467131460579 20470659852875200697190869)
                  ·
                    refine ⟨479781090301762516340411, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 20470659852875200697190869 479781090301762516340411)
                    ·
                      rfl

theorem cell23_2803111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 3, 1, 1, 7].length) (baseStart_2803111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2803111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2803111 prefixEnd_2803111 := by exact prefixLift 2803111
  have htrace : WordTrace (prefixWord ++ tailWord_2803111) baseStart_2803111 baseEnd_2803111 := by
    simpa [prefixWord, tailWord_2803111, baseEnd_2803111] using wordTrace_append hprefix tailTrace_2803111
  have hstable : (prefixWord ++ tailWord_2803111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2803111).length < 2 ^ (prefixWord ++ tailWord_2803111).sum := by decide
  have hdescent : baseEnd_2803111 < baseStart_2803111 := by decide
  rcases family_descends (prefixWord ++ tailWord_2803111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
