import V185TrunkScan23Chunk0647

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_3831048 : List Nat := [2, 1, 3, 2, 4, 1, 1, 1, 3, 1, 4]
def baseStart_3831048 : Nat := 118140960795 + 3831048 * 2 ^ 59
def prefixEnd_3831048 : Nat := 4983230072969 + 3 ^ 40 * 3831048 * 2
def baseEnd_3831048 : Nat := 1967169034446032240781337

theorem tailTrace_3831048 : CollatzResearch.WordTrace tailWord_3831048 prefixEnd_3831048 1967169034446032240781337 := by
  unfold tailWord_3831048
  simp only [CollatzResearch.WordTrace]
  refine ⟨69864899912387430876374899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93153199883183241168499865 69864899912387430876374899)
  ·
    refine ⟨104797349868581146314562349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69864899912387430876374899 104797349868581146314562349)
    ·
      refine ⟨39299006200717929867960881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 104797349868581146314562349 39299006200717929867960881)
      ·
        refine ⟨29474254650538447400970661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39299006200717929867960881 29474254650538447400970661)
        ·
          refine ⟨5526422746975958887681999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29474254650538447400970661 5526422746975958887681999)
          ·
            refine ⟨8289634120463938331522999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5526422746975958887681999 8289634120463938331522999)
            ·
              refine ⟨12434451180695907497284499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8289634120463938331522999 12434451180695907497284499)
              ·
                refine ⟨18651676771043861245926749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12434451180695907497284499 18651676771043861245926749)
                ·
                  refine ⟨6994378789141447967222531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18651676771043861245926749 6994378789141447967222531)
                  ·
                    refine ⟨10491568183712171950833797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6994378789141447967222531 10491568183712171950833797)
                    ·
                      refine ⟨1967169034446032240781337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10491568183712171950833797 1967169034446032240781337)
                      ·
                        rfl

theorem cell23_3831048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 1, 1, 1, 3, 1, 4].length) (baseStart_3831048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3831048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3831048 prefixEnd_3831048 := by exact prefixLift 3831048
  have htrace : WordTrace (prefixWord ++ tailWord_3831048) baseStart_3831048 baseEnd_3831048 := by
    simpa [prefixWord, tailWord_3831048, baseEnd_3831048] using wordTrace_append hprefix tailTrace_3831048
  have hstable : (prefixWord ++ tailWord_3831048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3831048).length < 2 ^ (prefixWord ++ tailWord_3831048).sum := by decide
  have hdescent : baseEnd_3831048 < baseStart_3831048 := by decide
  rcases family_descends (prefixWord ++ tailWord_3831048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3831068 : List Nat := [2, 2, 3, 1, 1, 1, 2, 5, 1, 2, 3]
def baseStart_3831068 : Nat := 118140960795 + 3831068 * 2 ^ 59
def prefixEnd_3831068 : Nat := 4983230072969 + 3 ^ 40 * 3831068 * 2
def baseEnd_3831068 : Nat := 1967179304059122162531245

theorem tailTrace_3831068 : CollatzResearch.WordTrace tailWord_3831068 prefixEnd_3831068 1967179304059122162531245 := by
  unfold tailWord_3831068
  simp only [CollatzResearch.WordTrace]
  refine ⟨69865264642351202584238929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93153686189801603445651905 69865264642351202584238929)
  ·
    refine ⟨52398948481763401938179197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69865264642351202584238929 52398948481763401938179197)
    ·
      refine ⟨19649605680661275726817199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52398948481763401938179197 19649605680661275726817199)
      ·
        refine ⟨29474408520991913590225799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19649605680661275726817199 29474408520991913590225799)
        ·
          refine ⟨44211612781487870385338699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29474408520991913590225799 44211612781487870385338699)
          ·
            refine ⟨66317419172231805578008049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44211612781487870385338699 66317419172231805578008049)
            ·
              refine ⟨49738064379173854183506037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66317419172231805578008049 49738064379173854183506037)
              ·
                refine ⟨4662943535547548829703691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 49738064379173854183506037 4662943535547548829703691)
                ·
                  refine ⟨6994415303321323244555537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4662943535547548829703691 6994415303321323244555537)
                  ·
                    refine ⟨5245811477490992433416653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6994415303321323244555537 5245811477490992433416653)
                    ·
                      refine ⟨1967179304059122162531245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5245811477490992433416653 1967179304059122162531245)
                      ·
                        rfl

theorem cell23_3831068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 2, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 2, 5, 1, 2, 3].length) (baseStart_3831068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3831068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3831068 prefixEnd_3831068 := by exact prefixLift 3831068
  have htrace : WordTrace (prefixWord ++ tailWord_3831068) baseStart_3831068 baseEnd_3831068 := by
    simpa [prefixWord, tailWord_3831068, baseEnd_3831068] using wordTrace_append hprefix tailTrace_3831068
  have hstable : (prefixWord ++ tailWord_3831068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3831068).length < 2 ^ (prefixWord ++ tailWord_3831068).sum := by decide
  have hdescent : baseEnd_3831068 < baseStart_3831068 := by decide
  rcases family_descends (prefixWord ++ tailWord_3831068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3831071 : List Nat := [1, 1, 2, 4, 5, 10]
def baseStart_3831071 : Nat := 118140960795 + 3831071 * 2 ^ 59
def prefixEnd_3831071 : Nat := 4983230072969 + 3 ^ 40 * 3831071 * 2
def baseEnd_3831071 : Nat := 8095394421815167287217

theorem tailTrace_3831071 : CollatzResearch.WordTrace tailWord_3831071 prefixEnd_3831071 8095394421815167287217 := by
  unfold tailWord_3831071
  simp only [CollatzResearch.WordTrace]
  refine ⟨139730638703691536680837067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93153759135794357787224711 139730638703691536680837067)
  ·
    refine ⟨209595958055537305021255601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139730638703691536680837067 209595958055537305021255601)
    ·
      refine ⟨157196968541652978765941701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 209595958055537305021255601 157196968541652978765941701)
      ·
        refine ⟨29474431601559933518614069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 157196968541652978765941701 29474431601559933518614069)
        ·
          refine ⟨2763227962646243767370069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 29474431601559933518614069 2763227962646243767370069)
          ·
            refine ⟨8095394421815167287217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 2763227962646243767370069 8095394421815167287217)
            ·
              rfl

theorem cell23_3831071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 5, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 5, 10].length) (baseStart_3831071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3831071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3831071 prefixEnd_3831071 := by exact prefixLift 3831071
  have htrace : WordTrace (prefixWord ++ tailWord_3831071) baseStart_3831071 baseEnd_3831071 := by
    simpa [prefixWord, tailWord_3831071, baseEnd_3831071] using wordTrace_append hprefix tailTrace_3831071
  have hstable : (prefixWord ++ tailWord_3831071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3831071).length < 2 ^ (prefixWord ++ tailWord_3831071).sum := by decide
  have hdescent : baseEnd_3831071 < baseStart_3831071 := by decide
  rcases family_descends (prefixWord ++ tailWord_3831071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3831085 : List Nat := [1, 5, 3, 1, 1, 1, 1, 2, 3, 2, 3]
def baseStart_3831085 : Nat := 118140960795 + 3831085 * 2 ^ 59
def prefixEnd_3831085 : Nat := 4983230072969 + 3 ^ 40 * 3831085 * 2
def baseEnd_3831085 : Nat := 1967188033230248596018667

theorem tailTrace_3831085 : CollatzResearch.WordTrace tailWord_3831085 prefixEnd_3831085 1967188033230248596018667 := by
  unfold tailWord_3831085
  simp only [CollatzResearch.WordTrace]
  refine ⟨139731149325640817071846709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93154099550427211381231139 139731149325640817071846709)
  ·
    refine ⟨13099795249278826600485629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 139731149325640817071846709 13099795249278826600485629)
    ·
      refine ⟨4912423218479559975182111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13099795249278826600485629 4912423218479559975182111)
      ·
        refine ⟨7368634827719339962773167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4912423218479559975182111 7368634827719339962773167)
        ·
          refine ⟨11052952241579009944159751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7368634827719339962773167 11052952241579009944159751)
          ·
            refine ⟨16579428362368514916239627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11052952241579009944159751 16579428362368514916239627)
            ·
              refine ⟨24869142543552772374359441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16579428362368514916239627 24869142543552772374359441)
              ·
                refine ⟨18651856907664579280769581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24869142543552772374359441 18651856907664579280769581)
                ·
                  refine ⟨6994446340374217230288593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18651856907664579280769581 6994446340374217230288593)
                  ·
                    refine ⟨5245834755280662922716445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6994446340374217230288593 5245834755280662922716445)
                    ·
                      refine ⟨1967188033230248596018667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5245834755280662922716445 1967188033230248596018667)
                      ·
                        rfl

theorem cell23_3831085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 1, 2, 3, 2, 3].length) (baseStart_3831085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3831085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3831085 prefixEnd_3831085 := by exact prefixLift 3831085
  have htrace : WordTrace (prefixWord ++ tailWord_3831085) baseStart_3831085 baseEnd_3831085 := by
    simpa [prefixWord, tailWord_3831085, baseEnd_3831085] using wordTrace_append hprefix tailTrace_3831085
  have hstable : (prefixWord ++ tailWord_3831085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3831085).length < 2 ^ (prefixWord ++ tailWord_3831085).sum := by decide
  have hdescent : baseEnd_3831085 < baseStart_3831085 := by decide
  rcases family_descends (prefixWord ++ tailWord_3831085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3831098 : List Nat := [3, 1, 1, 1, 4, 1, 4, 1, 1, 3, 3]
def baseStart_3831098 : Nat := 118140960795 + 3831098 * 2 ^ 59
def prefixEnd_3831098 : Nat := 4983230072969 + 3 ^ 40 * 3831098 * 2
def baseEnd_3831098 : Nat := 1967194708478757045156107

theorem tailTrace_3831098 : CollatzResearch.WordTrace tailWord_3831098 prefixEnd_3831098 1967194708478757045156107 := by
  unfold tailWord_3831098
  simp only [CollatzResearch.WordTrace]
  refine ⟨34932905868648430073017487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93154415649729146861379965 34932905868648430073017487)
  ·
    refine ⟨52399358802972645109526231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34932905868648430073017487 52399358802972645109526231)
    ·
      refine ⟨78599038204458967664289347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52399358802972645109526231 78599038204458967664289347)
      ·
        refine ⟨117898557306688451496434021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78599038204458967664289347 117898557306688451496434021)
        ·
          refine ⟨22105979495004084655581379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 117898557306688451496434021 22105979495004084655581379)
          ·
            refine ⟨33158969242506126983372069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22105979495004084655581379 33158969242506126983372069)
            ·
              refine ⟨6217306732969898809382263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33158969242506126983372069 6217306732969898809382263)
              ·
                refine ⟨9325960099454848214073395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6217306732969898809382263 9325960099454848214073395)
                ·
                  refine ⟨13988940149182272321110093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9325960099454848214073395 13988940149182272321110093)
                  ·
                    refine ⟨5245852555943352120416285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13988940149182272321110093 5245852555943352120416285)
                    ·
                      refine ⟨1967194708478757045156107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5245852555943352120416285 1967194708478757045156107)
                      ·
                        rfl

theorem cell23_3831098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 4, 1, 1, 3, 3].length) (baseStart_3831098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3831098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3831098 prefixEnd_3831098 := by exact prefixLift 3831098
  have htrace : WordTrace (prefixWord ++ tailWord_3831098) baseStart_3831098 baseEnd_3831098 := by
    simpa [prefixWord, tailWord_3831098, baseEnd_3831098] using wordTrace_append hprefix tailTrace_3831098
  have hstable : (prefixWord ++ tailWord_3831098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3831098).length < 2 ^ (prefixWord ++ tailWord_3831098).sum := by decide
  have hdescent : baseEnd_3831098 < baseStart_3831098 := by decide
  rcases family_descends (prefixWord ++ tailWord_3831098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3831151 : List Nat := [1, 1, 2, 1, 3, 1, 3, 3, 2, 2, 4]
def baseStart_3831151 : Nat := 118140960795 + 3831151 * 2 ^ 59
def prefixEnd_3831151 : Nat := 4983230072969 + 3 ^ 40 * 3831151 * 2
def baseEnd_3831151 : Nat := 1967221922953445337793363

theorem tailTrace_3831151 : CollatzResearch.WordTrace tailWord_3831151 prefixEnd_3831151 1967221922953445337793363 := by
  unfold tailWord_3831151
  simp only [CollatzResearch.WordTrace]
  refine ⟨139733556543401710343749307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93155704362267806895832871 139733556543401710343749307)
  ·
    refine ⟨209600334815102565515623961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139733556543401710343749307 209600334815102565515623961)
    ·
      refine ⟨157200251111326924136717971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 209600334815102565515623961 157200251111326924136717971)
      ·
        refine ⟨235800376666990386205076957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157200251111326924136717971 235800376666990386205076957)
        ·
          refine ⟨88425141250121394826903859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 235800376666990386205076957 88425141250121394826903859)
          ·
            refine ⟨132637711875182092240355789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88425141250121394826903859 132637711875182092240355789)
            ·
              refine ⟨49739141953193284590133421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 132637711875182092240355789 49739141953193284590133421)
              ·
                refine ⟨18652178232447481721300033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49739141953193284590133421 18652178232447481721300033)
                ·
                  refine ⟨13989133674335611290975025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18652178232447481721300033 13989133674335611290975025)
                  ·
                    refine ⟨10491850255751708468231269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13989133674335611290975025 10491850255751708468231269)
                    ·
                      refine ⟨1967221922953445337793363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10491850255751708468231269 1967221922953445337793363)
                      ·
                        rfl

theorem cell23_3831151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 3, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 3, 3, 2, 2, 4].length) (baseStart_3831151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3831151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3831151 prefixEnd_3831151 := by exact prefixLift 3831151
  have htrace : WordTrace (prefixWord ++ tailWord_3831151) baseStart_3831151 baseEnd_3831151 := by
    simpa [prefixWord, tailWord_3831151, baseEnd_3831151] using wordTrace_append hprefix tailTrace_3831151
  have hstable : (prefixWord ++ tailWord_3831151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3831151).length < 2 ^ (prefixWord ++ tailWord_3831151).sum := by decide
  have hdescent : baseEnd_3831151 < baseStart_3831151 := by decide
  rcases family_descends (prefixWord ++ tailWord_3831151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3831161 : List Nat := [1, 2, 1, 3, 2, 1, 4, 2, 7]
def baseStart_3831161 : Nat := 118140960795 + 3831161 * 2 ^ 59
def prefixEnd_3831161 : Nat := 4983230072969 + 3 ^ 40 * 3831161 * 2
def baseEnd_3831161 : Nat := 218580784195554477629813

theorem tailTrace_3831161 : CollatzResearch.WordTrace tailWord_3831161 prefixEnd_3831161 218580784195554477629813 := by
  unfold tailWord_3831161
  simp only [CollatzResearch.WordTrace]
  refine ⟨139733921273365482051613337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93155947515576988034408891 139733921273365482051613337)
  ·
    refine ⟨104800440955024111538710003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139733921273365482051613337 104800440955024111538710003)
    ·
      refine ⟨157200661432536167308065005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104800440955024111538710003 157200661432536167308065005)
      ·
        refine ⟨58950248037201062740524377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 157200661432536167308065005 58950248037201062740524377)
        ·
          refine ⟨44212686027900797055393283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58950248037201062740524377 44212686027900797055393283)
          ·
            refine ⟨66319029041851195583089925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44212686027900797055393283 66319029041851195583089925)
            ·
              refine ⟨12434817945347099171829361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 66319029041851195583089925 12434817945347099171829361)
              ·
                refine ⟨9326113459010324378872021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12434817945347099171829361 9326113459010324378872021)
                ·
                  refine ⟨218580784195554477629813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9326113459010324378872021 218580784195554477629813)
                  ·
                    rfl

theorem cell23_3831161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 4, 2, 7].length) (baseStart_3831161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3831161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3831161 prefixEnd_3831161 := by exact prefixLift 3831161
  have htrace : WordTrace (prefixWord ++ tailWord_3831161) baseStart_3831161 baseEnd_3831161 := by
    simpa [prefixWord, tailWord_3831161, baseEnd_3831161] using wordTrace_append hprefix tailTrace_3831161
  have hstable : (prefixWord ++ tailWord_3831161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3831161).length < 2 ^ (prefixWord ++ tailWord_3831161).sum := by decide
  have hdescent : baseEnd_3831161 < baseStart_3831161 := by decide
  rcases family_descends (prefixWord ++ tailWord_3831161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3831225 : List Nat := [1, 2, 1, 4, 4, 1, 2, 1, 2, 5]
def baseStart_3831225 : Nat := 118140960795 + 3831225 * 2 ^ 59
def prefixEnd_3831225 : Nat := 4983230072969 + 3 ^ 40 * 3831225 * 2
def baseEnd_3831225 : Nat := 655753306840626016089341

theorem tailTrace_3831225 : CollatzResearch.WordTrace tailWord_3831225 prefixEnd_3831225 655753306840626016089341 := by
  unfold tailWord_3831225
  simp only [CollatzResearch.WordTrace]
  refine ⟨139736255545133620981943129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93157503696755747321295419 139736255545133620981943129)
  ·
    refine ⟨104802191658850215736457347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139736255545133620981943129 104802191658850215736457347)
    ·
      refine ⟨157203287488275323604686021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104802191658850215736457347 157203287488275323604686021)
      ·
        refine ⟨29475616404051623175878629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 157203287488275323604686021 29475616404051623175878629)
        ·
          refine ⟨5526678075759679345477243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29475616404051623175878629 5526678075759679345477243)
          ·
            refine ⟨8290017113639519018215865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5526678075759679345477243 8290017113639519018215865)
            ·
              refine ⟨6217512835229639263661899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8290017113639519018215865 6217512835229639263661899)
              ·
                refine ⟨9326269252844458895492849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6217512835229639263661899 9326269252844458895492849)
                ·
                  refine ⟨6994701939633344171619637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9326269252844458895492849 6994701939633344171619637)
                  ·
                    refine ⟨655753306840626016089341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6994701939633344171619637 655753306840626016089341)
                    ·
                      rfl

theorem cell23_3831225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 1, 2, 1, 2, 5].length) (baseStart_3831225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3831225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3831225 prefixEnd_3831225 := by exact prefixLift 3831225
  have htrace : WordTrace (prefixWord ++ tailWord_3831225) baseStart_3831225 baseEnd_3831225 := by
    simpa [prefixWord, tailWord_3831225, baseEnd_3831225] using wordTrace_append hprefix tailTrace_3831225
  have hstable : (prefixWord ++ tailWord_3831225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3831225).length < 2 ^ (prefixWord ++ tailWord_3831225).sum := by decide
  have hdescent : baseEnd_3831225 < baseStart_3831225 := by decide
  rcases family_descends (prefixWord ++ tailWord_3831225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3831241 : List Nat := [1, 2, 1, 1, 2, 1, 3, 3, 2, 1, 6]
def baseStart_3831241 : Nat := 118140960795 + 3831241 * 2 ^ 59
def prefixEnd_3831241 : Nat := 4983230072969 + 3 ^ 40 * 3831241 * 2
def baseEnd_3831241 : Nat := 1967268136212349985667949

theorem tailTrace_3831241 : CollatzResearch.WordTrace tailWord_3831241 prefixEnd_3831241 1967268136212349985667949 := by
  unfold tailWord_3831241
  simp only [CollatzResearch.WordTrace]
  refine ⟨139736839113075655714525577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93157892742050437143017051 139736839113075655714525577)
  ·
    refine ⟨104802629334806741785894183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139736839113075655714525577 104802629334806741785894183)
    ·
      refine ⟨157203944002210112678841275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104802629334806741785894183 157203944002210112678841275)
      ·
        refine ⟨235805916003315169018261913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157203944002210112678841275 235805916003315169018261913)
        ·
          refine ⟨176854437002486376763696435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 235805916003315169018261913 176854437002486376763696435)
          ·
            refine ⟨265281655503729565145544653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 176854437002486376763696435 265281655503729565145544653)
            ·
              refine ⟨99480620813898586929579245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 265281655503729565145544653 99480620813898586929579245)
              ·
                refine ⟨37305232805211970098592217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 99480620813898586929579245 37305232805211970098592217)
                ·
                  refine ⟨27978924603908977573944163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37305232805211970098592217 27978924603908977573944163)
                  ·
                    refine ⟨41968386905863466360916245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27978924603908977573944163 41968386905863466360916245)
                    ·
                      refine ⟨1967268136212349985667949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 41968386905863466360916245 1967268136212349985667949)
                      ·
                        rfl

theorem cell23_3831241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 3, 2, 1, 6].length) (baseStart_3831241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3831241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3831241 prefixEnd_3831241 := by exact prefixLift 3831241
  have htrace : WordTrace (prefixWord ++ tailWord_3831241) baseStart_3831241 baseEnd_3831241 := by
    simpa [prefixWord, tailWord_3831241, baseEnd_3831241] using wordTrace_append hprefix tailTrace_3831241
  have hstable : (prefixWord ++ tailWord_3831241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3831241).length < 2 ^ (prefixWord ++ tailWord_3831241).sum := by decide
  have hdescent : baseEnd_3831241 < baseStart_3831241 := by decide
  rcases family_descends (prefixWord ++ tailWord_3831241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3831282 : List Nat := [3, 2, 1, 4, 1, 1, 3, 1, 2, 2, 3]
def baseStart_3831282 : Nat := 118140960795 + 3831282 * 2 ^ 59
def prefixEnd_3831282 : Nat := 4983230072969 + 3 ^ 40 * 3831282 * 2
def baseEnd_3831282 : Nat := 1967289188919184325255261

theorem tailTrace_3831282 : CollatzResearch.WordTrace tailWord_3831282 prefixEnd_3831282 1967289188919184325255261 := by
  unfold tailWord_3831282
  simp only [CollatzResearch.WordTrace]
  refine ⟨34934583626481779929192025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93158889670618079811178733 34934583626481779929192025)
  ·
    refine ⟨26200937719861334946894019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34934583626481779929192025 26200937719861334946894019)
    ·
      refine ⟨39301406579792002420341029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26200937719861334946894019 39301406579792002420341029)
      ·
        refine ⟨7369013733711000453813943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 39301406579792002420341029 7369013733711000453813943)
        ·
          refine ⟨11053520600566500680720915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7369013733711000453813943 11053520600566500680720915)
          ·
            refine ⟨16580280900849751021081373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11053520600566500680720915 16580280900849751021081373)
            ·
              refine ⟨6217605337818656632905515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16580280900849751021081373 6217605337818656632905515)
              ·
                refine ⟨9326408006727984949358273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6217605337818656632905515 9326408006727984949358273)
                ·
                  refine ⟨6994806005045988712018705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9326408006727984949358273 6994806005045988712018705)
                  ·
                    refine ⟨5246104503784491534014029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6994806005045988712018705 5246104503784491534014029)
                    ·
                      refine ⟨1967289188919184325255261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5246104503784491534014029 1967289188919184325255261)
                      ·
                        rfl

theorem cell23_3831282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 3, 1, 2, 2, 3].length) (baseStart_3831282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3831282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3831282 prefixEnd_3831282 := by exact prefixLift 3831282
  have htrace : WordTrace (prefixWord ++ tailWord_3831282) baseStart_3831282 baseEnd_3831282 := by
    simpa [prefixWord, tailWord_3831282, baseEnd_3831282] using wordTrace_append hprefix tailTrace_3831282
  have hstable : (prefixWord ++ tailWord_3831282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3831282).length < 2 ^ (prefixWord ++ tailWord_3831282).sum := by decide
  have hdescent : baseEnd_3831282 < baseStart_3831282 := by decide
  rcases family_descends (prefixWord ++ tailWord_3831282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3831291 : List Nat := [1, 1, 1, 1, 1, 3, 2, 2, 1, 3, 7]
def baseStart_3831291 : Nat := 118140960795 + 3831291 * 2 ^ 59
def prefixEnd_3831291 : Nat := 4983230072969 + 3 ^ 40 * 3831291 * 2
def baseEnd_3831291 : Nat := 1967293810245074790042719

theorem tailTrace_3831291 : CollatzResearch.WordTrace tailWord_3831291 prefixEnd_3831291 1967293810245074790042719 := by
  unfold tailWord_3831291
  simp only [CollatzResearch.WordTrace]
  refine ⟨139738662762894514253845727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93159108508596342835897151 139738662762894514253845727)
  ·
    refine ⟨209607994144341771380768591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139738662762894514253845727 209607994144341771380768591)
    ·
      refine ⟨314411991216512657071152887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209607994144341771380768591 314411991216512657071152887)
      ·
        refine ⟨471617986824768985606729331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 314411991216512657071152887 471617986824768985606729331)
        ·
          refine ⟨707426980237153478410093997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 471617986824768985606729331 707426980237153478410093997)
          ·
            refine ⟨265285117588932554403785249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 707426980237153478410093997 265285117588932554403785249)
            ·
              refine ⟨198963838191699415802838937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 265285117588932554403785249 198963838191699415802838937)
              ·
                refine ⟨149222878643774561852129203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 198963838191699415802838937 149222878643774561852129203)
                ·
                  refine ⟨223834317965661842778193805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 149222878643774561852129203 223834317965661842778193805)
                  ·
                    refine ⟨83937869237123191041822677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 223834317965661842778193805 83937869237123191041822677)
                    ·
                      refine ⟨1967293810245074790042719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 83937869237123191041822677 1967293810245074790042719)
                      ·
                        rfl

theorem cell23_3831291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 2, 1, 3, 7].length) (baseStart_3831291 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3831291 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3831291 prefixEnd_3831291 := by exact prefixLift 3831291
  have htrace : WordTrace (prefixWord ++ tailWord_3831291) baseStart_3831291 baseEnd_3831291 := by
    simpa [prefixWord, tailWord_3831291, baseEnd_3831291] using wordTrace_append hprefix tailTrace_3831291
  have hstable : (prefixWord ++ tailWord_3831291).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3831291).length < 2 ^ (prefixWord ++ tailWord_3831291).sum := by decide
  have hdescent : baseEnd_3831291 < baseStart_3831291 := by decide
  rcases family_descends (prefixWord ++ tailWord_3831291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3831305 : List Nat := [1, 2, 1, 1, 3, 1, 4, 1, 4, 3, 2]
def baseStart_3831305 : Nat := 118140960795 + 3831305 * 2 ^ 59
def prefixEnd_3831305 : Nat := 4983230072969 + 3 ^ 40 * 3831305 * 2
def baseEnd_3831305 : Nat := 1967300998974237735267655

theorem tailTrace_3831305 : CollatzResearch.WordTrace tailWord_3831305 prefixEnd_3831305 1967300998974237735267655 := by
  unfold tailWord_3831305
  simp only [CollatzResearch.WordTrace]
  refine ⟨139739173384843794644855369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93159448923229196429903579 139739173384843794644855369)
  ·
    refine ⟨104804380038632845983641527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139739173384843794644855369 104804380038632845983641527)
    ·
      refine ⟨157206570057949268975462291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104804380038632845983641527 157206570057949268975462291)
      ·
        refine ⟨235809855086923903463193437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157206570057949268975462291 235809855086923903463193437)
        ·
          refine ⟨88428695657596463798697539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 235809855086923903463193437 88428695657596463798697539)
          ·
            refine ⟨132643043486394695698046309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88428695657596463798697539 132643043486394695698046309)
            ·
              refine ⟨24870570653699005443383683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 132643043486394695698046309 24870570653699005443383683)
              ·
                refine ⟨37305855980548508165075525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24870570653699005443383683 37305855980548508165075525)
                ·
                  refine ⟨6994847996352845280951661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37305855980548508165075525 6994847996352845280951661)
                  ·
                    refine ⟨2623067998632316980356873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6994847996352845280951661 2623067998632316980356873)
                    ·
                      refine ⟨1967300998974237735267655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2623067998632316980356873 1967300998974237735267655)
                      ·
                        rfl

theorem cell23_3831305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 4, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 4, 1, 4, 3, 2].length) (baseStart_3831305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3831305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3831305 prefixEnd_3831305 := by exact prefixLift 3831305
  have htrace : WordTrace (prefixWord ++ tailWord_3831305) baseStart_3831305 baseEnd_3831305 := by
    simpa [prefixWord, tailWord_3831305, baseEnd_3831305] using wordTrace_append hprefix tailTrace_3831305
  have hstable : (prefixWord ++ tailWord_3831305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3831305).length < 2 ^ (prefixWord ++ tailWord_3831305).sum := by decide
  have hdescent : baseEnd_3831305 < baseStart_3831305 := by decide
  rcases family_descends (prefixWord ++ tailWord_3831305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3831369 : List Nat := [1, 2, 1, 1, 2, 2, 1, 8, 1, 2, 2]
def baseStart_3831369 : Nat := 118140960795 + 3831369 * 2 ^ 59
def prefixEnd_3831369 : Nat := 4983230072969 + 3 ^ 40 * 3831369 * 2
def baseEnd_3831369 : Nat := 1967333861736125484867361

theorem tailTrace_3831369 : CollatzResearch.WordTrace tailWord_3831369 prefixEnd_3831369 1967333861736125484867361 := by
  unfold tailWord_3831369
  simp only [CollatzResearch.WordTrace]
  refine ⟨139741507656611933575185161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93161005104407955716790107 139741507656611933575185161)
  ·
    refine ⟨104806130742458950181388871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139741507656611933575185161 104806130742458950181388871)
    ·
      refine ⟨157209196113688425272083307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104806130742458950181388871 157209196113688425272083307)
      ·
        refine ⟨235813794170532637908124961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157209196113688425272083307 235813794170532637908124961)
        ·
          refine ⟨176860345627899478431093721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 235813794170532637908124961 176860345627899478431093721)
          ·
            refine ⟨132645259220924608823320291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 176860345627899478431093721 132645259220924608823320291)
            ·
              refine ⟨198967888831386913234980437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 132645259220924608823320291 198967888831386913234980437)
              ·
                refine ⟨2331654947242815389472427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 198967888831386913234980437 2331654947242815389472427)
                ·
                  refine ⟨3497482420864223084208641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2331654947242815389472427 3497482420864223084208641)
                  ·
                    refine ⟨2623111815648167313156481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3497482420864223084208641 2623111815648167313156481)
                    ·
                      refine ⟨1967333861736125484867361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2623111815648167313156481 1967333861736125484867361)
                      ·
                        rfl

theorem cell23_3831369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 8, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 8, 1, 2, 2].length) (baseStart_3831369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3831369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3831369 prefixEnd_3831369 := by exact prefixLift 3831369
  have htrace : WordTrace (prefixWord ++ tailWord_3831369) baseStart_3831369 baseEnd_3831369 := by
    simpa [prefixWord, tailWord_3831369, baseEnd_3831369] using wordTrace_append hprefix tailTrace_3831369
  have hstable : (prefixWord ++ tailWord_3831369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3831369).length < 2 ^ (prefixWord ++ tailWord_3831369).sum := by decide
  have hdescent : baseEnd_3831369 < baseStart_3831369 := by decide
  rcases family_descends (prefixWord ++ tailWord_3831369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3831402 : List Nat := [3, 1, 3, 2, 1, 3, 1, 2, 1, 3, 3]
def baseStart_3831402 : Nat := 118140960795 + 3831402 * 2 ^ 59
def prefixEnd_3831402 : Nat := 4983230072969 + 3 ^ 40 * 3831402 * 2
def baseEnd_3831402 : Nat := 1967350806597723855754709

theorem tailTrace_3831402 : CollatzResearch.WordTrace tailWord_3831402 prefixEnd_3831402 1967350806597723855754709 := by
  unfold tailWord_3831402
  simp only [CollatzResearch.WordTrace]
  refine ⟨34935677816373095052784115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93161807510328253474090973 34935677816373095052784115)
  ·
    refine ⟨52403516724559642579176173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34935677816373095052784115 52403516724559642579176173)
    ·
      refine ⟨19651318771709865967191065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52403516724559642579176173 19651318771709865967191065)
      ·
        refine ⟨14738489078782399475393299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19651318771709865967191065 14738489078782399475393299)
        ·
          refine ⟨22107733618173599213089949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14738489078782399475393299 22107733618173599213089949)
          ·
            refine ⟨8290400106815099704908731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22107733618173599213089949 8290400106815099704908731)
            ·
              refine ⟨12435600160222649557363097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8290400106815099704908731 12435600160222649557363097)
              ·
                refine ⟨9326700120166987168022323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12435600160222649557363097 9326700120166987168022323)
                ·
                  refine ⟨13990050180250480752033485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9326700120166987168022323 13990050180250480752033485)
                  ·
                    refine ⟨5246268817593930282012557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13990050180250480752033485 5246268817593930282012557)
                    ·
                      refine ⟨1967350806597723855754709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5246268817593930282012557 1967350806597723855754709)
                      ·
                        rfl

theorem cell23_3831402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 3, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 3, 1, 2, 1, 3, 3].length) (baseStart_3831402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3831402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3831402 prefixEnd_3831402 := by exact prefixLift 3831402
  have htrace : WordTrace (prefixWord ++ tailWord_3831402) baseStart_3831402 baseEnd_3831402 := by
    simpa [prefixWord, tailWord_3831402, baseEnd_3831402] using wordTrace_append hprefix tailTrace_3831402
  have hstable : (prefixWord ++ tailWord_3831402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3831402).length < 2 ^ (prefixWord ++ tailWord_3831402).sum := by decide
  have hdescent : baseEnd_3831402 < baseStart_3831402 := by decide
  rcases family_descends (prefixWord ++ tailWord_3831402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3831406 : List Nat := [4, 1, 2, 2, 3, 1, 3, 1, 1, 2, 3]
def baseStart_3831406 : Nat := 118140960795 + 3831406 * 2 ^ 59
def prefixEnd_3831406 : Nat := 4983230072969 + 3 ^ 40 * 3831406 * 2
def baseEnd_3831406 : Nat := 1967352860520341840104691

theorem tailTrace_3831406 : CollatzResearch.WordTrace tailWord_3831406 prefixEnd_3831406 1967352860520341840104691 := by
  unfold tailWord_3831406
  simp only [CollatzResearch.WordTrace]
  refine ⟨17467857144684736111785259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 93161904771651925929521381 17467857144684736111785259)
  ·
    refine ⟨26201785717027104167677889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17467857144684736111785259 26201785717027104167677889)
    ·
      refine ⟨19651339287770328125758417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26201785717027104167677889 19651339287770328125758417)
      ·
        refine ⟨14738504465827746094318813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19651339287770328125758417 14738504465827746094318813)
        ·
          refine ⟨5526939174685404785369555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14738504465827746094318813 5526939174685404785369555)
          ·
            refine ⟨8290408762028107178054333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5526939174685404785369555 8290408762028107178054333)
            ·
              refine ⟨3108903285760540191770375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8290408762028107178054333 3108903285760540191770375)
              ·
                refine ⟨4663354928640810287655563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3108903285760540191770375 4663354928640810287655563)
                ·
                  refine ⟨6995032392961215431483345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4663354928640810287655563 6995032392961215431483345)
                  ·
                    refine ⟨5246274294720911573612509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6995032392961215431483345 5246274294720911573612509)
                    ·
                      refine ⟨1967352860520341840104691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5246274294720911573612509 1967352860520341840104691)
                      ·
                        rfl

theorem cell23_3831406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 1, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 1, 3, 1, 1, 2, 3].length) (baseStart_3831406 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3831406 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3831406 prefixEnd_3831406 := by exact prefixLift 3831406
  have htrace : WordTrace (prefixWord ++ tailWord_3831406) baseStart_3831406 baseEnd_3831406 := by
    simpa [prefixWord, tailWord_3831406, baseEnd_3831406] using wordTrace_append hprefix tailTrace_3831406
  have hstable : (prefixWord ++ tailWord_3831406).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3831406).length < 2 ^ (prefixWord ++ tailWord_3831406).sum := by decide
  have hdescent : baseEnd_3831406 < baseStart_3831406 := by decide
  rcases family_descends (prefixWord ++ tailWord_3831406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3831425 : List Nat := [1, 2, 4, 2, 1, 2, 1, 1, 2, 3, 4]
def baseStart_3831425 : Nat := 118140960795 + 3831425 * 2 ^ 59
def prefixEnd_3831425 : Nat := 4983230072969 + 3 ^ 40 * 3831425 * 2
def baseEnd_3831425 : Nat := 1967362616652777265767103

theorem tailTrace_3831425 : CollatzResearch.WordTrace tailWord_3831425 prefixEnd_3831425 1967362616652777265767103 := by
  unfold tailWord_3831425
  simp only [CollatzResearch.WordTrace]
  refine ⟨139743550144409055139223729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93162366762939370092815819 139743550144409055139223729)
  ·
    refine ⟨104807662608306791354417797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139743550144409055139223729 104807662608306791354417797)
    ·
      refine ⟨19651436739057523378953337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 104807662608306791354417797 19651436739057523378953337)
      ·
        refine ⟨14738577554293142534215003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19651436739057523378953337 14738577554293142534215003)
        ·
          refine ⟨22107866331439713801322505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14738577554293142534215003 22107866331439713801322505)
          ·
            refine ⟨16580899748579785350991879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22107866331439713801322505 16580899748579785350991879)
            ·
              refine ⟨24871349622869678026487819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16580899748579785350991879 24871349622869678026487819)
              ·
                refine ⟨37307024434304517039731729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24871349622869678026487819 37307024434304517039731729)
                ·
                  refine ⟨27980268325728387779798797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37307024434304517039731729 27980268325728387779798797)
                  ·
                    refine ⟨10492600622148145417424549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27980268325728387779798797 10492600622148145417424549)
                    ·
                      refine ⟨1967362616652777265767103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10492600622148145417424549 1967362616652777265767103)
                      ·
                        rfl

theorem cell23_3831425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 1, 1, 2, 3, 4].length) (baseStart_3831425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3831425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3831425 prefixEnd_3831425 := by exact prefixLift 3831425
  have htrace : WordTrace (prefixWord ++ tailWord_3831425) baseStart_3831425 baseEnd_3831425 := by
    simpa [prefixWord, tailWord_3831425, baseEnd_3831425] using wordTrace_append hprefix tailTrace_3831425
  have hstable : (prefixWord ++ tailWord_3831425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3831425).length < 2 ^ (prefixWord ++ tailWord_3831425).sum := by decide
  have hdescent : baseEnd_3831425 < baseStart_3831425 := by decide
  rcases family_descends (prefixWord ++ tailWord_3831425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3831470 : List Nat := [4, 1, 4, 1, 3, 1, 1, 2, 2, 1, 3]
def baseStart_3831470 : Nat := 118140960795 + 3831470 * 2 ^ 59
def prefixEnd_3831470 : Nat := 4983230072969 + 3 ^ 40 * 3831470 * 2
def baseEnd_3831470 : Nat := 1967385723282229589704397

theorem tailTrace_3831470 : CollatzResearch.WordTrace tailWord_3831470 prefixEnd_3831470 1967385723282229589704397 := by
  unfold tailWord_3831470
  simp only [CollatzResearch.WordTrace]
  refine ⟨17468148928655753478076483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 93163460952830685216407909 17468148928655753478076483)
  ·
    refine ⟨26202223392983630217114725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17468148928655753478076483 26202223392983630217114725)
    ·
      refine ⟨4912916886184430665709011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26202223392983630217114725 4912916886184430665709011)
      ·
        refine ⟨7369375329276645998563517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4912916886184430665709011 7369375329276645998563517)
        ·
          refine ⟨2763515748478742249461319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7369375329276645998563517 2763515748478742249461319)
          ·
            refine ⟨4145273622718113374191979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2763515748478742249461319 4145273622718113374191979)
            ·
              refine ⟨6217910434077170061287969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4145273622718113374191979 6217910434077170061287969)
              ·
                refine ⟨4663432825557877545965977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6217910434077170061287969 4663432825557877545965977)
                ·
                  refine ⟨3497574619168408159474483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4663432825557877545965977 3497574619168408159474483)
                  ·
                    refine ⟨5246361928752612239211725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3497574619168408159474483 5246361928752612239211725)
                    ·
                      refine ⟨1967385723282229589704397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5246361928752612239211725 1967385723282229589704397)
                      ·
                        rfl

theorem cell23_3831470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 3, 1, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 3, 1, 1, 2, 2, 1, 3].length) (baseStart_3831470 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3831470 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3831470 prefixEnd_3831470 := by exact prefixLift 3831470
  have htrace : WordTrace (prefixWord ++ tailWord_3831470) baseStart_3831470 baseEnd_3831470 := by
    simpa [prefixWord, tailWord_3831470, baseEnd_3831470] using wordTrace_append hprefix tailTrace_3831470
  have hstable : (prefixWord ++ tailWord_3831470).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3831470).length < 2 ^ (prefixWord ++ tailWord_3831470).sum := by decide
  have hdescent : baseEnd_3831470 < baseStart_3831470 := by decide
  rcases family_descends (prefixWord ++ tailWord_3831470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3831475 : List Nat := [1, 1, 1, 2, 3, 3, 1, 1, 4, 3, 3]
def baseStart_3831475 : Nat := 118140960795 + 3831475 * 2 ^ 59
def prefixEnd_3831475 : Nat := 4983230072969 + 3 ^ 40 * 3831475 * 2
def baseEnd_3831475 : Nat := 1967388290685502070141873

theorem tailTrace_3831475 : CollatzResearch.WordTrace tailWord_3831475 prefixEnd_3831475 1967388290685502070141873 := by
  unfold tailWord_3831475
  simp only [CollatzResearch.WordTrace]
  refine ⟨139745373794227913678543879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93163582529485275785695919 139745373794227913678543879)
  ·
    refine ⟨209618060691341870517815819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139745373794227913678543879 209618060691341870517815819)
    ·
      refine ⟨314427091037012805776723729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209618060691341870517815819 314427091037012805776723729)
      ·
        refine ⟨235820318277759604332542797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 314427091037012805776723729 235820318277759604332542797)
        ·
          refine ⟨88432619354159851624703549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 235820318277759604332542797 88432619354159851624703549)
          ·
            refine ⟨33162232257809944359263831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 88432619354159851624703549 33162232257809944359263831)
            ·
              refine ⟨49743348386714916538895747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33162232257809944359263831 49743348386714916538895747)
              ·
                refine ⟨74615022580072374808343621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49743348386714916538895747 74615022580072374808343621)
                ·
                  refine ⟨13990316733763570276564429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 74615022580072374808343621 13990316733763570276564429)
                  ·
                    refine ⟨5246368775161338853711661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13990316733763570276564429 5246368775161338853711661)
                    ·
                      refine ⟨1967388290685502070141873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5246368775161338853711661 1967388290685502070141873)
                      ·
                        rfl

theorem cell23_3831475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 1, 1, 4, 3, 3].length) (baseStart_3831475 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3831475 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3831475 prefixEnd_3831475 := by exact prefixLift 3831475
  have htrace : WordTrace (prefixWord ++ tailWord_3831475) baseStart_3831475 baseEnd_3831475 := by
    simpa [prefixWord, tailWord_3831475, baseEnd_3831475] using wordTrace_append hprefix tailTrace_3831475
  have hstable : (prefixWord ++ tailWord_3831475).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3831475).length < 2 ^ (prefixWord ++ tailWord_3831475).sum := by decide
  have hdescent : baseEnd_3831475 < baseStart_3831475 := by decide
  rcases family_descends (prefixWord ++ tailWord_3831475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3831482 : List Nat := [3, 1, 1, 1, 2, 4, 2, 4, 5]
def baseStart_3831482 : Nat := 118140960795 + 3831482 * 2 ^ 59
def prefixEnd_3831482 : Nat := 4983230072969 + 3 ^ 40 * 3831482 * 2
def baseEnd_3831482 : Nat := 218599098338898171417149

theorem tailTrace_3831482 : CollatzResearch.WordTrace tailWord_3831482 prefixEnd_3831482 218599098338898171417149 := by
  unfold tailWord_3831482
  simp only [CollatzResearch.WordTrace]
  refine ⟨34936407276300638468512175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93163752736801702582699133 34936407276300638468512175)
  ·
    refine ⟨52404610914450957702768263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34936407276300638468512175 52404610914450957702768263)
    ·
      refine ⟨78606916371676436554152395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52404610914450957702768263 78606916371676436554152395)
      ·
        refine ⟨117910374557514654831228593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78606916371676436554152395 117910374557514654831228593)
        ·
          refine ⟨88432780918135991123421445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 117910374557514654831228593 88432780918135991123421445)
          ·
            refine ⟨16581146422150498335641521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 88432780918135991123421445 16581146422150498335641521)
            ·
              refine ⟨12435859816612873751731141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16581146422150498335641521 12435859816612873751731141)
              ·
                refine ⟨2331723715614913828449589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12435859816612873751731141 2331723715614913828449589)
                ·
                  refine ⟨218599098338898171417149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2331723715614913828449589 218599098338898171417149)
                  ·
                    rfl

theorem cell23_3831482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 2, 4, 5].length) (baseStart_3831482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3831482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3831482 prefixEnd_3831482 := by exact prefixLift 3831482
  have htrace : WordTrace (prefixWord ++ tailWord_3831482) baseStart_3831482 baseEnd_3831482 := by
    simpa [prefixWord, tailWord_3831482, baseEnd_3831482] using wordTrace_append hprefix tailTrace_3831482
  have hstable : (prefixWord ++ tailWord_3831482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3831482).length < 2 ^ (prefixWord ++ tailWord_3831482).sum := by decide
  have hdescent : baseEnd_3831482 < baseStart_3831482 := by decide
  rcases family_descends (prefixWord ++ tailWord_3831482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3831492 : List Nat := [2, 3, 3, 1, 1, 1, 1, 3, 2, 3, 3]
def baseStart_3831492 : Nat := 118140960795 + 3831492 * 2 ^ 59
def prefixEnd_3831492 : Nat := 4983230072969 + 3 ^ 40 * 3831492 * 2
def baseEnd_3831492 : Nat := 1967397019856628503629295

theorem tailTrace_3831492 : CollatzResearch.WordTrace tailWord_3831492 prefixEnd_3831492 1967397019856628503629295 := by
  unfold tailWord_3831492
  simp only [CollatzResearch.WordTrace]
  refine ⟨69872996917583162790956365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93163995890110883721275153 69872996917583162790956365)
  ·
    refine ⟨26202373844093686046608637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69872996917583162790956365 26202373844093686046608637)
    ·
      refine ⟨9825890191535132267478239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26202373844093686046608637 9825890191535132267478239)
      ·
        refine ⟨14738835287302698401217359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9825890191535132267478239 14738835287302698401217359)
        ·
          refine ⟨22108252930954047601826039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14738835287302698401217359 22108252930954047601826039)
          ·
            refine ⟨33162379396431071402739059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22108252930954047601826039 33162379396431071402739059)
            ·
              refine ⟨49743569094646607104108589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33162379396431071402739059 49743569094646607104108589)
              ·
                refine ⟨18653838410492477664040721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49743569094646607104108589 18653838410492477664040721)
                ·
                  refine ⟨13990378807869358248030541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18653838410492477664040721 13990378807869358248030541)
                  ·
                    refine ⟨5246392052951009343011453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13990378807869358248030541 5246392052951009343011453)
                    ·
                      refine ⟨1967397019856628503629295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5246392052951009343011453 1967397019856628503629295)
                      ·
                        rfl

theorem cell23_3831492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 1, 3, 2, 3, 3].length) (baseStart_3831492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3831492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3831492 prefixEnd_3831492 := by exact prefixLift 3831492
  have htrace : WordTrace (prefixWord ++ tailWord_3831492) baseStart_3831492 baseEnd_3831492 := by
    simpa [prefixWord, tailWord_3831492, baseEnd_3831492] using wordTrace_append hprefix tailTrace_3831492
  have hstable : (prefixWord ++ tailWord_3831492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3831492).length < 2 ^ (prefixWord ++ tailWord_3831492).sum := by decide
  have hdescent : baseEnd_3831492 < baseStart_3831492 := by decide
  rcases family_descends (prefixWord ++ tailWord_3831492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3831532 : List Nat := [2, 2, 1, 1, 2, 2, 2, 1, 4, 4, 2]
def baseStart_3831532 : Nat := 118140960795 + 3831532 * 2 ^ 59
def prefixEnd_3831532 : Nat := 4983230072969 + 3 ^ 40 * 3831532 * 2
def baseEnd_3831532 : Nat := 1967417559082808347129111

theorem tailTrace_3831532 : CollatzResearch.WordTrace tailWord_3831532 prefixEnd_3831532 1967417559082808347129111 := by
  unfold tailWord_3831532
  simp only [CollatzResearch.WordTrace]
  refine ⟨69873726377510706206684425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93164968503347608275579233 69873726377510706206684425)
  ·
    refine ⟨52405294783133029655013319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69873726377510706206684425 52405294783133029655013319)
    ·
      refine ⟨78607942174699544482519979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52405294783133029655013319 78607942174699544482519979)
      ·
        refine ⟨117911913262049316723779969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78607942174699544482519979 117911913262049316723779969)
        ·
          refine ⟨88433934946536987542834977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 117911913262049316723779969 88433934946536987542834977)
          ·
            refine ⟨66325451209902740657126233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 88433934946536987542834977 66325451209902740657126233)
            ·
              refine ⟨49744088407427055492844675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66325451209902740657126233 49744088407427055492844675)
              ·
                refine ⟨74616132611140583239267013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49744088407427055492844675 74616132611140583239267013)
                ·
                  refine ⟨13990524864588859357362565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 74616132611140583239267013 13990524864588859357362565)
                  ·
                    refine ⟨2623223412110411129505481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13990524864588859357362565 2623223412110411129505481)
                    ·
                      refine ⟨1967417559082808347129111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2623223412110411129505481 1967417559082808347129111)
                      ·
                        rfl

theorem cell23_3831532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 4, 2].length) (baseStart_3831532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3831532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3831532 prefixEnd_3831532 := by exact prefixLift 3831532
  have htrace : WordTrace (prefixWord ++ tailWord_3831532) baseStart_3831532 baseEnd_3831532 := by
    simpa [prefixWord, tailWord_3831532, baseEnd_3831532] using wordTrace_append hprefix tailTrace_3831532
  have hstable : (prefixWord ++ tailWord_3831532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3831532).length < 2 ^ (prefixWord ++ tailWord_3831532).sum := by decide
  have hdescent : baseEnd_3831532 < baseStart_3831532 := by decide
  rcases family_descends (prefixWord ++ tailWord_3831532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3831602 : List Nat := [3, 2, 1, 1, 3, 2, 1, 2, 3, 5]
def baseStart_3831602 : Nat := 118140960795 + 3831602 * 2 ^ 59
def prefixEnd_3831602 : Nat := 4983230072969 + 3 ^ 40 * 3831602 * 2
def baseEnd_3831602 : Nat := 655817834242874357751263

theorem tailTrace_3831602 : CollatzResearch.WordTrace tailWord_3831602 prefixEnd_3831602 655817834242874357751263 := by
  unfold tailWord_3831602
  simp only [CollatzResearch.WordTrace]
  refine ⟨34937501466191953592104265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93166670576511876245611373 34937501466191953592104265)
  ·
    refine ⟨26203126099643965194078199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34937501466191953592104265 26203126099643965194078199)
    ·
      refine ⟨39304689149465947791117299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26203126099643965194078199 39304689149465947791117299)
      ·
        refine ⟨58957033724198921686675949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39304689149465947791117299 58957033724198921686675949)
        ·
          refine ⟨22108887646574595632503481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58957033724198921686675949 22108887646574595632503481)
          ·
            refine ⟨16581665734930946724377611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22108887646574595632503481 16581665734930946724377611)
            ·
              refine ⟨24872498602396420086566417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16581665734930946724377611 24872498602396420086566417)
              ·
                refine ⟨18654373951797315064924813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24872498602396420086566417 18654373951797315064924813)
                ·
                  refine ⟨6995390231923993149346805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18654373951797315064924813 6995390231923993149346805)
                  ·
                    refine ⟨655817834242874357751263, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6995390231923993149346805 655817834242874357751263)
                    ·
                      rfl

theorem cell23_3831602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 1, 2, 3, 5].length) (baseStart_3831602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3831602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3831602 prefixEnd_3831602 := by exact prefixLift 3831602
  have htrace : WordTrace (prefixWord ++ tailWord_3831602) baseStart_3831602 baseEnd_3831602 := by
    simpa [prefixWord, tailWord_3831602, baseEnd_3831602] using wordTrace_append hprefix tailTrace_3831602
  have hstable : (prefixWord ++ tailWord_3831602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3831602).length < 2 ^ (prefixWord ++ tailWord_3831602).sum := by decide
  have hdescent : baseEnd_3831602 < baseStart_3831602 := by decide
  rcases family_descends (prefixWord ++ tailWord_3831602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3831632 : List Nat := [2, 1, 1, 1, 1, 4, 1, 4, 4, 4]
def baseStart_3831632 : Nat := 118140960795 + 3831632 * 2 ^ 59
def prefixEnd_3831632 : Nat := 4983230072969 + 3 ^ 40 * 3831632 * 2
def baseEnd_3831632 : Nat := 655822969049419318626217

theorem tailTrace_3831632 : CollatzResearch.WordTrace tailWord_3831632 prefixEnd_3831632 655822969049419318626217 := by
  unfold tailWord_3831632
  simp only [CollatzResearch.WordTrace]
  refine ⟨69875550027329564746004575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93167400036439419661339433 69875550027329564746004575)
  ·
    refine ⟨104813325040994347119006863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69875550027329564746004575 104813325040994347119006863)
    ·
      refine ⟨157219987561491520678510295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104813325040994347119006863 157219987561491520678510295)
      ·
        refine ⟨235829981342237281017765443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157219987561491520678510295 235829981342237281017765443)
        ·
          refine ⟨353744972013355921526648165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 235829981342237281017765443 353744972013355921526648165)
          ·
            refine ⟨66327182252504235286246531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 353744972013355921526648165 66327182252504235286246531)
            ·
              refine ⟨99490773378756352929369797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66327182252504235286246531 99490773378756352929369797)
              ·
                refine ⟨18654520008516816174256837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 99490773378756352929369797 18654520008516816174256837)
                ·
                  refine ⟨3497722501596903032673157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18654520008516816174256837 3497722501596903032673157)
                  ·
                    refine ⟨655822969049419318626217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3497722501596903032673157 655822969049419318626217)
                    ·
                      rfl

theorem cell23_3831632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 4, 4, 4].length) (baseStart_3831632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3831632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3831632 prefixEnd_3831632 := by exact prefixLift 3831632
  have htrace : WordTrace (prefixWord ++ tailWord_3831632) baseStart_3831632 baseEnd_3831632 := by
    simpa [prefixWord, tailWord_3831632, baseEnd_3831632] using wordTrace_append hprefix tailTrace_3831632
  have hstable : (prefixWord ++ tailWord_3831632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3831632).length < 2 ^ (prefixWord ++ tailWord_3831632).sum := by decide
  have hdescent : baseEnd_3831632 < baseStart_3831632 := by decide
  rcases family_descends (prefixWord ++ tailWord_3831632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3831633 : List Nat := [1, 2, 2, 1, 5, 2, 2, 3, 1, 1, 3]
def baseStart_3831633 : Nat := 118140960795 + 3831633 * 2 ^ 59
def prefixEnd_3831633 : Nat := 4983230072969 + 3 ^ 40 * 3831633 * 2
def baseEnd_3831633 : Nat := 1967469420628912451966147

theorem tailTrace_3831633 : CollatzResearch.WordTrace tailWord_3831633 prefixEnd_3831633 1967469420628912451966147 := by
  unfold tailWord_3831633
  simp only [CollatzResearch.WordTrace]
  refine ⟨139751136527655506662795553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93167424351770337775197035 139751136527655506662795553)
  ·
    refine ⟨104813352395741629997096665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139751136527655506662795553 104813352395741629997096665)
    ·
      refine ⟨78610014296806222497822499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104813352395741629997096665 78610014296806222497822499)
      ·
        refine ⟨117915021445209333746733749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78610014296806222497822499 117915021445209333746733749)
        ·
          refine ⟨11054533260488375038756289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 117915021445209333746733749 11054533260488375038756289)
          ·
            refine ⟨8290899945366281279067217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11054533260488375038756289 8290899945366281279067217)
            ·
              refine ⟨6218174959024710959300413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8290899945366281279067217 6218174959024710959300413)
              ·
                refine ⟨2331815609634266609737655, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6218174959024710959300413 2331815609634266609737655)
                ·
                  refine ⟨3497723414451399914606483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2331815609634266609737655 3497723414451399914606483)
                  ·
                    refine ⟨5246585121677099871909725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3497723414451399914606483 5246585121677099871909725)
                    ·
                      refine ⟨1967469420628912451966147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5246585121677099871909725 1967469420628912451966147)
                      ·
                        rfl

theorem cell23_3831633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 2, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 2, 2, 3, 1, 1, 3].length) (baseStart_3831633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3831633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3831633 prefixEnd_3831633 := by exact prefixLift 3831633
  have htrace : WordTrace (prefixWord ++ tailWord_3831633) baseStart_3831633 baseEnd_3831633 := by
    simpa [prefixWord, tailWord_3831633, baseEnd_3831633] using wordTrace_append hprefix tailTrace_3831633
  have hstable : (prefixWord ++ tailWord_3831633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3831633).length < 2 ^ (prefixWord ++ tailWord_3831633).sum := by decide
  have hdescent : baseEnd_3831633 < baseStart_3831633 := by decide
  rcases family_descends (prefixWord ++ tailWord_3831633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3831635 : List Nat := [1, 1, 1, 2, 1, 1, 3, 1, 5, 1, 6]
def baseStart_3831635 : Nat := 118140960795 + 3831635 * 2 ^ 59
def prefixEnd_3831635 : Nat := 4983230072969 + 3 ^ 40 * 3831635 * 2
def baseEnd_3831635 : Nat := 1967470447590221444141137

theorem tailTrace_3831635 : CollatzResearch.WordTrace tailWord_3831635 prefixEnd_3831635 1967470447590221444141137 := by
  unfold tailWord_3831635
  simp only [CollatzResearch.WordTrace]
  refine ⟨139751209473648261004368359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93167472982432174002912239 139751209473648261004368359)
  ·
    refine ⟨209626814210472391506552539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139751209473648261004368359 209626814210472391506552539)
    ·
      refine ⟨314440221315708587259828809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209626814210472391506552539 314440221315708587259828809)
      ·
        refine ⟨235830165986781440444871607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 314440221315708587259828809 235830165986781440444871607)
        ·
          refine ⟨353745248980172160667307411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 235830165986781440444871607 353745248980172160667307411)
          ·
            refine ⟨530617873470258241000961117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 353745248980172160667307411 530617873470258241000961117)
            ·
              refine ⟨198981702551346840375360419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 530617873470258241000961117 198981702551346840375360419)
              ·
                refine ⟨298472553827020260563040629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 198981702551346840375360419 298472553827020260563040629)
                ·
                  refine ⟨27981801921283149427785059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 298472553827020260563040629 27981801921283149427785059)
                  ·
                    refine ⟨41972702881924724141677589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27981801921283149427785059 41972702881924724141677589)
                    ·
                      refine ⟨1967470447590221444141137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 41972702881924724141677589 1967470447590221444141137)
                      ·
                        rfl

theorem cell23_3831635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 1, 5, 1, 6].length) (baseStart_3831635 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3831635 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3831635 prefixEnd_3831635 := by exact prefixLift 3831635
  have htrace : WordTrace (prefixWord ++ tailWord_3831635) baseStart_3831635 baseEnd_3831635 := by
    simpa [prefixWord, tailWord_3831635, baseEnd_3831635] using wordTrace_append hprefix tailTrace_3831635
  have hstable : (prefixWord ++ tailWord_3831635).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3831635).length < 2 ^ (prefixWord ++ tailWord_3831635).sum := by decide
  have hdescent : baseEnd_3831635 < baseStart_3831635 := by decide
  rcases family_descends (prefixWord ++ tailWord_3831635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3831636 : List Nat := [2, 4, 1, 1, 3, 1, 4, 1, 1, 5]
def baseStart_3831636 : Nat := 118140960795 + 3831636 * 2 ^ 59
def prefixEnd_3831636 : Nat := 4983230072969 + 3 ^ 40 * 3831636 * 2
def baseEnd_3831636 : Nat := 655823653690291980076211

theorem tailTrace_3831636 : CollatzResearch.WordTrace tailWord_3831636 prefixEnd_3831636 655823653690291980076211 := by
  unfold tailWord_3831636
  simp only [CollatzResearch.WordTrace]
  refine ⟨69875622973322319087577381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93167497297763092116769841 69875622973322319087577381)
  ·
    refine ⟨13101679307497934828920759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 69875622973322319087577381 13101679307497934828920759)
    ·
      refine ⟨19652518961246902243381139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13101679307497934828920759 19652518961246902243381139)
      ·
        refine ⟨29478778441870353365071709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19652518961246902243381139 29478778441870353365071709)
        ·
          refine ⟨11054541915701382511901891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29478778441870353365071709 11054541915701382511901891)
          ·
            refine ⟨16581812873552073767852837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11054541915701382511901891 16581812873552073767852837)
            ·
              refine ⟨3109089913791013831472407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16581812873552073767852837 3109089913791013831472407)
              ·
                refine ⟨4663634870686520747208611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3109089913791013831472407 4663634870686520747208611)
                ·
                  refine ⟨6995452306029781120812917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4663634870686520747208611 6995452306029781120812917)
                  ·
                    refine ⟨655823653690291980076211, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6995452306029781120812917 655823653690291980076211)
                    ·
                      rfl

theorem cell23_3831636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 4, 1, 1, 5].length) (baseStart_3831636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3831636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3831636 prefixEnd_3831636 := by exact prefixLift 3831636
  have htrace : WordTrace (prefixWord ++ tailWord_3831636) baseStart_3831636 baseEnd_3831636 := by
    simpa [prefixWord, tailWord_3831636, baseEnd_3831636] using wordTrace_append hprefix tailTrace_3831636
  have hstable : (prefixWord ++ tailWord_3831636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3831636).length < 2 ^ (prefixWord ++ tailWord_3831636).sum := by decide
  have hdescent : baseEnd_3831636 < baseStart_3831636 := by decide
  rcases family_descends (prefixWord ++ tailWord_3831636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3831642 : List Nat := [3, 1, 1, 2, 1, 3, 2, 3, 1, 1, 5]
def baseStart_3831642 : Nat := 118140960795 + 3831642 * 2 ^ 59
def prefixEnd_3831642 : Nat := 4983230072969 + 3 ^ 40 * 3831642 * 2
def baseEnd_3831642 : Nat := 1967474041954802916753605

theorem tailTrace_3831642 : CollatzResearch.WordTrace tailWord_3831642 prefixEnd_3831642 1967474041954802916753605 := by
  unfold tailWord_3831642
  simp only [CollatzResearch.WordTrace]
  refine ⟨34937866196155725299968295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93167643189748600799915453 34937866196155725299968295)
  ·
    refine ⟨52406799294233587949952443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34937866196155725299968295 52406799294233587949952443)
    ·
      refine ⟨78610198941350381924928665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52406799294233587949952443 78610198941350381924928665)
      ·
        refine ⟨58957649206012786443696499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78610198941350381924928665 58957649206012786443696499)
        ·
          refine ⟨88436473809019179665544749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58957649206012786443696499 88436473809019179665544749)
          ·
            refine ⟨33163677678382192374579281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 88436473809019179665544749 33163677678382192374579281)
            ·
              refine ⟨24872758258786644280934461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33163677678382192374579281 24872758258786644280934461)
              ·
                refine ⟨9327284347044991605350423, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24872758258786644280934461 9327284347044991605350423)
                ·
                  refine ⟨13990926520567487408025635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9327284347044991605350423 13990926520567487408025635)
                  ·
                    refine ⟨20986389780851231112038453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13990926520567487408025635 20986389780851231112038453)
                    ·
                      refine ⟨1967474041954802916753605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20986389780851231112038453 1967474041954802916753605)
                      ·
                        rfl

theorem cell23_3831642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 2, 3, 1, 1, 5].length) (baseStart_3831642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3831642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3831642 prefixEnd_3831642 := by exact prefixLift 3831642
  have htrace : WordTrace (prefixWord ++ tailWord_3831642) baseStart_3831642 baseEnd_3831642 := by
    simpa [prefixWord, tailWord_3831642, baseEnd_3831642] using wordTrace_append hprefix tailTrace_3831642
  have hstable : (prefixWord ++ tailWord_3831642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3831642).length < 2 ^ (prefixWord ++ tailWord_3831642).sum := by decide
  have hdescent : baseEnd_3831642 < baseStart_3831642 := by decide
  rcases family_descends (prefixWord ++ tailWord_3831642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3831689 : List Nat := [1, 2, 1, 1, 5, 1, 1, 1, 6, 1, 3]
def baseStart_3831689 : Nat := 118140960795 + 3831689 * 2 ^ 59
def prefixEnd_3831689 : Nat := 4983230072969 + 3 ^ 40 * 3831689 * 2
def baseEnd_3831689 : Nat := 1967498175545564232865889

theorem tailTrace_3831689 : CollatzResearch.WordTrace tailWord_3831689 prefixEnd_3831689 1967498175545564232865889 := by
  unfold tailWord_3831689
  simp only [CollatzResearch.WordTrace]
  refine ⟨139753179015452628226834121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93168786010301752151222747 139753179015452628226834121)
  ·
    refine ⟨104814884261589471170125591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139753179015452628226834121 104814884261589471170125591)
    ·
      refine ⟨157222326392384206755188387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104814884261589471170125591 157222326392384206755188387)
      ·
        refine ⟨235833489588576310132782581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157222326392384206755188387 235833489588576310132782581)
        ·
          refine ⟨22109389648929029074948367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 235833489588576310132782581 22109389648929029074948367)
          ·
            refine ⟨33164084473393543612422551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22109389648929029074948367 33164084473393543612422551)
            ·
              refine ⟨49746126710090315418633827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33164084473393543612422551 49746126710090315418633827)
              ·
                refine ⟨74619190065135473127950741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49746126710090315418633827 74619190065135473127950741)
                ·
                  refine ⟨3497774534303225302872691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 74619190065135473127950741 3497774534303225302872691)
                  ·
                    refine ⟨5246661801454837954309037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3497774534303225302872691 5246661801454837954309037)
                    ·
                      refine ⟨1967498175545564232865889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5246661801454837954309037 1967498175545564232865889)
                      ·
                        rfl

theorem cell23_3831689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 1, 1, 6, 1, 3].length) (baseStart_3831689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3831689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3831689 prefixEnd_3831689 := by exact prefixLift 3831689
  have htrace : WordTrace (prefixWord ++ tailWord_3831689) baseStart_3831689 baseEnd_3831689 := by
    simpa [prefixWord, tailWord_3831689, baseEnd_3831689] using wordTrace_append hprefix tailTrace_3831689
  have hstable : (prefixWord ++ tailWord_3831689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3831689).length < 2 ^ (prefixWord ++ tailWord_3831689).sum := by decide
  have hdescent : baseEnd_3831689 < baseStart_3831689 := by decide
  rcases family_descends (prefixWord ++ tailWord_3831689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3831706 : List Nat := [3, 1, 1, 4, 2, 1, 2, 1, 4, 1, 3]
def baseStart_3831706 : Nat := 118140960795 + 3831706 * 2 ^ 59
def prefixEnd_3831706 : Nat := 4983230072969 + 3 ^ 40 * 3831706 * 2
def baseEnd_3831706 : Nat := 1967506904716690666353311

theorem tailTrace_3831706 : CollatzResearch.WordTrace tailWord_3831706 prefixEnd_3831706 1967506904716690666353311 := by
  unfold tailWord_3831706
  simp only [CollatzResearch.WordTrace]
  refine ⟨34938449764097760032550743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93169199370927360086801981 34938449764097760032550743)
  ·
    refine ⟨52407674646146640048826115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34938449764097760032550743 52407674646146640048826115)
    ·
      refine ⟨78611511969219960073239173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52407674646146640048826115 78611511969219960073239173)
      ·
        refine ⟨14739658494228742513732345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 78611511969219960073239173 14739658494228742513732345)
        ·
          refine ⟨11054743870671556885299259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14739658494228742513732345 11054743870671556885299259)
          ·
            refine ⟨16582115806007335327948889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11054743870671556885299259 16582115806007335327948889)
            ·
              refine ⟨12436586854505501495961667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16582115806007335327948889 12436586854505501495961667)
              ·
                refine ⟨18654880281758252243942501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12436586854505501495961667 18654880281758252243942501)
                ·
                  refine ⟨3497790052829672295739219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18654880281758252243942501 3497790052829672295739219)
                  ·
                    refine ⟨5246685079244508443608829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3497790052829672295739219 5246685079244508443608829)
                    ·
                      refine ⟨1967506904716690666353311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5246685079244508443608829 1967506904716690666353311)
                      ·
                        rfl

theorem cell23_3831706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 2, 1, 4, 1, 3].length) (baseStart_3831706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3831706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3831706 prefixEnd_3831706 := by exact prefixLift 3831706
  have htrace : WordTrace (prefixWord ++ tailWord_3831706) baseStart_3831706 baseEnd_3831706 := by
    simpa [prefixWord, tailWord_3831706, baseEnd_3831706] using wordTrace_append hprefix tailTrace_3831706
  have hstable : (prefixWord ++ tailWord_3831706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3831706).length < 2 ^ (prefixWord ++ tailWord_3831706).sum := by decide
  have hdescent : baseEnd_3831706 < baseStart_3831706 := by decide
  rcases family_descends (prefixWord ++ tailWord_3831706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3831712 : List Nat := [2, 1, 1, 4, 1, 1, 1, 3, 2, 3, 4]
def baseStart_3831712 : Nat := 118140960795 + 3831712 * 2 ^ 59
def prefixEnd_3831712 : Nat := 4983230072969 + 3 ^ 40 * 3831712 * 2
def baseEnd_3831712 : Nat := 1967509985600617642878283

theorem tailTrace_3831712 : CollatzResearch.WordTrace tailWord_3831712 prefixEnd_3831712 1967509985600617642878283 := by
  unfold tailWord_3831712
  simp only [CollatzResearch.WordTrace]
  refine ⟨69877008947184651577460695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93169345262912868769947593 69877008947184651577460695)
  ·
    refine ⟨104815513420776977366191043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69877008947184651577460695 104815513420776977366191043)
    ·
      refine ⟨157223270131165466049286565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104815513420776977366191043 157223270131165466049286565)
      ·
        refine ⟨29479363149593524884241231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 157223270131165466049286565 29479363149593524884241231)
        ·
          refine ⟨44219044724390287326361847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29479363149593524884241231 44219044724390287326361847)
          ·
            refine ⟨66328567086585430989542771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44219044724390287326361847 66328567086585430989542771)
            ·
              refine ⟨99492850629878146484314157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66328567086585430989542771 99492850629878146484314157)
              ·
                refine ⟨37309818986204304931617809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 99492850629878146484314157 37309818986204304931617809)
                ·
                  refine ⟨27982364239653228698713357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37309818986204304931617809 27982364239653228698713357)
                  ·
                    refine ⟨10493386589869960762017509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27982364239653228698713357 10493386589869960762017509)
                    ·
                      refine ⟨1967509985600617642878283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10493386589869960762017509 1967509985600617642878283)
                      ·
                        rfl

theorem cell23_3831712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 3, 2, 3, 4].length) (baseStart_3831712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3831712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3831712 prefixEnd_3831712 := by exact prefixLift 3831712
  have htrace : WordTrace (prefixWord ++ tailWord_3831712) baseStart_3831712 baseEnd_3831712 := by
    simpa [prefixWord, tailWord_3831712, baseEnd_3831712] using wordTrace_append hprefix tailTrace_3831712
  have hstable : (prefixWord ++ tailWord_3831712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3831712).length < 2 ^ (prefixWord ++ tailWord_3831712).sum := by decide
  have hdescent : baseEnd_3831712 < baseStart_3831712 := by decide
  rcases family_descends (prefixWord ++ tailWord_3831712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3831733 : List Nat := [1, 3, 3, 2, 1, 2, 3, 2, 1, 3, 2]
def baseStart_3831733 : Nat := 118140960795 + 3831733 * 2 ^ 59
def prefixEnd_3831733 : Nat := 4983230072969 + 3 ^ 40 * 3831733 * 2
def baseEnd_3831733 : Nat := 1967520768694362060715687

theorem tailTrace_3831733 : CollatzResearch.WordTrace tailWord_3831733 prefixEnd_3831733 1967520768694362060715687 := by
  unfold tailWord_3831733
  simp only [CollatzResearch.WordTrace]
  refine ⟨139754783827293223741435853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93169855884862149160957235 139754783827293223741435853)
  ·
    refine ⟨52408043935234958903038445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 139754783827293223741435853 52408043935234958903038445)
    ·
      refine ⟨19653016475713109588639417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52408043935234958903038445 19653016475713109588639417)
      ·
        refine ⟨14739762356784832191479563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19653016475713109588639417 14739762356784832191479563)
        ·
          refine ⟨22109643535177248287219345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14739762356784832191479563 22109643535177248287219345)
          ·
            refine ⟨16582232651382936215414509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22109643535177248287219345 16582232651382936215414509)
            ·
              refine ⟨6218337244268601080780441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16582232651382936215414509 6218337244268601080780441)
              ·
                refine ⟨4663752933201450810585331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6218337244268601080780441 4663752933201450810585331)
                ·
                  refine ⟨6995629399802176215877997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4663752933201450810585331 6995629399802176215877997)
                  ·
                    refine ⟨2623361024925816080954249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6995629399802176215877997 2623361024925816080954249)
                    ·
                      refine ⟨1967520768694362060715687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2623361024925816080954249 1967520768694362060715687)
                      ·
                        rfl

theorem cell23_3831733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 3, 2, 1, 3, 2].length) (baseStart_3831733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3831733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3831733 prefixEnd_3831733 := by exact prefixLift 3831733
  have htrace : WordTrace (prefixWord ++ tailWord_3831733) baseStart_3831733 baseEnd_3831733 := by
    simpa [prefixWord, tailWord_3831733, baseEnd_3831733] using wordTrace_append hprefix tailTrace_3831733
  have hstable : (prefixWord ++ tailWord_3831733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3831733).length < 2 ^ (prefixWord ++ tailWord_3831733).sum := by decide
  have hdescent : baseEnd_3831733 < baseStart_3831733 := by decide
  rcases family_descends (prefixWord ++ tailWord_3831733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3831779 : List Nat := [1, 1, 1, 6, 1, 2, 1, 1, 1, 5, 3]
def baseStart_3831779 : Nat := 118140960795 + 3831779 * 2 ^ 59
def prefixEnd_3831779 : Nat := 4983230072969 + 3 ^ 40 * 3831779 * 2
def baseEnd_3831779 : Nat := 1967544388804468880740475

theorem tailTrace_3831779 : CollatzResearch.WordTrace tailWord_3831779 prefixEnd_3831779 1967544388804468880740475 := by
  unfold tailWord_3831779
  simp only [CollatzResearch.WordTrace]
  refine ⟨139756461585126573597610391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93170974390084382398406927 139756461585126573597610391)
  ·
    refine ⟨209634692377689860396415587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139756461585126573597610391 209634692377689860396415587)
    ·
      refine ⟨314452038566534790594623381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209634692377689860396415587 314452038566534790594623381)
      ·
        refine ⟨14739939307806318309122971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 314452038566534790594623381 14739939307806318309122971)
        ·
          refine ⟨22109908961709477463684457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14739939307806318309122971 22109908961709477463684457)
          ·
            refine ⟨16582431721282108097763343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22109908961709477463684457 16582431721282108097763343)
            ·
              refine ⟨24873647581923162146645015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16582431721282108097763343 24873647581923162146645015)
              ·
                refine ⟨37310471372884743219967523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24873647581923162146645015 37310471372884743219967523)
                ·
                  refine ⟨55965707059327114829951285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37310471372884743219967523 55965707059327114829951285)
                  ·
                    refine ⟨5246785036811917015307933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 55965707059327114829951285 5246785036811917015307933)
                    ·
                      refine ⟨1967544388804468880740475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5246785036811917015307933 1967544388804468880740475)
                      ·
                        rfl

theorem cell23_3831779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 1, 1, 1, 5, 3].length) (baseStart_3831779 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3831779 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3831779 prefixEnd_3831779 := by exact prefixLift 3831779
  have htrace : WordTrace (prefixWord ++ tailWord_3831779) baseStart_3831779 baseEnd_3831779 := by
    simpa [prefixWord, tailWord_3831779, baseEnd_3831779] using wordTrace_append hprefix tailTrace_3831779
  have hstable : (prefixWord ++ tailWord_3831779).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3831779).length < 2 ^ (prefixWord ++ tailWord_3831779).sum := by decide
  have hdescent : baseEnd_3831779 < baseStart_3831779 := by decide
  rcases family_descends (prefixWord ++ tailWord_3831779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3831792 : List Nat := [2, 1, 1, 1, 3, 2, 2, 2, 1, 1, 7]
def baseStart_3831792 : Nat := 118140960795 + 3831792 * 2 ^ 59
def prefixEnd_3831792 : Nat := 4983230072969 + 3 ^ 40 * 3831792 * 2
def baseEnd_3831792 : Nat := 1967551064052977329877915

theorem tailTrace_3831792 : CollatzResearch.WordTrace tailWord_3831792 prefixEnd_3831792 1967551064052977329877915 := by
  unfold tailWord_3831792
  simp only [CollatzResearch.WordTrace]
  refine ⟨69878467867039738408916815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93171290489386317878555753 69878467867039738408916815)
  ·
    refine ⟨104817701800559607613375223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69878467867039738408916815 104817701800559607613375223)
    ·
      refine ⟨157226552700839411420062835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104817701800559607613375223 157226552700839411420062835)
      ·
        refine ⟨235839829051259117130094253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157226552700839411420062835 235839829051259117130094253)
        ·
          refine ⟨88439935894222168923785345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 235839829051259117130094253 88439935894222168923785345)
          ·
            refine ⟨66329951920666626692839009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 88439935894222168923785345 66329951920666626692839009)
            ·
              refine ⟨49747463940499970019629257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66329951920666626692839009 49747463940499970019629257)
              ·
                refine ⟨37310597955374977514721943, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49747463940499970019629257 37310597955374977514721943)
                ·
                  refine ⟨55965896933062466272082915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37310597955374977514721943 55965896933062466272082915)
                  ·
                    refine ⟨83948845399593699408124373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 55965896933062466272082915 83948845399593699408124373)
                    ·
                      refine ⟨1967551064052977329877915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 83948845399593699408124373 1967551064052977329877915)
                      ·
                        rfl

theorem cell23_3831792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 2, 2, 1, 1, 7].length) (baseStart_3831792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3831792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3831792 prefixEnd_3831792 := by exact prefixLift 3831792
  have htrace : WordTrace (prefixWord ++ tailWord_3831792) baseStart_3831792 baseEnd_3831792 := by
    simpa [prefixWord, tailWord_3831792, baseEnd_3831792] using wordTrace_append hprefix tailTrace_3831792
  have hstable : (prefixWord ++ tailWord_3831792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3831792).length < 2 ^ (prefixWord ++ tailWord_3831792).sum := by decide
  have hdescent : baseEnd_3831792 < baseStart_3831792 := by decide
  rcases family_descends (prefixWord ++ tailWord_3831792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3831819 : List Nat := [1, 1, 1, 1, 6, 1, 2, 1, 4, 1, 4]
def baseStart_3831819 : Nat := 118140960795 + 3831819 * 2 ^ 59
def prefixEnd_3831819 : Nat := 4983230072969 + 3 ^ 40 * 3831819 * 2
def baseEnd_3831819 : Nat := 1967564928030648724240291

theorem tailTrace_3831819 : CollatzResearch.WordTrace tailWord_3831819 prefixEnd_3831819 1967564928030648724240291 := by
  unfold tailWord_3831819
  simp only [CollatzResearch.WordTrace]
  refine ⟨139757920504981660429066511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93171947003321106952711007 139757920504981660429066511)
  ·
    refine ⟨209636880757472490643599767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139757920504981660429066511 209636880757472490643599767)
    ·
      refine ⟨314455321136208735965399651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209636880757472490643599767 314455321136208735965399651)
      ·
        refine ⟨471682981704313103948099477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 314455321136208735965399651 471682981704313103948099477)
        ·
          refine ⟨22110139767389676747567163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 471682981704313103948099477 22110139767389676747567163)
          ·
            refine ⟨33165209651084515121350745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22110139767389676747567163 33165209651084515121350745)
            ·
              refine ⟨24873907238313386341013059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33165209651084515121350745 24873907238313386341013059)
              ·
                refine ⟨37310860857470079511519589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24873907238313386341013059 37310860857470079511519589)
                ·
                  refine ⟨6995786410775639908409923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37310860857470079511519589 6995786410775639908409923)
                  ·
                    refine ⟨10493679616163459862614885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6995786410775639908409923 10493679616163459862614885)
                    ·
                      refine ⟨1967564928030648724240291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10493679616163459862614885 1967564928030648724240291)
                      ·
                        rfl

theorem cell23_3831819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 2, 1, 4, 1, 4].length) (baseStart_3831819 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3831819 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3831819 prefixEnd_3831819 := by exact prefixLift 3831819
  have htrace : WordTrace (prefixWord ++ tailWord_3831819) baseStart_3831819 baseEnd_3831819 := by
    simpa [prefixWord, tailWord_3831819, baseEnd_3831819] using wordTrace_append hprefix tailTrace_3831819
  have hstable : (prefixWord ++ tailWord_3831819).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3831819).length < 2 ^ (prefixWord ++ tailWord_3831819).sum := by decide
  have hdescent : baseEnd_3831819 < baseStart_3831819 := by decide
  rcases family_descends (prefixWord ++ tailWord_3831819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3831839 : List Nat := [1, 1, 2, 4, 1, 2, 1, 1, 3, 4, 3]
def baseStart_3831839 : Nat := 118140960795 + 3831839 * 2 ^ 59
def prefixEnd_3831839 : Nat := 4983230072969 + 3 ^ 40 * 3831839 * 2
def baseEnd_3831839 : Nat := 1967575197643738645990199

theorem tailTrace_3831839 : CollatzResearch.WordTrace tailWord_3831839 prefixEnd_3831839 1967575197643738645990199 := by
  unfold tailWord_3831839
  simp only [CollatzResearch.WordTrace]
  refine ⟨139758649964909203844794571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93172433309939469229863047 139758649964909203844794571)
  ·
    refine ⟨209637974947363805767191857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139758649964909203844794571 209637974947363805767191857)
    ·
      refine ⟨157228481210522854325393893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 209637974947363805767191857 157228481210522854325393893)
      ·
        refine ⟨29480340226973035186011355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 157228481210522854325393893 29480340226973035186011355)
        ·
          refine ⟨44220510340459552779017033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29480340226973035186011355 44220510340459552779017033)
          ·
            refine ⟨33165382755344664584262775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44220510340459552779017033 33165382755344664584262775)
            ·
              refine ⟨49748074133016996876394163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33165382755344664584262775 49748074133016996876394163)
              ·
                refine ⟨74622111199525495314591245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49748074133016996876394163 74622111199525495314591245)
                ·
                  refine ⟨27983291699822060742971717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 74622111199525495314591245 27983291699822060742971717)
                  ·
                    refine ⟨5246867193716636389307197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27983291699822060742971717 5246867193716636389307197)
                    ·
                      refine ⟨1967575197643738645990199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5246867193716636389307197 1967575197643738645990199)
                      ·
                        rfl

theorem cell23_3831839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 1, 1, 3, 4, 3].length) (baseStart_3831839 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3831839 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3831839 prefixEnd_3831839 := by exact prefixLift 3831839
  have htrace : WordTrace (prefixWord ++ tailWord_3831839) baseStart_3831839 baseEnd_3831839 := by
    simpa [prefixWord, tailWord_3831839, baseEnd_3831839] using wordTrace_append hprefix tailTrace_3831839
  have hstable : (prefixWord ++ tailWord_3831839).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3831839).length < 2 ^ (prefixWord ++ tailWord_3831839).sum := by decide
  have hdescent : baseEnd_3831839 < baseStart_3831839 := by decide
  rcases family_descends (prefixWord ++ tailWord_3831839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3831863 : List Nat := [1, 1, 3, 1, 2, 2, 5, 3, 1, 4]
def baseStart_3831863 : Nat := 118140960795 + 3831863 * 2 ^ 59
def prefixEnd_3831863 : Nat := 4983230072969 + 3 ^ 40 * 3831863 * 2
def baseEnd_3831863 : Nat := 655862507059815517363363

theorem tailTrace_3831863 : CollatzResearch.WordTrace tailWord_3831863 prefixEnd_3831863 655862507059815517363363 := by
  unfold tailWord_3831863
  simp only [CollatzResearch.WordTrace]
  refine ⟨139759525316822255943668243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93173016877881503962445495 139759525316822255943668243)
  ·
    refine ⟨209639287975233383915502365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139759525316822255943668243 209639287975233383915502365)
    ·
      refine ⟨78614732990712518968313387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 209639287975233383915502365 78614732990712518968313387)
      ·
        refine ⟨117922099486068778452470081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78614732990712518968313387 117922099486068778452470081)
        ·
          refine ⟨88441574614551583839352561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 117922099486068778452470081 88441574614551583839352561)
          ·
            refine ⟨66331180960913687879514421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 88441574614551583839352561 66331180960913687879514421)
            ·
              refine ⟨6218548215085658238704477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 66331180960913687879514421 6218548215085658238704477)
              ·
                refine ⟨2331955580657121839514179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6218548215085658238704477 2331955580657121839514179)
                ·
                  refine ⟨3497933370985682759271269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2331955580657121839514179 3497933370985682759271269)
                  ·
                    refine ⟨655862507059815517363363, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3497933370985682759271269 655862507059815517363363)
                    ·
                      rfl

theorem cell23_3831863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 5, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 5, 3, 1, 4].length) (baseStart_3831863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3831863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3831863 prefixEnd_3831863 := by exact prefixLift 3831863
  have htrace : WordTrace (prefixWord ++ tailWord_3831863) baseStart_3831863 baseEnd_3831863 := by
    simpa [prefixWord, tailWord_3831863, baseEnd_3831863] using wordTrace_append hprefix tailTrace_3831863
  have hstable : (prefixWord ++ tailWord_3831863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3831863).length < 2 ^ (prefixWord ++ tailWord_3831863).sum := by decide
  have hdescent : baseEnd_3831863 < baseStart_3831863 := by decide
  rcases family_descends (prefixWord ++ tailWord_3831863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3831873 : List Nat := [1, 2, 5, 1, 2, 2, 1, 2, 2, 2, 3]
def baseStart_3831873 : Nat := 118140960795 + 3831873 * 2 ^ 59
def prefixEnd_3831873 : Nat := 4983230072969 + 3 ^ 40 * 3831873 * 2
def baseEnd_3831873 : Nat := 1967592655985991512965043

theorem tailTrace_3831873 : CollatzResearch.WordTrace tailWord_3831873 prefixEnd_3831873 1967592655985991512965043 := by
  unfold tailWord_3831873
  simp only [CollatzResearch.WordTrace]
  refine ⟨139759890046786027651532273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93173260031190685101021515 139759890046786027651532273)
  ·
    refine ⟨104819917535089520738649205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139759890046786027651532273 104819917535089520738649205)
    ·
      refine ⟨9826867268914642569248363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 104819917535089520738649205 9826867268914642569248363)
      ·
        refine ⟨14740300903371963853872545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9826867268914642569248363 14740300903371963853872545)
        ·
          refine ⟨11055225677528972890404409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14740300903371963853872545 11055225677528972890404409)
          ·
            refine ⟨8291419258146729667803307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11055225677528972890404409 8291419258146729667803307)
            ·
              refine ⟨12437128887220094501704961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8291419258146729667803307 12437128887220094501704961)
              ·
                refine ⟨9327846665415070876278721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12437128887220094501704961 9327846665415070876278721)
                ·
                  refine ⟨6995884999061303157209041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9327846665415070876278721 6995884999061303157209041)
                  ·
                    refine ⟨5246913749295977367906781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6995884999061303157209041 5246913749295977367906781)
                    ·
                      refine ⟨1967592655985991512965043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5246913749295977367906781 1967592655985991512965043)
                      ·
                        rfl

theorem cell23_3831873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 2, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 2, 1, 2, 2, 2, 3].length) (baseStart_3831873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3831873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3831873 prefixEnd_3831873 := by exact prefixLift 3831873
  have htrace : WordTrace (prefixWord ++ tailWord_3831873) baseStart_3831873 baseEnd_3831873 := by
    simpa [prefixWord, tailWord_3831873, baseEnd_3831873] using wordTrace_append hprefix tailTrace_3831873
  have hstable : (prefixWord ++ tailWord_3831873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3831873).length < 2 ^ (prefixWord ++ tailWord_3831873).sum := by decide
  have hdescent : baseEnd_3831873 < baseStart_3831873 := by decide
  rcases family_descends (prefixWord ++ tailWord_3831873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3831889 : List Nat := [1, 2, 2, 1, 3, 1, 1, 4, 3, 5]
def baseStart_3831889 : Nat := 118140960795 + 3831889 * 2 ^ 59
def prefixEnd_3831889 : Nat := 4983230072969 + 3 ^ 40 * 3831889 * 2
def baseEnd_3831889 : Nat := 655866957225487816788323

theorem tailTrace_3831889 : CollatzResearch.WordTrace tailWord_3831889 prefixEnd_3831889 655866957225487816788323 := by
  unfold tailWord_3831889
  simp only [CollatzResearch.WordTrace]
  refine ⟨139760473614728062384114721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93173649076485374922743147 139760473614728062384114721)
  ·
    refine ⟨104820355211046046788086041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139760473614728062384114721 104820355211046046788086041)
    ·
      refine ⟨78615266408284535091064531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104820355211046046788086041 78615266408284535091064531)
      ·
        refine ⟨117922899612426802636596797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78615266408284535091064531 117922899612426802636596797)
        ·
          refine ⟨44221087354660050988723799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 117922899612426802636596797 44221087354660050988723799)
          ·
            refine ⟨66331631031990076483085699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44221087354660050988723799 66331631031990076483085699)
            ·
              refine ⟨99497446547985114724628549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66331631031990076483085699 99497446547985114724628549)
              ·
                refine ⟨18655771227747209010867853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 99497446547985114724628549 18655771227747209010867853)
                ·
                  refine ⟨6995914210405203379075445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18655771227747209010867853 6995914210405203379075445)
                  ·
                    refine ⟨655866957225487816788323, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6995914210405203379075445 655866957225487816788323)
                    ·
                      rfl

theorem cell23_3831889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 4, 3, 5].length) (baseStart_3831889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3831889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3831889 prefixEnd_3831889 := by exact prefixLift 3831889
  have htrace : WordTrace (prefixWord ++ tailWord_3831889) baseStart_3831889 baseEnd_3831889 := by
    simpa [prefixWord, tailWord_3831889, baseEnd_3831889] using wordTrace_append hprefix tailTrace_3831889
  have hstable : (prefixWord ++ tailWord_3831889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3831889).length < 2 ^ (prefixWord ++ tailWord_3831889).sum := by decide
  have hdescent : baseEnd_3831889 < baseStart_3831889 := by decide
  rcases family_descends (prefixWord ++ tailWord_3831889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3831893 : List Nat := [1, 3, 2, 2, 1, 5, 2, 1, 6]
def baseStart_3831893 : Nat := 118140960795 + 3831893 * 2 ^ 59
def prefixEnd_3831893 : Nat := 4983230072969 + 3 ^ 40 * 3831893 * 2
def baseEnd_3831893 : Nat := 218622547288786826079439

theorem tailTrace_3831893 : CollatzResearch.WordTrace tailWord_3831893 prefixEnd_3831893 218622547288786826079439 := by
  unfold tailWord_3831893
  simp only [CollatzResearch.WordTrace]
  refine ⟨139760619506713571067260333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93173746337809047378173555 139760619506713571067260333)
  ·
    refine ⟨52410232315017589150222625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 139760619506713571067260333 52410232315017589150222625)
    ·
      refine ⟨39307674236263191862666969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52410232315017589150222625 39307674236263191862666969)
      ·
        refine ⟨29480755677197393897000227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39307674236263191862666969 29480755677197393897000227)
        ·
          refine ⟨44221133515796090845500341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29480755677197393897000227 44221133515796090845500341)
          ·
            refine ⟨4145731267105883516765657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 44221133515796090845500341 4145731267105883516765657)
            ·
              refine ⟨3109298450329412637574243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4145731267105883516765657 3109298450329412637574243)
              ·
                refine ⟨4663947675494118956361365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3109298450329412637574243 4663947675494118956361365)
                ·
                  refine ⟨218622547288786826079439, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4663947675494118956361365 218622547288786826079439)
                  ·
                    rfl

theorem cell23_3831893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 5, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 5, 2, 1, 6].length) (baseStart_3831893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3831893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3831893 prefixEnd_3831893 := by exact prefixLift 3831893
  have htrace : WordTrace (prefixWord ++ tailWord_3831893) baseStart_3831893 baseEnd_3831893 := by
    simpa [prefixWord, tailWord_3831893, baseEnd_3831893] using wordTrace_append hprefix tailTrace_3831893
  have hstable : (prefixWord ++ tailWord_3831893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3831893).length < 2 ^ (prefixWord ++ tailWord_3831893).sum := by decide
  have hdescent : baseEnd_3831893 < baseStart_3831893 := by decide
  rcases family_descends (prefixWord ++ tailWord_3831893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3831913 : List Nat := [1, 2, 1, 1, 1, 5, 4, 1, 2, 3, 2]
def baseStart_3831913 : Nat := 118140960795 + 3831913 * 2 ^ 59
def prefixEnd_3831913 : Nat := 4983230072969 + 3 ^ 40 * 3831913 * 2
def baseEnd_3831913 : Nat := 1967613195212171356464859

theorem tailTrace_3831913 : CollatzResearch.WordTrace tailWord_3831913 prefixEnd_3831913 1967613195212171356464859 := by
  unfold tailWord_3831913
  simp only [CollatzResearch.WordTrace]
  refine ⟨139761348966641114482988393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93174232644427409655325595 139761348966641114482988393)
  ·
    refine ⟨104821011724980835862241295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139761348966641114482988393 104821011724980835862241295)
    ·
      refine ⟨157231517587471253793361943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104821011724980835862241295 157231517587471253793361943)
      ·
        refine ⟨235847276381206880690042915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157231517587471253793361943 235847276381206880690042915)
        ·
          refine ⟨353770914571810321035064373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 235847276381206880690042915 353770914571810321035064373)
          ·
            refine ⟨33166023241107217597037285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 353770914571810321035064373 33166023241107217597037285)
            ·
              refine ⟨6218629357707603299444491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33166023241107217597037285 6218629357707603299444491)
              ·
                refine ⟨9327944036561404949166737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6218629357707603299444491 9327944036561404949166737)
                ·
                  refine ⟨6995958027421053711875053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9327944036561404949166737 6995958027421053711875053)
                  ·
                    refine ⟨2623484260282895141953145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6995958027421053711875053 2623484260282895141953145)
                    ·
                      refine ⟨1967613195212171356464859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2623484260282895141953145 1967613195212171356464859)
                      ·
                        rfl

theorem cell23_3831913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 4, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 4, 1, 2, 3, 2].length) (baseStart_3831913 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3831913 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3831913 prefixEnd_3831913 := by exact prefixLift 3831913
  have htrace : WordTrace (prefixWord ++ tailWord_3831913) baseStart_3831913 baseEnd_3831913 := by
    simpa [prefixWord, tailWord_3831913, baseEnd_3831913] using wordTrace_append hprefix tailTrace_3831913
  have hstable : (prefixWord ++ tailWord_3831913).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3831913).length < 2 ^ (prefixWord ++ tailWord_3831913).sum := by decide
  have hdescent : baseEnd_3831913 < baseStart_3831913 := by decide
  rcases family_descends (prefixWord ++ tailWord_3831913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3831919 : List Nat := [1, 1, 2, 1, 3, 4, 1, 1, 3, 6]
def baseStart_3831919 : Nat := 118140960795 + 3831919 * 2 ^ 59
def prefixEnd_3831919 : Nat := 4983230072969 + 3 ^ 40 * 3831919 * 2
def baseEnd_3831919 : Nat := 655872092032032777663277

theorem tailTrace_3831919 : CollatzResearch.WordTrace tailWord_3831919 prefixEnd_3831919 655872092032032777663277 := by
  unfold tailWord_3831919
  simp only [CollatzResearch.WordTrace]
  refine ⟨139761567804619377507706811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93174378536412918338471207 139761567804619377507706811)
  ·
    refine ⟨209642351706929066261560217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139761567804619377507706811 209642351706929066261560217)
    ·
      refine ⟨157231763780196799696170163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 209642351706929066261560217 157231763780196799696170163)
      ·
        refine ⟨235847645670295199544255245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157231763780196799696170163 235847645670295199544255245)
        ·
          refine ⟨88442867126360699829095717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 235847645670295199544255245 88442867126360699829095717)
          ·
            refine ⟨16583037586192631217955447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 88442867126360699829095717 16583037586192631217955447)
            ·
              refine ⟨24874556379288946826933171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16583037586192631217955447 24874556379288946826933171)
              ·
                refine ⟨37311834568933420240399757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24874556379288946826933171 37311834568933420240399757)
                ·
                  refine ⟨13991937963350032590149909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37311834568933420240399757 13991937963350032590149909)
                  ·
                    refine ⟨655872092032032777663277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13991937963350032590149909 655872092032032777663277)
                    ·
                      rfl

theorem cell23_3831919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 1, 1, 3, 6].length) (baseStart_3831919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3831919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3831919 prefixEnd_3831919 := by exact prefixLift 3831919
  have htrace : WordTrace (prefixWord ++ tailWord_3831919) baseStart_3831919 baseEnd_3831919 := by
    simpa [prefixWord, tailWord_3831919, baseEnd_3831919] using wordTrace_append hprefix tailTrace_3831919
  have hstable : (prefixWord ++ tailWord_3831919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3831919).length < 2 ^ (prefixWord ++ tailWord_3831919).sum := by decide
  have hdescent : baseEnd_3831919 < baseStart_3831919 := by decide
  rcases family_descends (prefixWord ++ tailWord_3831919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3831937 : List Nat := [1, 2, 4, 2, 3, 1, 1, 4, 1, 1, 3]
def baseStart_3831937 : Nat := 118140960795 + 3831937 * 2 ^ 59
def prefixEnd_3831937 : Nat := 4983230072969 + 3 ^ 40 * 3831937 * 2
def baseEnd_3831937 : Nat := 1967625518747879262564749

theorem tailTrace_3831937 : CollatzResearch.WordTrace tailWord_3831937 prefixEnd_3831937 1967625518747879262564749 := by
  unfold tailWord_3831937
  simp only [CollatzResearch.WordTrace]
  refine ⟨139762224318554166581862065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93174816212369444387908043 139762224318554166581862065)
  ·
    refine ⟨104821668238915624936396549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139762224318554166581862065 104821668238915624936396549)
    ·
      refine ⟨19654062794796679675574353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 104821668238915624936396549 19654062794796679675574353)
      ·
        refine ⟨14740547096097509756680765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19654062794796679675574353 14740547096097509756680765)
        ·
          refine ⟨5527705161036566158755287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14740547096097509756680765 5527705161036566158755287)
          ·
            refine ⟨8291557741554849238132931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5527705161036566158755287 8291557741554849238132931)
            ·
              refine ⟨12437336612332273857199397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8291557741554849238132931 12437336612332273857199397)
              ·
                refine ⟨2332000614812301348224887, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12437336612332273857199397 2332000614812301348224887)
                ·
                  refine ⟨3498000922218452022337331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2332000614812301348224887 3498000922218452022337331)
                  ·
                    refine ⟨5247001383327678033505997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3498000922218452022337331 5247001383327678033505997)
                    ·
                      refine ⟨1967625518747879262564749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5247001383327678033505997 1967625518747879262564749)
                      ·
                        rfl

theorem cell23_3831937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 1, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 1, 1, 4, 1, 1, 3].length) (baseStart_3831937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3831937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3831937 prefixEnd_3831937 := by exact prefixLift 3831937
  have htrace : WordTrace (prefixWord ++ tailWord_3831937) baseStart_3831937 baseEnd_3831937 := by
    simpa [prefixWord, tailWord_3831937, baseEnd_3831937] using wordTrace_append hprefix tailTrace_3831937
  have hstable : (prefixWord ++ tailWord_3831937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3831937).length < 2 ^ (prefixWord ++ tailWord_3831937).sum := by decide
  have hdescent : baseEnd_3831937 < baseStart_3831937 := by decide
  rcases family_descends (prefixWord ++ tailWord_3831937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3831958 : List Nat := [5, 3, 2, 1, 2, 1, 1, 1, 2, 2, 3]
def baseStart_3831958 : Nat := 118140960795 + 3831958 * 2 ^ 59
def prefixEnd_3831958 : Nat := 4983230072969 + 3 ^ 40 * 3831958 * 2
def baseEnd_3831958 : Nat := 1967636301841623680402153

theorem tailTrace_3831958 : CollatzResearch.WordTrace tailWord_3831958 prefixEnd_3831958 1967636301841623680402153 := by
  unfold tailWord_3831958
  simp only [CollatzResearch.WordTrace]
  refine ⟨8735186890717380448023533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 93175326834318724778917685 8735186890717380448023533)
  ·
    refine ⟨3275695084019017668008825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8735186890717380448023533 3275695084019017668008825)
    ·
      refine ⟨2456771313014263251006619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3275695084019017668008825 2456771313014263251006619)
      ·
        refine ⟨3685156969521394876509929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2456771313014263251006619 3685156969521394876509929)
        ·
          refine ⟨2763867727141046157382447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3685156969521394876509929 2763867727141046157382447)
          ·
            refine ⟨4145801590711569236073671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2763867727141046157382447 4145801590711569236073671)
            ·
              refine ⟨6218702386067353854110507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4145801590711569236073671 6218702386067353854110507)
              ·
                refine ⟨9328053579101030781165761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6218702386067353854110507 9328053579101030781165761)
                ·
                  refine ⟨6996040184325773085874321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9328053579101030781165761 6996040184325773085874321)
                  ·
                    refine ⟨5247030138244329814405741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6996040184325773085874321 5247030138244329814405741)
                    ·
                      refine ⟨1967636301841623680402153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5247030138244329814405741 1967636301841623680402153)
                      ·
                        rfl

theorem cell23_3831958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 2, 1, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 2, 1, 1, 1, 2, 2, 3].length) (baseStart_3831958 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3831958 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3831958 prefixEnd_3831958 := by exact prefixLift 3831958
  have htrace : WordTrace (prefixWord ++ tailWord_3831958) baseStart_3831958 baseEnd_3831958 := by
    simpa [prefixWord, tailWord_3831958, baseEnd_3831958] using wordTrace_append hprefix tailTrace_3831958
  have hstable : (prefixWord ++ tailWord_3831958).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3831958).length < 2 ^ (prefixWord ++ tailWord_3831958).sum := by decide
  have hdescent : baseEnd_3831958 < baseStart_3831958 := by decide
  rcases family_descends (prefixWord ++ tailWord_3831958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3831993 : List Nat := [1, 2, 1, 4, 1, 2, 3, 1, 4, 1, 3]
def baseStart_3831993 : Nat := 118140960795 + 3831993 * 2 ^ 59
def prefixEnd_3831993 : Nat := 4983230072969 + 3 ^ 40 * 3831993 * 2
def baseEnd_3831993 : Nat := 1967654273664531043464491

theorem tailTrace_3831993 : CollatzResearch.WordTrace tailWord_3831993 prefixEnd_3831993 1967654273664531043464491 := by
  unfold tailWord_3831993
  simp only [CollatzResearch.WordTrace]
  refine ⟨139764266806351288145900633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93176177870900858763933755 139764266806351288145900633)
  ·
    refine ⟨104823200104763466109425475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139764266806351288145900633 104823200104763466109425475)
    ·
      refine ⟨157234800157145199164138213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104823200104763466109425475 157234800157145199164138213)
      ·
        refine ⟨29481525029464724843275915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 157234800157145199164138213 29481525029464724843275915)
        ·
          refine ⟨44222287544197087264913873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29481525029464724843275915 44222287544197087264913873)
          ·
            refine ⟨33166715658147815448685405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44222287544197087264913873 33166715658147815448685405)
            ·
              refine ⟨12437518371805430793257027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33166715658147815448685405 12437518371805430793257027)
              ·
                refine ⟨18656277557708146189885541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12437518371805430793257027 18656277557708146189885541)
                ·
                  refine ⟨3498052042070277410603539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18656277557708146189885541 3498052042070277410603539)
                  ·
                    refine ⟨5247078063105416115905309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3498052042070277410603539 5247078063105416115905309)
                    ·
                      refine ⟨1967654273664531043464491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5247078063105416115905309 1967654273664531043464491)
                      ·
                        rfl

theorem cell23_3831993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 3, 1, 4, 1, 3].length) (baseStart_3831993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3831993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3831993 prefixEnd_3831993 := by exact prefixLift 3831993
  have htrace : WordTrace (prefixWord ++ tailWord_3831993) baseStart_3831993 baseEnd_3831993 := by
    simpa [prefixWord, tailWord_3831993, baseEnd_3831993] using wordTrace_append hprefix tailTrace_3831993
  have hstable : (prefixWord ++ tailWord_3831993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3831993).length < 2 ^ (prefixWord ++ tailWord_3831993).sum := by decide
  have hdescent : baseEnd_3831993 < baseStart_3831993 := by decide
  rcases family_descends (prefixWord ++ tailWord_3831993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3832009 : List Nat := [1, 2, 1, 1, 2, 1, 1, 5, 1, 8]
def baseStart_3832009 : Nat := 118140960795 + 3832009 * 2 ^ 59
def prefixEnd_3832009 : Nat := 4983230072969 + 3 ^ 40 * 3832009 * 2
def baseEnd_3832009 : Nat := 655887496451667660288139

theorem tailTrace_3832009 : CollatzResearch.WordTrace tailWord_3832009 prefixEnd_3832009 655887496451667660288139 := by
  unfold tailWord_3832009
  simp only [CollatzResearch.WordTrace]
  refine ⟨139764850374293322878483081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93176566916195548585655387 139764850374293322878483081)
  ·
    refine ⟨104823637780719992158862311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139764850374293322878483081 104823637780719992158862311)
    ·
      refine ⟨157235456671079988238293467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104823637780719992158862311 157235456671079988238293467)
      ·
        refine ⟨235853185006619982357440201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157235456671079988238293467 235853185006619982357440201)
        ·
          refine ⟨176889888754964986768080151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 235853185006619982357440201 176889888754964986768080151)
          ·
            refine ⟨265334833132447480152120227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 176889888754964986768080151 265334833132447480152120227)
            ·
              refine ⟨398002249698671220228180341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 265334833132447480152120227 398002249698671220228180341)
              ·
                refine ⟨37312710909250426896391907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 398002249698671220228180341 37312710909250426896391907)
                ·
                  refine ⟨55969066363875640344587861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37312710909250426896391907 55969066363875640344587861)
                  ·
                    refine ⟨655887496451667660288139, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 55969066363875640344587861 655887496451667660288139)
                    ·
                      rfl

theorem cell23_3832009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 5, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 5, 1, 8].length) (baseStart_3832009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3832009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3832009 prefixEnd_3832009 := by exact prefixLift 3832009
  have htrace : WordTrace (prefixWord ++ tailWord_3832009) baseStart_3832009 baseEnd_3832009 := by
    simpa [prefixWord, tailWord_3832009, baseEnd_3832009] using wordTrace_append hprefix tailTrace_3832009
  have hstable : (prefixWord ++ tailWord_3832009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3832009).length < 2 ^ (prefixWord ++ tailWord_3832009).sum := by decide
  have hdescent : baseEnd_3832009 < baseStart_3832009 := by decide
  rcases family_descends (prefixWord ++ tailWord_3832009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3832028 : List Nat := [2, 2, 5, 2, 1, 2, 1, 3, 1, 2, 2]
def baseStart_3832028 : Nat := 118140960795 + 3832028 * 2 ^ 59
def prefixEnd_3832028 : Nat := 4983230072969 + 3 ^ 40 * 3832028 * 2
def baseEnd_3832028 : Nat := 1967672245487438406526831

theorem tailTrace_3832028 : CollatzResearch.WordTrace tailWord_3832028 prefixEnd_3832028 1967672245487438406526831 := by
  unfold tailWord_3832028
  simp only [CollatzResearch.WordTrace]
  refine ⟨69882771680612244561712369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93177028907482992748949825 69882771680612244561712369)
  ·
    refine ⟨52412078760459183421284277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69882771680612244561712369 52412078760459183421284277)
    ·
      refine ⟨4913632383793048445745401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 52412078760459183421284277 4913632383793048445745401)
      ·
        refine ⟨3685224287844786334309051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4913632383793048445745401 3685224287844786334309051)
        ·
          refine ⟨5527836431767179501463577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3685224287844786334309051 5527836431767179501463577)
          ·
            refine ⟨4145877323825384626097683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5527836431767179501463577 4145877323825384626097683)
            ·
              refine ⟨6218815985738076939146525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4145877323825384626097683 6218815985738076939146525)
              ·
                refine ⟨2332055994651778852179947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6218815985738076939146525 2332055994651778852179947)
                ·
                  refine ⟨3498083991977668278269921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2332055994651778852179947 3498083991977668278269921)
                  ·
                    refine ⟨2623562993983251208702441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3498083991977668278269921 2623562993983251208702441)
                    ·
                      refine ⟨1967672245487438406526831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2623562993983251208702441 1967672245487438406526831)
                      ·
                        rfl

theorem cell23_3832028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 2, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 2, 1, 3, 1, 2, 2].length) (baseStart_3832028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3832028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3832028 prefixEnd_3832028 := by exact prefixLift 3832028
  have htrace : WordTrace (prefixWord ++ tailWord_3832028) baseStart_3832028 baseEnd_3832028 := by
    simpa [prefixWord, tailWord_3832028, baseEnd_3832028] using wordTrace_append hprefix tailTrace_3832028
  have hstable : (prefixWord ++ tailWord_3832028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3832028).length < 2 ^ (prefixWord ++ tailWord_3832028).sum := by decide
  have hdescent : baseEnd_3832028 < baseStart_3832028 := by decide
  rcases family_descends (prefixWord ++ tailWord_3832028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3832033 : List Nat := [1, 2, 3, 1, 3, 1, 2, 1, 3, 4, 2]
def baseStart_3832033 : Nat := 118140960795 + 3832033 * 2 ^ 59
def prefixEnd_3832033 : Nat := 4983230072969 + 3 ^ 40 * 3832033 * 2
def baseEnd_3832033 : Nat := 1967674812890710886964307

theorem tailTrace_3832033 : CollatzResearch.WordTrace tailWord_3832033 prefixEnd_3832033 1967674812890710886964307 := by
  unfold tailWord_3832033
  simp only [CollatzResearch.WordTrace]
  refine ⟨139765725726206374977356753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93177150484137583318237835 139765725726206374977356753)
  ·
    refine ⟨104824294294654781233017565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139765725726206374977356753 104824294294654781233017565)
    ·
      refine ⟨39309110360495542962381587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 104824294294654781233017565 39309110360495542962381587)
      ·
        refine ⟨58963665540743314443572381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39309110360495542962381587 58963665540743314443572381)
        ·
          refine ⟨22111374577778742916339643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58963665540743314443572381 22111374577778742916339643)
          ·
            refine ⟨33167061866668114374509465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22111374577778742916339643 33167061866668114374509465)
            ·
              refine ⟨24875296400001085780882099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33167061866668114374509465 24875296400001085780882099)
              ·
                refine ⟨37312944600001628671323149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24875296400001085780882099 37312944600001628671323149)
                ·
                  refine ⟨13992354225000610751746181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37312944600001628671323149 13992354225000610751746181)
                  ·
                    refine ⟨2623566417187614515952409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13992354225000610751746181 2623566417187614515952409)
                    ·
                      refine ⟨1967674812890710886964307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2623566417187614515952409 1967674812890710886964307)
                      ·
                        rfl

theorem cell23_3832033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 2, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 2, 1, 3, 4, 2].length) (baseStart_3832033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3832033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3832033 prefixEnd_3832033 := by exact prefixLift 3832033
  have htrace : WordTrace (prefixWord ++ tailWord_3832033) baseStart_3832033 baseEnd_3832033 := by
    simpa [prefixWord, tailWord_3832033, baseEnd_3832033] using wordTrace_append hprefix tailTrace_3832033
  have hstable : (prefixWord ++ tailWord_3832033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3832033).length < 2 ^ (prefixWord ++ tailWord_3832033).sum := by decide
  have hdescent : baseEnd_3832033 < baseStart_3832033 := by decide
  rcases family_descends (prefixWord ++ tailWord_3832033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3832036 : List Nat := [2, 3, 1, 1, 1, 2, 1, 2, 1, 6, 3]
def baseStart_3832036 : Nat := 118140960795 + 3832036 * 2 ^ 59
def prefixEnd_3832036 : Nat := 4983230072969 + 3 ^ 40 * 3832036 * 2
def baseEnd_3832036 : Nat := 1967676353332674375226793

theorem tailTrace_3832036 : CollatzResearch.WordTrace tailWord_3832036 prefixEnd_3832036 1967676353332674375226793 := by
  unfold tailWord_3832036
  simp only [CollatzResearch.WordTrace]
  refine ⟨69882917572597753244857981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93177223430130337659810641 69882917572597753244857981)
  ·
    refine ⟨26206094089724157466821743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69882917572597753244857981 26206094089724157466821743)
    ·
      refine ⟨39309141134586236200232615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26206094089724157466821743 39309141134586236200232615)
      ·
        refine ⟨58963711701879354300348923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39309141134586236200232615 58963711701879354300348923)
        ·
          refine ⟨88445567552819031450523385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58963711701879354300348923 88445567552819031450523385)
          ·
            refine ⟨66334175664614273587892539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 88445567552819031450523385 66334175664614273587892539)
            ·
              refine ⟨99501263496921410381838809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66334175664614273587892539 99501263496921410381838809)
              ·
                refine ⟨74625947622691057786379107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 99501263496921410381838809 74625947622691057786379107)
                ·
                  refine ⟨111938921434036586679568661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 74625947622691057786379107 111938921434036586679568661)
                  ·
                    refine ⟨5247136942220465000604781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 111938921434036586679568661 5247136942220465000604781)
                    ·
                      refine ⟨1967676353332674375226793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5247136942220465000604781 1967676353332674375226793)
                      ·
                        rfl

theorem cell23_3832036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 2, 1, 6, 3].length) (baseStart_3832036 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3832036 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3832036 prefixEnd_3832036 := by exact prefixLift 3832036
  have htrace : WordTrace (prefixWord ++ tailWord_3832036) baseStart_3832036 baseEnd_3832036 := by
    simpa [prefixWord, tailWord_3832036, baseEnd_3832036] using wordTrace_append hprefix tailTrace_3832036
  have hstable : (prefixWord ++ tailWord_3832036).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3832036).length < 2 ^ (prefixWord ++ tailWord_3832036).sum := by decide
  have hdescent : baseEnd_3832036 < baseStart_3832036 := by decide
  rcases family_descends (prefixWord ++ tailWord_3832036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3832071 : List Nat := [1, 1, 4, 5, 2, 1, 1, 2, 1, 3, 2]
def baseStart_3832071 : Nat := 118140960795 + 3832071 * 2 ^ 59
def prefixEnd_3832071 : Nat := 4983230072969 + 3 ^ 40 * 3832071 * 2
def baseEnd_3832071 : Nat := 1967694325155581738289133

theorem tailTrace_3832071 : CollatzResearch.WordTrace tailWord_3832071 prefixEnd_3832071 1967694325155581738289133 := by
  unfold tailWord_3832071
  simp only [CollatzResearch.WordTrace]
  refine ⟨139767111700068707467240067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93178074466712471644826711 139767111700068707467240067)
  ·
    refine ⟨209650667550103061200860101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139767111700068707467240067 209650667550103061200860101)
    ·
      refine ⟨39309500165644323975161269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 209650667550103061200860101 39309500165644323975161269)
      ·
        refine ⟨3685265640529155372671369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 39309500165644323975161269 3685265640529155372671369)
        ·
          refine ⟨2763949230396866529503527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3685265640529155372671369 2763949230396866529503527)
          ·
            refine ⟨4145923845595299794255291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2763949230396866529503527 4145923845595299794255291)
            ·
              refine ⟨6218885768392949691382937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4145923845595299794255291 6218885768392949691382937)
              ·
                refine ⟨4664164326294712268537203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6218885768392949691382937 4664164326294712268537203)
                ·
                  refine ⟨6996246489442068402805805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4664164326294712268537203 6996246489442068402805805)
                  ·
                    refine ⟨2623592433540775651052177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6996246489442068402805805 2623592433540775651052177)
                    ·
                      refine ⟨1967694325155581738289133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2623592433540775651052177 1967694325155581738289133)
                      ·
                        rfl

theorem cell23_3832071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 2, 1, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 2, 1, 1, 2, 1, 3, 2].length) (baseStart_3832071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3832071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3832071 prefixEnd_3832071 := by exact prefixLift 3832071
  have htrace : WordTrace (prefixWord ++ tailWord_3832071) baseStart_3832071 baseEnd_3832071 := by
    simpa [prefixWord, tailWord_3832071, baseEnd_3832071] using wordTrace_append hprefix tailTrace_3832071
  have hstable : (prefixWord ++ tailWord_3832071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3832071).length < 2 ^ (prefixWord ++ tailWord_3832071).sum := by decide
  have hdescent : baseEnd_3832071 < baseStart_3832071 := by decide
  rcases family_descends (prefixWord ++ tailWord_3832071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3832143 : List Nat := [1, 1, 2, 1, 1, 2, 1, 7, 2, 2, 3]
def baseStart_3832143 : Nat := 118140960795 + 3832143 * 2 ^ 59
def prefixEnd_3832143 : Nat := 4983230072969 + 3 ^ 40 * 3832143 * 2
def baseEnd_3832143 : Nat := 1967731295762705456588801

theorem tailTrace_3832143 : CollatzResearch.WordTrace tailWord_3832143 prefixEnd_3832143 1967731295762705456588801 := by
  unfold tailWord_3832143
  simp only [CollatzResearch.WordTrace]
  refine ⟨139769737755807863763861083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93179825170538575842574055 139769737755807863763861083)
  ·
    refine ⟨209654606633711795645791625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139769737755807863763861083 209654606633711795645791625)
    ·
      refine ⟨157240954975283846734343719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 209654606633711795645791625 157240954975283846734343719)
      ·
        refine ⟨235861432462925770101515579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157240954975283846734343719 235861432462925770101515579)
        ·
          refine ⟨353792148694388655152273369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 235861432462925770101515579 353792148694388655152273369)
          ·
            refine ⟨265344111520791491364205027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 353792148694388655152273369 265344111520791491364205027)
            ·
              refine ⟨398016167281187237046307541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 265344111520791491364205027 398016167281187237046307541)
              ·
                refine ⟨9328503920652825868272833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 398016167281187237046307541 9328503920652825868272833)
                ·
                  refine ⟨6996377940489619401204625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9328503920652825868272833 6996377940489619401204625)
                  ·
                    refine ⟨5247283455367214550903469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6996377940489619401204625 5247283455367214550903469)
                    ·
                      refine ⟨1967731295762705456588801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5247283455367214550903469 1967731295762705456588801)
                      ·
                        rfl

theorem cell23_3832143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 7, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 7, 2, 2, 3].length) (baseStart_3832143 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3832143 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3832143 prefixEnd_3832143 := by exact prefixLift 3832143
  have htrace : WordTrace (prefixWord ++ tailWord_3832143) baseStart_3832143 baseEnd_3832143 := by
    simpa [prefixWord, tailWord_3832143, baseEnd_3832143] using wordTrace_append hprefix tailTrace_3832143
  have hstable : (prefixWord ++ tailWord_3832143).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3832143).length < 2 ^ (prefixWord ++ tailWord_3832143).sum := by decide
  have hdescent : baseEnd_3832143 < baseStart_3832143 := by decide
  rcases family_descends (prefixWord ++ tailWord_3832143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3832167 : List Nat := [1, 1, 5, 1, 3, 1, 2, 4, 1, 4]
def baseStart_3832167 : Nat := 118140960795 + 3832167 * 2 ^ 59
def prefixEnd_3832167 : Nat := 4983230072969 + 3 ^ 40 * 3832167 * 2
def baseEnd_3832167 : Nat := 655914539766137787562897

theorem tailTrace_3832167 : CollatzResearch.WordTrace tailWord_3832167 prefixEnd_3832167 655914539766137787562897 := by
  unfold tailWord_3832167
  simp only [CollatzResearch.WordTrace]
  refine ⟨139770613107720915862734755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93180408738480610575156503 139770613107720915862734755)
  ·
    refine ⟨209655919661581373794102133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139770613107720915862734755 209655919661581373794102133)
    ·
      refine ⟨19655242468273253793197075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 209655919661581373794102133 19655242468273253793197075)
      ·
        refine ⟨29482863702409880689795613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19655242468273253793197075 29482863702409880689795613)
        ·
          refine ⟨11056073888403705258673355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29482863702409880689795613 11056073888403705258673355)
          ·
            refine ⟨16584110832605557888010033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11056073888403705258673355 16584110832605557888010033)
            ·
              refine ⟨12438083124454168416007525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16584110832605557888010033 12438083124454168416007525)
              ·
                refine ⟨2332140585835156578001411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12438083124454168416007525 2332140585835156578001411)
                ·
                  refine ⟨3498210878752734867002117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2332140585835156578001411 3498210878752734867002117)
                  ·
                    refine ⟨655914539766137787562897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3498210878752734867002117 655914539766137787562897)
                    ·
                      rfl

theorem cell23_3832167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 2, 4, 1, 4].length) (baseStart_3832167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3832167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3832167 prefixEnd_3832167 := by exact prefixLift 3832167
  have htrace : WordTrace (prefixWord ++ tailWord_3832167) baseStart_3832167 baseEnd_3832167 := by
    simpa [prefixWord, tailWord_3832167, baseEnd_3832167] using wordTrace_append hprefix tailTrace_3832167
  have hstable : (prefixWord ++ tailWord_3832167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3832167).length < 2 ^ (prefixWord ++ tailWord_3832167).sum := by decide
  have hdescent : baseEnd_3832167 < baseStart_3832167 := by decide
  rcases family_descends (prefixWord ++ tailWord_3832167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3832200 : List Nat := [2, 1, 3, 3, 1, 1, 1, 3, 1, 5, 2]
def baseStart_3832200 : Nat := 118140960795 + 3832200 * 2 ^ 59
def prefixEnd_3832200 : Nat := 4983230072969 + 3 ^ 40 * 3832200 * 2
def baseEnd_3832200 : Nat := 1967760564160011733576039

theorem tailTrace_3832200 : CollatzResearch.WordTrace tailWord_3832200 prefixEnd_3832200 1967760564160011733576039 := by
  unfold tailWord_3832200
  simp only [CollatzResearch.WordTrace]
  refine ⟨69885908358300681249343027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93181211144400908332457369 69885908358300681249343027)
  ·
    refine ⟨104828862537451021874014541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69885908358300681249343027 104828862537451021874014541)
    ·
      refine ⟨39310823451544133202755453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 104828862537451021874014541 39310823451544133202755453)
      ·
        refine ⟨14741558794329049951033295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39310823451544133202755453 14741558794329049951033295)
        ·
          refine ⟨22112338191493574926549943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14741558794329049951033295 22112338191493574926549943)
          ·
            refine ⟨33168507287240362389824915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22112338191493574926549943 33168507287240362389824915)
            ·
              refine ⟨49752760930860543584737373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33168507287240362389824915 49752760930860543584737373)
              ·
                refine ⟨18657285349072703844276515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49752760930860543584737373 18657285349072703844276515)
                ·
                  refine ⟨27985928023609055766414773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18657285349072703844276515 27985928023609055766414773)
                  ·
                    refine ⟨2623680752213348978101385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 27985928023609055766414773 2623680752213348978101385)
                    ·
                      refine ⟨1967760564160011733576039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2623680752213348978101385 1967760564160011733576039)
                      ·
                        rfl

theorem cell23_3832200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 1, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 1, 3, 1, 5, 2].length) (baseStart_3832200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3832200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3832200 prefixEnd_3832200 := by exact prefixLift 3832200
  have htrace : WordTrace (prefixWord ++ tailWord_3832200) baseStart_3832200 baseEnd_3832200 := by
    simpa [prefixWord, tailWord_3832200, baseEnd_3832200] using wordTrace_append hprefix tailTrace_3832200
  have hstable : (prefixWord ++ tailWord_3832200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3832200).length < 2 ^ (prefixWord ++ tailWord_3832200).sum := by decide
  have hdescent : baseEnd_3832200 < baseStart_3832200 := by decide
  rcases family_descends (prefixWord ++ tailWord_3832200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3832213 : List Nat := [1, 3, 2, 1, 1, 2, 1, 2, 5, 1, 4]
def baseStart_3832213 : Nat := 118140960795 + 3832213 * 2 ^ 59
def prefixEnd_3832213 : Nat := 4983230072969 + 3 ^ 40 * 3832213 * 2
def baseEnd_3832213 : Nat := 1967767239408520182713479

theorem tailTrace_3832213 : CollatzResearch.WordTrace tailWord_3832213 prefixEnd_3832213 1967767239408520182713479 := by
  unfold tailWord_3832213
  simp only [CollatzResearch.WordTrace]
  refine ⟨139772290865554265718909293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93181527243702843812606195 139772290865554265718909293)
  ·
    refine ⟨52414609074582849644590985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 139772290865554265718909293 52414609074582849644590985)
    ·
      refine ⟨39310956805937137233443239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52414609074582849644590985 39310956805937137233443239)
      ·
        refine ⟨58966435208905705850164859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39310956805937137233443239 58966435208905705850164859)
        ·
          refine ⟨88449652813358558775247289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58966435208905705850164859 88449652813358558775247289)
          ·
            refine ⟨66337239610018919081435467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 88449652813358558775247289 66337239610018919081435467)
            ·
              refine ⟨99505859415028378622153201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66337239610018919081435467 99505859415028378622153201)
              ·
                refine ⟨74629394561271283966614901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 99505859415028378622153201 74629394561271283966614901)
                ·
                  refine ⟨6996505740119182871870147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 74629394561271283966614901 6996505740119182871870147)
                  ·
                    refine ⟨10494758610178774307805221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6996505740119182871870147 10494758610178774307805221)
                    ·
                      refine ⟨1967767239408520182713479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10494758610178774307805221 1967767239408520182713479)
                      ·
                        rfl

theorem cell23_3832213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 2, 5, 1, 4].length) (baseStart_3832213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3832213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3832213 prefixEnd_3832213 := by exact prefixLift 3832213
  have htrace : WordTrace (prefixWord ++ tailWord_3832213) baseStart_3832213 baseEnd_3832213 := by
    simpa [prefixWord, tailWord_3832213, baseEnd_3832213] using wordTrace_append hprefix tailTrace_3832213
  have hstable : (prefixWord ++ tailWord_3832213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3832213).length < 2 ^ (prefixWord ++ tailWord_3832213).sum := by decide
  have hdescent : baseEnd_3832213 < baseStart_3832213 := by decide
  rcases family_descends (prefixWord ++ tailWord_3832213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3832244 : List Nat := [2, 5, 2, 2, 1, 1, 1, 1, 3, 5]
def baseStart_3832244 : Nat := 118140960795 + 3832244 * 2 ^ 59
def prefixEnd_3832244 : Nat := 4983230072969 + 3 ^ 40 * 3832244 * 2
def baseEnd_3832244 : Nat := 655927719102936520475279

theorem tailTrace_3832244 : CollatzResearch.WordTrace tailWord_3832244 prefixEnd_3832244 655927719102936520475279 := by
  unfold tailWord_3832244
  simp only [CollatzResearch.WordTrace]
  refine ⟨69886710764220979006643893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93182281018961305342191857 69886710764220979006643893)
  ·
    refine ⟨6551879134145716781872865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 69886710764220979006643893 6551879134145716781872865)
    ·
      refine ⟨4913909350609287586404649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6551879134145716781872865 4913909350609287586404649)
      ·
        refine ⟨3685432012956965689803487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4913909350609287586404649 3685432012956965689803487)
        ·
          refine ⟨5528148019435448534705231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3685432012956965689803487 5528148019435448534705231)
          ·
            refine ⟨8292222029153172802057847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5528148019435448534705231 8292222029153172802057847)
            ·
              refine ⟨12438333043729759203086771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8292222029153172802057847 12438333043729759203086771)
              ·
                refine ⟨18657499565594638804630157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12438333043729759203086771 18657499565594638804630157)
                ·
                  refine ⟨6996562337097989551736309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18657499565594638804630157 6996562337097989551736309)
                  ·
                    refine ⟨655927719102936520475279, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6996562337097989551736309 655927719102936520475279)
                    ·
                      rfl

theorem cell23_3832244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 1, 1, 1, 3, 5].length) (baseStart_3832244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3832244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3832244 prefixEnd_3832244 := by exact prefixLift 3832244
  have htrace : WordTrace (prefixWord ++ tailWord_3832244) baseStart_3832244 baseEnd_3832244 := by
    simpa [prefixWord, tailWord_3832244, baseEnd_3832244] using wordTrace_append hprefix tailTrace_3832244
  have hstable : (prefixWord ++ tailWord_3832244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3832244).length < 2 ^ (prefixWord ++ tailWord_3832244).sum := by decide
  have hdescent : baseEnd_3832244 < baseStart_3832244 := by decide
  rcases family_descends (prefixWord ++ tailWord_3832244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3832247 : List Nat := [1, 1, 3, 1, 3, 5, 1, 2, 1, 1, 4]
def baseStart_3832247 : Nat := 118140960795 + 3832247 * 2 ^ 59
def prefixEnd_3832247 : Nat := 4983230072969 + 3 ^ 40 * 3832247 * 2
def baseEnd_3832247 : Nat := 1967784697750773049688323

theorem tailTrace_3832247 : CollatzResearch.WordTrace tailWord_3832247 prefixEnd_3832247 1967784697750773049688323 := by
  unfold tailWord_3832247
  simp only [CollatzResearch.WordTrace]
  refine ⟨139773530947431089525646995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93182353964954059683764663 139773530947431089525646995)
  ·
    refine ⟨209660296421146634288470493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139773530947431089525646995 209660296421146634288470493)
    ·
      refine ⟨78622611157929987858176435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 209660296421146634288470493 78622611157929987858176435)
      ·
        refine ⟨117933916736894981787264653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78622611157929987858176435 117933916736894981787264653)
        ·
          refine ⟨44225218776335618170224245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 117933916736894981787264653 44225218776335618170224245)
          ·
            refine ⟨4146114260281464203458523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 44225218776335618170224245 4146114260281464203458523)
            ·
              refine ⟨6219171390422196305187785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4146114260281464203458523 6219171390422196305187785)
              ·
                refine ⟨4664378542816647228890839, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6219171390422196305187785 4664378542816647228890839)
                ·
                  refine ⟨6996567814224970843336259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4664378542816647228890839 6996567814224970843336259)
                  ·
                    refine ⟨10494851721337456265004389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6996567814224970843336259 10494851721337456265004389)
                    ·
                      refine ⟨1967784697750773049688323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10494851721337456265004389 1967784697750773049688323)
                      ·
                        rfl

theorem cell23_3832247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 5, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 5, 1, 2, 1, 1, 4].length) (baseStart_3832247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3832247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3832247 prefixEnd_3832247 := by exact prefixLift 3832247
  have htrace : WordTrace (prefixWord ++ tailWord_3832247) baseStart_3832247 baseEnd_3832247 := by
    simpa [prefixWord, tailWord_3832247, baseEnd_3832247] using wordTrace_append hprefix tailTrace_3832247
  have hstable : (prefixWord ++ tailWord_3832247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3832247).length < 2 ^ (prefixWord ++ tailWord_3832247).sum := by decide
  have hdescent : baseEnd_3832247 < baseStart_3832247 := by decide
  rcases family_descends (prefixWord ++ tailWord_3832247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3832253 : List Nat := [1, 4, 1, 2, 2, 2, 2, 9]
def baseStart_3832253 : Nat := 118140960795 + 3832253 * 2 ^ 59
def prefixEnd_3832253 : Nat := 4983230072969 + 3 ^ 40 * 3832253 * 2
def baseEnd_3832253 : Nat := 72881028838322223193085

theorem tailTrace_3832253 : CollatzResearch.WordTrace tailWord_3832253 prefixEnd_3832253 72881028838322223193085 := by
  unfold tailWord_3832253
  simp only [CollatzResearch.WordTrace]
  refine ⟨139773749785409352550365413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93182499856939568366910275 139773749785409352550365413)
  ·
    refine ⟨26207578084764253603193515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 139773749785409352550365413 26207578084764253603193515)
    ·
      refine ⟨39311367127146380404790273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26207578084764253603193515 39311367127146380404790273)
      ·
        refine ⟨29483525345359785303592705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39311367127146380404790273 29483525345359785303592705)
        ·
          refine ⟨22112644009019838977694529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29483525345359785303592705 22112644009019838977694529)
          ·
            refine ⟨16584483006764879233270897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22112644009019838977694529 16584483006764879233270897)
            ·
              refine ⟨12438362255073659424953173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16584483006764879233270897 12438362255073659424953173)
              ·
                refine ⟨72881028838322223193085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 12438362255073659424953173 72881028838322223193085)
                ·
                  rfl

theorem cell23_3832253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 2, 9].length) (baseStart_3832253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3832253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3832253 prefixEnd_3832253 := by exact prefixLift 3832253
  have htrace : WordTrace (prefixWord ++ tailWord_3832253) baseStart_3832253 baseEnd_3832253 := by
    simpa [prefixWord, tailWord_3832253, baseEnd_3832253] using wordTrace_append hprefix tailTrace_3832253
  have hstable : (prefixWord ++ tailWord_3832253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3832253).length < 2 ^ (prefixWord ++ tailWord_3832253).sum := by decide
  have hdescent : baseEnd_3832253 < baseStart_3832253 := by decide
  rcases family_descends (prefixWord ++ tailWord_3832253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3832303 : List Nat := [1, 1, 2, 1, 4, 1, 1, 1, 4, 3, 4]
def baseStart_3832303 : Nat := 118140960795 + 3832303 * 2 ^ 59
def prefixEnd_3832303 : Nat := 4983230072969 + 3 ^ 40 * 3832303 * 2
def baseEnd_3832303 : Nat := 1967813452667424830588065

theorem tailTrace_3832303 : CollatzResearch.WordTrace tailWord_3832303 prefixEnd_3832303 1967813452667424830588065 := by
  unfold tailWord_3832303
  simp only [CollatzResearch.WordTrace]
  refine ⟨139775573435228211089685563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93183715623485474059790375 139775573435228211089685563)
  ·
    refine ⟨209663360152842316634528345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139775573435228211089685563 209663360152842316634528345)
    ·
      refine ⟨157247520114631737475896259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 209663360152842316634528345 157247520114631737475896259)
      ·
        refine ⟨235871280171947606213844389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157247520114631737475896259 235871280171947606213844389)
        ·
          refine ⟨44225865032240176165095823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 235871280171947606213844389 44225865032240176165095823)
          ·
            refine ⟨66338797548360264247643735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44225865032240176165095823 66338797548360264247643735)
            ·
              refine ⟨99508196322540396371465603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66338797548360264247643735 99508196322540396371465603)
              ·
                refine ⟨149262294483810594557198405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 99508196322540396371465603 149262294483810594557198405)
                ·
                  refine ⟨27986680215714486479474701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 149262294483810594557198405 27986680215714486479474701)
                  ·
                    refine ⟨10495005080892932429803013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27986680215714486479474701 10495005080892932429803013)
                    ·
                      refine ⟨1967813452667424830588065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10495005080892932429803013 1967813452667424830588065)
                      ·
                        rfl

theorem cell23_3832303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 1, 4, 3, 4].length) (baseStart_3832303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3832303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3832303 prefixEnd_3832303 := by exact prefixLift 3832303
  have htrace : WordTrace (prefixWord ++ tailWord_3832303) baseStart_3832303 baseEnd_3832303 := by
    simpa [prefixWord, tailWord_3832303, baseEnd_3832303] using wordTrace_append hprefix tailTrace_3832303
  have hstable : (prefixWord ++ tailWord_3832303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3832303).length < 2 ^ (prefixWord ++ tailWord_3832303).sum := by decide
  have hdescent : baseEnd_3832303 < baseStart_3832303 := by decide
  rcases family_descends (prefixWord ++ tailWord_3832303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3832307 : List Nat := [1, 1, 1, 2, 2, 2, 4, 4, 1, 3, 2]
def baseStart_3832307 : Nat := 118140960795 + 3832307 * 2 ^ 59
def prefixEnd_3832307 : Nat := 4983230072969 + 3 ^ 40 * 3832307 * 2
def baseEnd_3832307 : Nat := 1967815506590042814938047

theorem tailTrace_3832307 : CollatzResearch.WordTrace tailWord_3832307 prefixEnd_3832307 1967815506590042814938047 := by
  unfold tailWord_3832307
  simp only [CollatzResearch.WordTrace]
  refine ⟨139775719327213719772831175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93183812884809146515220783 139775719327213719772831175)
  ·
    refine ⟨209663578990820579659246763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139775719327213719772831175 209663578990820579659246763)
    ·
      refine ⟨314495368486230869488870145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209663578990820579659246763 314495368486230869488870145)
      ·
        refine ⟨235871526364673152116652609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 314495368486230869488870145 235871526364673152116652609)
        ·
          refine ⟨176903644773504864087489457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 235871526364673152116652609 176903644773504864087489457)
          ·
            refine ⟨132677733580128648065617093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 176903644773504864087489457 132677733580128648065617093)
            ·
              refine ⟨24877075046274121512303205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 132677733580128648065617093 24877075046274121512303205)
              ·
                refine ⟨4664451571176397783556851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24877075046274121512303205 4664451571176397783556851)
                ·
                  refine ⟨6996677356764596675335277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4664451571176397783556851 6996677356764596675335277)
                  ·
                    refine ⟨2623754008786723753250729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6996677356764596675335277 2623754008786723753250729)
                    ·
                      refine ⟨1967815506590042814938047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2623754008786723753250729 1967815506590042814938047)
                      ·
                        rfl

theorem cell23_3832307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 4, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 4, 4, 1, 3, 2].length) (baseStart_3832307 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3832307 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3832307 prefixEnd_3832307 := by exact prefixLift 3832307
  have htrace : WordTrace (prefixWord ++ tailWord_3832307) baseStart_3832307 baseEnd_3832307 := by
    simpa [prefixWord, tailWord_3832307, baseEnd_3832307] using wordTrace_append hprefix tailTrace_3832307
  have hstable : (prefixWord ++ tailWord_3832307).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3832307).length < 2 ^ (prefixWord ++ tailWord_3832307).sum := by decide
  have hdescent : baseEnd_3832307 < baseStart_3832307 := by decide
  rcases family_descends (prefixWord ++ tailWord_3832307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3832310 : List Nat := [5, 1, 1, 1, 2, 1, 2, 1, 2, 2, 5]
def baseStart_3832310 : Nat := 118140960795 + 3832310 * 2 ^ 59
def prefixEnd_3832310 : Nat := 4983230072969 + 3 ^ 40 * 3832310 * 2
def baseEnd_3832310 : Nat := 1967817047032006303200533

theorem tailTrace_3832310 : CollatzResearch.WordTrace tailWord_3832310 prefixEnd_3832310 1967817047032006303200533 := by
  unfold tailWord_3832310
  simp only [CollatzResearch.WordTrace]
  refine ⟨8735989296637678205324399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 93183885830801900856793589 8735989296637678205324399)
  ·
    refine ⟨13103983944956517307986599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8735989296637678205324399 13103983944956517307986599)
    ·
      refine ⟨19655975917434775961979899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13103983944956517307986599 19655975917434775961979899)
      ·
        refine ⟨29483963876152163942969849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19655975917434775961979899 29483963876152163942969849)
        ·
          refine ⟨22112972907114122957227387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29483963876152163942969849 22112972907114122957227387)
          ·
            refine ⟨33169459360671184435841081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22112972907114122957227387 33169459360671184435841081)
            ·
              refine ⟨24877094520503388326880811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33169459360671184435841081 24877094520503388326880811)
              ·
                refine ⟨37315641780755082490321217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24877094520503388326880811 37315641780755082490321217)
                ·
                  refine ⟨27986731335566311867740913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37315641780755082490321217 27986731335566311867740913)
                  ·
                    refine ⟨20990048501674733900805685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27986731335566311867740913 20990048501674733900805685)
                    ·
                      refine ⟨1967817047032006303200533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20990048501674733900805685 1967817047032006303200533)
                      ·
                        rfl

theorem cell23_3832310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 2, 1, 2, 2, 5].length) (baseStart_3832310 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3832310 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3832310 prefixEnd_3832310 := by exact prefixLift 3832310
  have htrace : WordTrace (prefixWord ++ tailWord_3832310) baseStart_3832310 baseEnd_3832310 := by
    simpa [prefixWord, tailWord_3832310, baseEnd_3832310] using wordTrace_append hprefix tailTrace_3832310
  have hstable : (prefixWord ++ tailWord_3832310).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3832310).length < 2 ^ (prefixWord ++ tailWord_3832310).sum := by decide
  have hdescent : baseEnd_3832310 < baseStart_3832310 := by decide
  rcases family_descends (prefixWord ++ tailWord_3832310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3832323 : List Nat := [1, 1, 1, 3, 2, 1, 4, 1, 1, 3, 5]
def baseStart_3832323 : Nat := 118140960795 + 3832323 * 2 ^ 59
def prefixEnd_3832323 : Nat := 4983230072969 + 3 ^ 40 * 3832323 * 2
def baseEnd_3832323 : Nat := 1967823722280514752337973

theorem tailTrace_3832323 : CollatzResearch.WordTrace tailWord_3832323 prefixEnd_3832323 1967823722280514752337973 := by
  unfold tailWord_3832323
  simp only [CollatzResearch.WordTrace]
  refine ⟨139776302895155754505413623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93184201930103836336942415 139776302895155754505413623)
  ·
    refine ⟨209664454342733631758120435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139776302895155754505413623 209664454342733631758120435)
    ·
      refine ⟨314496681514100447637180653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209664454342733631758120435 314496681514100447637180653)
      ·
        refine ⟨117936255567787667863942745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 314496681514100447637180653 117936255567787667863942745)
        ·
          refine ⟨88452191675840750897957059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 117936255567787667863942745 88452191675840750897957059)
          ·
            refine ⟨132678287513761126346935589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88452191675840750897957059 132678287513761126346935589)
            ·
              refine ⟨24877178908830211190050423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 132678287513761126346935589 24877178908830211190050423)
              ·
                refine ⟨37315768363245316785075635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24877178908830211190050423 37315768363245316785075635)
                ·
                  refine ⟨55973652544867975177613453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37315768363245316785075635 55973652544867975177613453)
                  ·
                    refine ⟨20990119704325490691605045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 55973652544867975177613453 20990119704325490691605045)
                    ·
                      refine ⟨1967823722280514752337973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20990119704325490691605045 1967823722280514752337973)
                      ·
                        rfl

theorem cell23_3832323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 4, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 4, 1, 1, 3, 5].length) (baseStart_3832323 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3832323 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3832323 prefixEnd_3832323 := by exact prefixLift 3832323
  have htrace : WordTrace (prefixWord ++ tailWord_3832323) baseStart_3832323 baseEnd_3832323 := by
    simpa [prefixWord, tailWord_3832323, baseEnd_3832323] using wordTrace_append hprefix tailTrace_3832323
  have hstable : (prefixWord ++ tailWord_3832323).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3832323).length < 2 ^ (prefixWord ++ tailWord_3832323).sum := by decide
  have hdescent : baseEnd_3832323 < baseStart_3832323 := by decide
  rcases family_descends (prefixWord ++ tailWord_3832323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3832370 : List Nat := [3, 2, 1, 1, 2, 1, 2, 2, 1, 5, 3]
def baseStart_3832370 : Nat := 118140960795 + 3832370 * 2 ^ 59
def prefixEnd_3832370 : Nat := 4983230072969 + 3 ^ 40 * 3832370 * 2
def baseEnd_3832370 : Nat := 1967847855871276068450257

theorem tailTrace_3832370 : CollatzResearch.WordTrace tailWord_3832370 prefixEnd_3832370 1967847855871276068450257 := by
  unfold tailWord_3832370
  simp only [CollatzResearch.WordTrace]
  refine ⟨34944504281496370383093641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93185344750656987688249709 34944504281496370383093641)
  ·
    refine ⟨26208378211122277787320231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34944504281496370383093641 26208378211122277787320231)
    ·
      refine ⟨39312567316683416680980347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26208378211122277787320231 39312567316683416680980347)
      ·
        refine ⟨58968850975025125021470521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39312567316683416680980347 58968850975025125021470521)
        ·
          refine ⟨44226638231268843766102891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58968850975025125021470521 44226638231268843766102891)
          ·
            refine ⟨66339957346903265649154337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44226638231268843766102891 66339957346903265649154337)
            ·
              refine ⟨49754968010177449236865753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66339957346903265649154337 49754968010177449236865753)
              ·
                refine ⟨37316226007633086927649315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49754968010177449236865753 37316226007633086927649315)
                ·
                  refine ⟨55974339011449630391473973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37316226007633086927649315 55974339011449630391473973)
                  ·
                    refine ⟨5247594282323402849200685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 55974339011449630391473973 5247594282323402849200685)
                    ·
                      refine ⟨1967847855871276068450257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5247594282323402849200685 1967847855871276068450257)
                      ·
                        rfl

theorem cell23_3832370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 2, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 2, 2, 1, 5, 3].length) (baseStart_3832370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3832370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3832370 prefixEnd_3832370 := by exact prefixLift 3832370
  have htrace : WordTrace (prefixWord ++ tailWord_3832370) baseStart_3832370 baseEnd_3832370 := by
    simpa [prefixWord, tailWord_3832370, baseEnd_3832370] using wordTrace_append hprefix tailTrace_3832370
  have hstable : (prefixWord ++ tailWord_3832370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3832370).length < 2 ^ (prefixWord ++ tailWord_3832370).sum := by decide
  have hdescent : baseEnd_3832370 < baseStart_3832370 := by decide
  rcases family_descends (prefixWord ++ tailWord_3832370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3832393 : List Nat := [1, 2, 1, 1, 2, 2, 1, 1, 2, 2, 8]
def baseStart_3832393 : Nat := 118140960795 + 3832393 * 2 ^ 59
def prefixEnd_3832393 : Nat := 4983230072969 + 3 ^ 40 * 3832393 * 2
def baseEnd_3832393 : Nat := 1967859665926329478462651

theorem tailTrace_3832393 : CollatzResearch.WordTrace tailWord_3832393 prefixEnd_3832393 1967859665926329478462651 := by
  unfold tailWord_3832393
  simp only [CollatzResearch.WordTrace]
  refine ⟨139778856004902156460461833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93185904003268104306974555 139778856004902156460461833)
  ·
    refine ⟨104834142003676617345346375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139778856004902156460461833 104834142003676617345346375)
    ·
      refine ⟨157251213005514926018019563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104834142003676617345346375 157251213005514926018019563)
      ·
        refine ⟨235876819508272389027029345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157251213005514926018019563 235876819508272389027029345)
        ·
          refine ⟨176907614631204291770272009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 235876819508272389027029345 176907614631204291770272009)
          ·
            refine ⟨132680710973403218827704007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 176907614631204291770272009 132680710973403218827704007)
            ·
              refine ⟨199021066460104828241556011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 132680710973403218827704007 199021066460104828241556011)
              ·
                refine ⟨298531599690157242362334017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 199021066460104828241556011 298531599690157242362334017)
                ·
                  refine ⟨223898699767617931771750513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 298531599690157242362334017 223898699767617931771750513)
                  ·
                    refine ⟨167924024825713448828812885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 223898699767617931771750513 167924024825713448828812885)
                    ·
                      refine ⟨1967859665926329478462651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 167924024825713448828812885 1967859665926329478462651)
                      ·
                        rfl

theorem cell23_3832393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 1, 2, 2, 8].length) (baseStart_3832393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3832393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3832393 prefixEnd_3832393 := by exact prefixLift 3832393
  have htrace : WordTrace (prefixWord ++ tailWord_3832393) baseStart_3832393 baseEnd_3832393 := by
    simpa [prefixWord, tailWord_3832393, baseEnd_3832393] using wordTrace_append hprefix tailTrace_3832393
  have hstable : (prefixWord ++ tailWord_3832393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3832393).length < 2 ^ (prefixWord ++ tailWord_3832393).sum := by decide
  have hdescent : baseEnd_3832393 < baseStart_3832393 := by decide
  rcases family_descends (prefixWord ++ tailWord_3832393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3832394 : List Nat := [3, 1, 2, 1, 1, 5, 3, 2, 5]
def baseStart_3832394 : Nat := 118140960795 + 3832394 * 2 ^ 59
def prefixEnd_3832394 : Nat := 4983230072969 + 3 ^ 40 * 3832394 * 2
def baseEnd_3832394 : Nat := 218651131045220441616683

theorem tailTrace_3832394 : CollatzResearch.WordTrace tailWord_3832394 prefixEnd_3832394 218651131045220441616683 := by
  unfold tailWord_3832394
  simp only [CollatzResearch.WordTrace]
  refine ⟨34944723119474633407812059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93185928318599022420832157 34944723119474633407812059)
  ·
    refine ⟨52417084679211950111718089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34944723119474633407812059 52417084679211950111718089)
    ·
      refine ⟨39312813509408962583788567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52417084679211950111718089 39312813509408962583788567)
      ·
        refine ⟨58969220264113443875682851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39312813509408962583788567 58969220264113443875682851)
        ·
          refine ⟨88453830396170165813524277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58969220264113443875682851 88453830396170165813524277)
          ·
            refine ⟨8292546599640953045017901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 88453830396170165813524277 8292546599640953045017901)
            ·
              refine ⟨3109704974865357391881713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8292546599640953045017901 3109704974865357391881713)
              ·
                refine ⟨2332278731149018043911285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3109704974865357391881713 2332278731149018043911285)
                ·
                  refine ⟨218651131045220441616683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2332278731149018043911285 218651131045220441616683)
                  ·
                    rfl

theorem cell23_3832394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 5, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 5, 3, 2, 5].length) (baseStart_3832394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3832394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3832394 prefixEnd_3832394 := by exact prefixLift 3832394
  have htrace : WordTrace (prefixWord ++ tailWord_3832394) baseStart_3832394 baseEnd_3832394 := by
    simpa [prefixWord, tailWord_3832394, baseEnd_3832394] using wordTrace_append hprefix tailTrace_3832394
  have hstable : (prefixWord ++ tailWord_3832394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3832394).length < 2 ^ (prefixWord ++ tailWord_3832394).sum := by decide
  have hdescent : baseEnd_3832394 < baseStart_3832394 := by decide
  rcases family_descends (prefixWord ++ tailWord_3832394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3832424 : List Nat := [2, 1, 4, 3, 2, 1, 2, 1, 2, 5]
def baseStart_3832424 : Nat := 118140960795 + 3832424 * 2 ^ 59
def prefixEnd_3832424 : Nat := 4983230072969 + 3 ^ 40 * 3832424 * 2
def baseEnd_3832424 : Nat := 655958527942206285725003

theorem tailTrace_3832424 : CollatzResearch.WordTrace tailWord_3832424 prefixEnd_3832424 655958527942206285725003 := by
  unfold tailWord_3832424
  simp only [CollatzResearch.WordTrace]
  refine ⟨69889993333894924377420163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93186657778526565836560217 69889993333894924377420163)
  ·
    refine ⟨104834990000842386566130245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69889993333894924377420163 104834990000842386566130245)
    ·
      refine ⟨19656560625157947481149421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 104834990000842386566130245 19656560625157947481149421)
      ·
        refine ⟨7371210234434230305431033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19656560625157947481149421 7371210234434230305431033)
        ·
          refine ⟨5528407675825672729073275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7371210234434230305431033 5528407675825672729073275)
          ·
            refine ⟨8292611513738509093609913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5528407675825672729073275 8292611513738509093609913)
            ·
              refine ⟨6219458635303881820207435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8292611513738509093609913 6219458635303881820207435)
              ·
                refine ⟨9329187952955822730311153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6219458635303881820207435 9329187952955822730311153)
                ·
                  refine ⟨6996890964716867047733365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9329187952955822730311153 6996890964716867047733365)
                  ·
                    refine ⟨655958527942206285725003, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6996890964716867047733365 655958527942206285725003)
                    ·
                      rfl

theorem cell23_3832424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 1, 2, 1, 2, 5].length) (baseStart_3832424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3832424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3832424 prefixEnd_3832424 := by exact prefixLift 3832424
  have htrace : WordTrace (prefixWord ++ tailWord_3832424) baseStart_3832424 baseEnd_3832424 := by
    simpa [prefixWord, tailWord_3832424, baseEnd_3832424] using wordTrace_append hprefix tailTrace_3832424
  have hstable : (prefixWord ++ tailWord_3832424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3832424).length < 2 ^ (prefixWord ++ tailWord_3832424).sum := by decide
  have hdescent : baseEnd_3832424 < baseStart_3832424 := by decide
  rcases family_descends (prefixWord ++ tailWord_3832424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3832481 : List Nat := [1, 2, 3, 3, 3, 2, 1, 1, 2, 2, 3]
def baseStart_3832481 : Nat := 118140960795 + 3832481 * 2 ^ 59
def prefixEnd_3832481 : Nat := 4983230072969 + 3 ^ 40 * 3832481 * 2
def baseEnd_3832481 : Nat := 1967904852223925134162247

theorem tailTrace_3832481 : CollatzResearch.WordTrace tailWord_3832481 prefixEnd_3832481 1967904852223925134162247 := by
  unfold tailWord_3832481
  simp only [CollatzResearch.WordTrace]
  refine ⟨139782065628583347489665297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93188043752388898326443531 139782065628583347489665297)
  ·
    refine ⟨104836549221437510617248973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139782065628583347489665297 104836549221437510617248973)
    ·
      refine ⟨39313705958039066481468365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 104836549221437510617248973 39313705958039066481468365)
      ·
        refine ⟨14742639734264649930550637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39313705958039066481468365 14742639734264649930550637)
        ·
          refine ⟨5528489900349243723956489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14742639734264649930550637 5528489900349243723956489)
          ·
            refine ⟨4146367425261932792967367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5528489900349243723956489 4146367425261932792967367)
            ·
              refine ⟨6219551137892899189451051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4146367425261932792967367 6219551137892899189451051)
              ·
                refine ⟨9329326706839348784176577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6219551137892899189451051 9329326706839348784176577)
                ·
                  refine ⟨6996995030129511588132433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9329326706839348784176577 6996995030129511588132433)
                  ·
                    refine ⟨5247746272597133691099325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6996995030129511588132433 5247746272597133691099325)
                    ·
                      refine ⟨1967904852223925134162247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5247746272597133691099325 1967904852223925134162247)
                      ·
                        rfl

theorem cell23_3832481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 2, 1, 1, 2, 2, 3].length) (baseStart_3832481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3832481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3832481 prefixEnd_3832481 := by exact prefixLift 3832481
  have htrace : WordTrace (prefixWord ++ tailWord_3832481) baseStart_3832481 baseEnd_3832481 := by
    simpa [prefixWord, tailWord_3832481, baseEnd_3832481] using wordTrace_append hprefix tailTrace_3832481
  have hstable : (prefixWord ++ tailWord_3832481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3832481).length < 2 ^ (prefixWord ++ tailWord_3832481).sum := by decide
  have hdescent : baseEnd_3832481 < baseStart_3832481 := by decide
  rcases family_descends (prefixWord ++ tailWord_3832481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3832511 : List Nat := [1, 1, 2, 2, 2, 4, 2, 4, 1, 1, 3]
def baseStart_3832511 : Nat := 118140960795 + 3832511 * 2 ^ 59
def prefixEnd_3832511 : Nat := 4983230072969 + 3 ^ 40 * 3832511 * 2
def baseEnd_3832511 : Nat := 1967920256643560016787109

theorem tailTrace_3832511 : CollatzResearch.WordTrace tailWord_3832511 prefixEnd_3832511 1967920256643560016787109 := by
  unfold tailWord_3832511
  simp only [CollatzResearch.WordTrace]
  refine ⟨139783159818474662613257387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93188773212316441742171591 139783159818474662613257387)
  ·
    refine ⟨209674739727711993919886081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139783159818474662613257387 209674739727711993919886081)
    ·
      refine ⟨157256054795783995439914561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 209674739727711993919886081 157256054795783995439914561)
      ·
        refine ⟨117942041096837996579935921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 157256054795783995439914561 117942041096837996579935921)
        ·
          refine ⟨88456530822628497434951941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 117942041096837996579935921 88456530822628497434951941)
          ·
            refine ⟨16585599529242843269053489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 88456530822628497434951941 16585599529242843269053489)
            ·
              refine ⟨12439199646932132451790117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16585599529242843269053489 12439199646932132451790117)
              ·
                refine ⟨2332349933799774834710647, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12439199646932132451790117 2332349933799774834710647)
                ·
                  refine ⟨3498524900699662252065971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2332349933799774834710647 3498524900699662252065971)
                  ·
                    refine ⟨5247787351049493378098957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3498524900699662252065971 5247787351049493378098957)
                    ·
                      refine ⟨1967920256643560016787109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5247787351049493378098957 1967920256643560016787109)
                      ·
                        rfl

theorem cell23_3832511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 2, 4, 1, 1, 3].length) (baseStart_3832511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3832511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3832511 prefixEnd_3832511 := by exact prefixLift 3832511
  have htrace : WordTrace (prefixWord ++ tailWord_3832511) baseStart_3832511 baseEnd_3832511 := by
    simpa [prefixWord, tailWord_3832511, baseEnd_3832511] using wordTrace_append hprefix tailTrace_3832511
  have hstable : (prefixWord ++ tailWord_3832511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3832511).length < 2 ^ (prefixWord ++ tailWord_3832511).sum := by decide
  have hdescent : baseEnd_3832511 < baseStart_3832511 := by decide
  rcases family_descends (prefixWord ++ tailWord_3832511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3832517 : List Nat := [1, 3, 1, 1, 1, 1, 2, 1, 4, 6, 2]
def baseStart_3832517 : Nat := 118140960795 + 3832517 * 2 ^ 59
def prefixEnd_3832517 : Nat := 4983230072969 + 3 ^ 40 * 3832517 * 2
def baseEnd_3832517 : Nat := 1967923337527486993312081

theorem tailTrace_3832517 : CollatzResearch.WordTrace tailWord_3832517 prefixEnd_3832517 1967923337527486993312081 := by
  unfold tailWord_3832517
  simp only [CollatzResearch.WordTrace]
  refine ⟨139783378656452925637975805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93188919104301950425317203 139783378656452925637975805)
  ·
    refine ⟨52418766996169847114240927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 139783378656452925637975805 52418766996169847114240927)
    ·
      refine ⟨78628150494254770671361391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52418766996169847114240927 78628150494254770671361391)
      ·
        refine ⟨117942225741382156007042087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78628150494254770671361391 117942225741382156007042087)
        ·
          refine ⟨176913338612073234010563131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117942225741382156007042087 176913338612073234010563131)
          ·
            refine ⟨265370007918109851015844697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 176913338612073234010563131 265370007918109851015844697)
            ·
              refine ⟨199027505938582388261883523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 265370007918109851015844697 199027505938582388261883523)
              ·
                refine ⟨298541258907873582392825285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 199027505938582388261883523 298541258907873582392825285)
                ·
                  refine ⟨55976486045226296698654741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 298541258907873582392825285 55976486045226296698654741)
                  ·
                    refine ⟨2623897783369982657749441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 55976486045226296698654741 2623897783369982657749441)
                    ·
                      refine ⟨1967923337527486993312081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2623897783369982657749441 1967923337527486993312081)
                      ·
                        rfl

theorem cell23_3832517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 1, 4, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 1, 4, 6, 2].length) (baseStart_3832517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3832517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3832517 prefixEnd_3832517 := by exact prefixLift 3832517
  have htrace : WordTrace (prefixWord ++ tailWord_3832517) baseStart_3832517 baseEnd_3832517 := by
    simpa [prefixWord, tailWord_3832517, baseEnd_3832517] using wordTrace_append hprefix tailTrace_3832517
  have hstable : (prefixWord ++ tailWord_3832517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3832517).length < 2 ^ (prefixWord ++ tailWord_3832517).sum := by decide
  have hdescent : baseEnd_3832517 < baseStart_3832517 := by decide
  rcases family_descends (prefixWord ++ tailWord_3832517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3832574 : List Nat := [4, 2, 2, 1, 2, 2, 2, 8]
def baseStart_3832574 : Nat := 118140960795 + 3832574 * 2 ^ 59
def prefixEnd_3832574 : Nat := 4983230072969 + 3 ^ 40 * 3832574 * 2
def baseEnd_3832574 : Nat := 72887133552770121122197

theorem tailTrace_3832574 : CollatzResearch.WordTrace tailWord_3832574 prefixEnd_3832574 72887133552770121122197 := by
  unfold tailWord_3832574
  simp only [CollatzResearch.WordTrace]
  refine ⟨17473182202155803046600097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 93190305078164282915200517 17473182202155803046600097)
  ·
    refine ⟨13104886651616852284950073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17473182202155803046600097 13104886651616852284950073)
    ·
      refine ⟨9828664988712639213712555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13104886651616852284950073 9828664988712639213712555)
      ·
        refine ⟨14742997483068958820568833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9828664988712639213712555 14742997483068958820568833)
        ·
          refine ⟨11057248112301719115426625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14742997483068958820568833 11057248112301719115426625)
          ·
            refine ⟨8292936084226289336569969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11057248112301719115426625 8292936084226289336569969)
            ·
              refine ⟨6219702063169717002427477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8292936084226289336569969 6219702063169717002427477)
              ·
                refine ⟨72887133552770121122197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6219702063169717002427477 72887133552770121122197)
                ·
                  rfl

theorem cell23_3832574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 2, 2, 8].length) (baseStart_3832574 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3832574 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3832574 prefixEnd_3832574 := by exact prefixLift 3832574
  have htrace : WordTrace (prefixWord ++ tailWord_3832574) baseStart_3832574 baseEnd_3832574 := by
    simpa [prefixWord, tailWord_3832574, baseEnd_3832574] using wordTrace_append hprefix tailTrace_3832574
  have hstable : (prefixWord ++ tailWord_3832574).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3832574).length < 2 ^ (prefixWord ++ tailWord_3832574).sum := by decide
  have hdescent : baseEnd_3832574 < baseStart_3832574 := by decide
  rcases family_descends (prefixWord ++ tailWord_3832574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3832578 : List Nat := [3, 4, 1, 1, 1, 2, 4, 1, 2, 4]
def baseStart_3832578 : Nat := 118140960795 + 3832578 * 2 ^ 59
def prefixEnd_3832578 : Nat := 4983230072969 + 3 ^ 40 * 3832578 * 2
def baseEnd_3832578 : Nat := 655984886615803751549767

theorem tailTrace_3832578 : CollatzResearch.WordTrace tailWord_3832578 prefixEnd_3832578 655984886615803751549767 := by
  unfold tailWord_3832578
  simp only [CollatzResearch.WordTrace]
  refine ⟨34946400877307983263986597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93190402339487955370630925 34946400877307983263986597)
  ·
    refine ⟨6552450164495246861997487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 34946400877307983263986597 6552450164495246861997487)
    ·
      refine ⟨9828675246742870292996231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6552450164495246861997487 9828675246742870292996231)
      ·
        refine ⟨14743012870114305439494347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9828675246742870292996231 14743012870114305439494347)
        ·
          refine ⟨22114519305171458159241521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14743012870114305439494347 22114519305171458159241521)
          ·
            refine ⟨16585889478878593619431141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22114519305171458159241521 16585889478878593619431141)
            ·
              refine ⟨3109854277289736303643339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16585889478878593619431141 3109854277289736303643339)
              ·
                refine ⟨4664781415934604455465009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3109854277289736303643339 4664781415934604455465009)
                ·
                  refine ⟨3498586061950953341598757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4664781415934604455465009 3498586061950953341598757)
                  ·
                    refine ⟨655984886615803751549767, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3498586061950953341598757 655984886615803751549767)
                    ·
                      rfl

theorem cell23_3832578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 4, 1, 2, 4].length) (baseStart_3832578 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3832578 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3832578 prefixEnd_3832578 := by exact prefixLift 3832578
  have htrace : WordTrace (prefixWord ++ tailWord_3832578) baseStart_3832578 baseEnd_3832578 := by
    simpa [prefixWord, tailWord_3832578, baseEnd_3832578] using wordTrace_append hprefix tailTrace_3832578
  have hstable : (prefixWord ++ tailWord_3832578).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3832578).length < 2 ^ (prefixWord ++ tailWord_3832578).sum := by decide
  have hdescent : baseEnd_3832578 < baseStart_3832578 := by decide
  rcases family_descends (prefixWord ++ tailWord_3832578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3832605 : List Nat := [1, 4, 2, 4, 1, 1, 3, 1, 1, 2, 3]
def baseStart_3832605 : Nat := 118140960795 + 3832605 * 2 ^ 59
def prefixEnd_3832605 : Nat := 4983230072969 + 3 ^ 40 * 3832605 * 2
def baseEnd_3832605 : Nat := 1967968523825082649011677

theorem tailTrace_3832605 : CollatzResearch.WordTrace tailWord_3832605 prefixEnd_3832605 1967968523825082649011677 := by
  unfold tailWord_3832605
  simp only [CollatzResearch.WordTrace]
  refine ⟨139786588280134116667179269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93191058853422744444786179 139786588280134116667179269)
  ·
    refine ⟨26209985302525146875096113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 139786588280134116667179269 26209985302525146875096113)
    ·
      refine ⟨19657488976893860156322085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26209985302525146875096113 19657488976893860156322085)
      ·
        refine ⟨3685779183167598779310391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19657488976893860156322085 3685779183167598779310391)
        ·
          refine ⟨5528668774751398168965587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3685779183167598779310391 5528668774751398168965587)
          ·
            refine ⟨8293003162127097253448381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5528668774751398168965587 8293003162127097253448381)
            ·
              refine ⟨3109876185797661470043143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8293003162127097253448381 3109876185797661470043143)
              ·
                refine ⟨4664814278696492205064715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3109876185797661470043143 4664814278696492205064715)
                ·
                  refine ⟨6997221418044738307597073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4664814278696492205064715 6997221418044738307597073)
                  ·
                    refine ⟨5247916063533553730697805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6997221418044738307597073 5247916063533553730697805)
                    ·
                      refine ⟨1967968523825082649011677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5247916063533553730697805 1967968523825082649011677)
                      ·
                        rfl

theorem cell23_3832605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 1, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 1, 3, 1, 1, 2, 3].length) (baseStart_3832605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3832605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3832605 prefixEnd_3832605 := by exact prefixLift 3832605
  have htrace : WordTrace (prefixWord ++ tailWord_3832605) baseStart_3832605 baseEnd_3832605 := by
    simpa [prefixWord, tailWord_3832605, baseEnd_3832605] using wordTrace_append hprefix tailTrace_3832605
  have hstable : (prefixWord ++ tailWord_3832605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3832605).length < 2 ^ (prefixWord ++ tailWord_3832605).sum := by decide
  have hdescent : baseEnd_3832605 < baseStart_3832605 := by decide
  rcases family_descends (prefixWord ++ tailWord_3832605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3832634 : List Nat := [3, 1, 1, 1, 6, 1, 1, 1, 2, 6]
def baseStart_3832634 : Nat := 118140960795 + 3832634 * 2 ^ 59
def prefixEnd_3832634 : Nat := 4983230072969 + 3 ^ 40 * 3832634 * 2
def baseEnd_3832634 : Nat := 655994471588021011849681

theorem tailTrace_3832634 : CollatzResearch.WordTrace tailWord_3832634 prefixEnd_3832634 655994471588021011849681 := by
  unfold tailWord_3832634
  simp only [CollatzResearch.WordTrace]
  refine ⟨34946911499257263654996239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93191763998019369746656637 34946911499257263654996239)
  ·
    refine ⟨52420367248885895482494359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34946911499257263654996239 52420367248885895482494359)
    ·
      refine ⟨78630550873328843223741539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52420367248885895482494359 78630550873328843223741539)
      ·
        refine ⟨117945826309993264835612309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78630550873328843223741539 117945826309993264835612309)
        ·
          refine ⟨5528710608280934289169327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 117945826309993264835612309 5528710608280934289169327)
          ·
            refine ⟨8293065912421401433753991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5528710608280934289169327 8293065912421401433753991)
            ·
              refine ⟨12439598868632102150630987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8293065912421401433753991 12439598868632102150630987)
              ·
                refine ⟨18659398302948153225946481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12439598868632102150630987 18659398302948153225946481)
                ·
                  refine ⟨13994548727211114919459861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18659398302948153225946481 13994548727211114919459861)
                  ·
                    refine ⟨655994471588021011849681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13994548727211114919459861 655994471588021011849681)
                    ·
                      rfl

theorem cell23_3832634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 1, 1, 1, 2, 6].length) (baseStart_3832634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3832634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3832634 prefixEnd_3832634 := by exact prefixLift 3832634
  have htrace : WordTrace (prefixWord ++ tailWord_3832634) baseStart_3832634 baseEnd_3832634 := by
    simpa [prefixWord, tailWord_3832634, baseEnd_3832634] using wordTrace_append hprefix tailTrace_3832634
  have hstable : (prefixWord ++ tailWord_3832634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3832634).length < 2 ^ (prefixWord ++ tailWord_3832634).sum := by decide
  have hdescent : baseEnd_3832634 < baseStart_3832634 := by decide
  rcases family_descends (prefixWord ++ tailWord_3832634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3832675 : List Nat := [1, 1, 1, 5, 3, 3, 1, 2, 2, 2, 2]
def baseStart_3832675 : Nat := 118140960795 + 3832675 * 2 ^ 59
def prefixEnd_3832675 : Nat := 4983230072969 + 3 ^ 40 * 3832675 * 2
def baseEnd_3832675 : Nat := 1968004467470897375136355

theorem tailTrace_3832675 : CollatzResearch.WordTrace tailWord_3832675 prefixEnd_3832675 1968004467470897375136355 := by
  unfold tailWord_3832675
  simp only [CollatzResearch.WordTrace]
  refine ⟨139789141389880518622227479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93192760926587012414818319 139789141389880518622227479)
  ·
    refine ⟨209683712084820777933341219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139789141389880518622227479 209683712084820777933341219)
    ·
      refine ⟨314525568127231166900011829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209683712084820777933341219 314525568127231166900011829)
      ·
        refine ⟨29486772011927921896876109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 314525568127231166900011829 29486772011927921896876109)
        ·
          refine ⟨11057539504472970711328541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29486772011927921896876109 11057539504472970711328541)
          ·
            refine ⟨4146577314177364016748203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11057539504472970711328541 4146577314177364016748203)
            ·
              refine ⟨6219865971266046025122305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4146577314177364016748203 6219865971266046025122305)
              ·
                refine ⟨4664899478449534518841729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6219865971266046025122305 4664899478449534518841729)
                ·
                  refine ⟨3498674608837150889131297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4664899478449534518841729 3498674608837150889131297)
                  ·
                    refine ⟨2624005956627863166848473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3498674608837150889131297 2624005956627863166848473)
                    ·
                      refine ⟨1968004467470897375136355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2624005956627863166848473 1968004467470897375136355)
                      ·
                        rfl

theorem cell23_3832675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 3, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 3, 1, 2, 2, 2, 2].length) (baseStart_3832675 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3832675 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3832675 prefixEnd_3832675 := by exact prefixLift 3832675
  have htrace : WordTrace (prefixWord ++ tailWord_3832675) baseStart_3832675 baseEnd_3832675 := by
    simpa [prefixWord, tailWord_3832675, baseEnd_3832675] using wordTrace_append hprefix tailTrace_3832675
  have hstable : (prefixWord ++ tailWord_3832675).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3832675).length < 2 ^ (prefixWord ++ tailWord_3832675).sum := by decide
  have hdescent : baseEnd_3832675 < baseStart_3832675 := by decide
  rcases family_descends (prefixWord ++ tailWord_3832675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3832687 : List Nat := [1, 1, 2, 1, 3, 1, 1, 5, 1, 2, 5]
def baseStart_3832687 : Nat := 118140960795 + 3832687 * 2 ^ 59
def prefixEnd_3832687 : Nat := 4983230072969 + 3 ^ 40 * 3832687 * 2
def baseEnd_3832687 : Nat := 1968010629238751328186299

theorem tailTrace_3832687 : CollatzResearch.WordTrace tailWord_3832687 prefixEnd_3832687 1968010629238751328186299 := by
  unfold tailWord_3832687
  simp only [CollatzResearch.WordTrace]
  refine ⟨139789579065837044671664315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93193052710558029781109543 139789579065837044671664315)
  ·
    refine ⟨209684368598755567007496473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139789579065837044671664315 209684368598755567007496473)
    ·
      refine ⟨157263276449066675255622355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 209684368598755567007496473 157263276449066675255622355)
      ·
        refine ⟨235894914673600012883433533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157263276449066675255622355 235894914673600012883433533)
        ·
          refine ⟨88460593002600004831287575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 235894914673600012883433533 88460593002600004831287575)
          ·
            refine ⟨132690889503900007246931363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88460593002600004831287575 132690889503900007246931363)
            ·
              refine ⟨199036334255850010870397045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 132690889503900007246931363 199036334255850010870397045)
              ·
                refine ⟨18659656336485938519099723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 199036334255850010870397045 18659656336485938519099723)
                ·
                  refine ⟨27989484504728907778649585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18659656336485938519099723 27989484504728907778649585)
                  ·
                    refine ⟨20992113378546680833987189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27989484504728907778649585 20992113378546680833987189)
                    ·
                      refine ⟨1968010629238751328186299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20992113378546680833987189 1968010629238751328186299)
                      ·
                        rfl

theorem cell23_3832687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 5, 1, 2, 5].length) (baseStart_3832687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3832687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3832687 prefixEnd_3832687 := by exact prefixLift 3832687
  have htrace : WordTrace (prefixWord ++ tailWord_3832687) baseStart_3832687 baseEnd_3832687 := by
    simpa [prefixWord, tailWord_3832687, baseEnd_3832687] using wordTrace_append hprefix tailTrace_3832687
  have hstable : (prefixWord ++ tailWord_3832687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3832687).length < 2 ^ (prefixWord ++ tailWord_3832687).sum := by decide
  have hdescent : baseEnd_3832687 < baseStart_3832687 := by decide
  rcases family_descends (prefixWord ++ tailWord_3832687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3832707 : List Nat := [1, 1, 1, 3, 4, 1, 1, 1, 2, 8]
def baseStart_3832707 : Nat := 118140960795 + 3832707 * 2 ^ 59
def prefixEnd_3832707 : Nat := 4983230072969 + 3 ^ 40 * 3832707 * 2
def baseEnd_3832707 : Nat := 656006966283947083312069

theorem tailTrace_3832707 : CollatzResearch.WordTrace tailWord_3832707 prefixEnd_3832707 656006966283947083312069 := by
  unfold tailWord_3832707
  simp only [CollatzResearch.WordTrace]
  refine ⟨139790308525764588087392375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93193539017176392058261583 139790308525764588087392375)
  ·
    refine ⟨209685462788646882131088563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139790308525764588087392375 209685462788646882131088563)
    ·
      refine ⟨314528194182970323196632845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209685462788646882131088563 314528194182970323196632845)
      ·
        refine ⟨117948072818613871198737317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 314528194182970323196632845 117948072818613871198737317)
        ·
          refine ⟨22115263653490100849763247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 117948072818613871198737317 22115263653490100849763247)
          ·
            refine ⟨33172895480235151274644871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22115263653490100849763247 33172895480235151274644871)
            ·
              refine ⟨49759343220352726911967307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33172895480235151274644871 49759343220352726911967307)
              ·
                refine ⟨74639014830529090367950961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49759343220352726911967307 74639014830529090367950961)
                ·
                  refine ⟨55979261122896817775963221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 74639014830529090367950961 55979261122896817775963221)
                  ·
                    refine ⟨656006966283947083312069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 55979261122896817775963221 656006966283947083312069)
                    ·
                      rfl

theorem cell23_3832707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 1, 1, 2, 8].length) (baseStart_3832707 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3832707 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3832707 prefixEnd_3832707 := by exact prefixLift 3832707
  have htrace : WordTrace (prefixWord ++ tailWord_3832707) baseStart_3832707 baseEnd_3832707 := by
    simpa [prefixWord, tailWord_3832707, baseEnd_3832707] using wordTrace_append hprefix tailTrace_3832707
  have hstable : (prefixWord ++ tailWord_3832707).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3832707).length < 2 ^ (prefixWord ++ tailWord_3832707).sum := by decide
  have hdescent : baseEnd_3832707 < baseStart_3832707 := by decide
  rcases family_descends (prefixWord ++ tailWord_3832707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3832791 : List Nat := [1, 1, 3, 2, 1, 1, 2, 3, 4, 3, 2]
def baseStart_3832791 : Nat := 118140960795 + 3832791 * 2 ^ 59
def prefixEnd_3832791 : Nat := 4983230072969 + 3 ^ 40 * 3832791 * 2
def baseEnd_3832791 : Nat := 1968064031226818921285821

theorem tailTrace_3832791 : CollatzResearch.WordTrace tailWord_3832791 prefixEnd_3832791 1968064031226818921285821 := by
  unfold tailWord_3832791
  simp only [CollatzResearch.WordTrace]
  refine ⟨139793372257460270433450227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93195581504973513622300151 139793372257460270433450227)
  ·
    refine ⟨209690058386190405650175341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139793372257460270433450227 209690058386190405650175341)
    ·
      refine ⟨78633771894821402118815753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 209690058386190405650175341 78633771894821402118815753)
      ·
        refine ⟨58975328921116051589111815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78633771894821402118815753 58975328921116051589111815)
        ·
          refine ⟨88462993381674077383667723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58975328921116051589111815 88462993381674077383667723)
          ·
            refine ⟨132694490072511116075501585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88462993381674077383667723 132694490072511116075501585)
            ·
              refine ⟨99520867554383337056626189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 132694490072511116075501585 99520867554383337056626189)
              ·
                refine ⟨37320325332893751396234821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 99520867554383337056626189 37320325332893751396234821)
                ·
                  refine ⟨6997560999917578386794029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37320325332893751396234821 6997560999917578386794029)
                  ·
                    refine ⟨2624085374969091895047761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6997560999917578386794029 2624085374969091895047761)
                    ·
                      refine ⟨1968064031226818921285821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2624085374969091895047761 1968064031226818921285821)
                      ·
                        rfl

theorem cell23_3832791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 3, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 3, 4, 3, 2].length) (baseStart_3832791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3832791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3832791 prefixEnd_3832791 := by exact prefixLift 3832791
  have htrace : WordTrace (prefixWord ++ tailWord_3832791) baseStart_3832791 baseEnd_3832791 := by
    simpa [prefixWord, tailWord_3832791, baseEnd_3832791] using wordTrace_append hprefix tailTrace_3832791
  have hstable : (prefixWord ++ tailWord_3832791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3832791).length < 2 ^ (prefixWord ++ tailWord_3832791).sum := by decide
  have hdescent : baseEnd_3832791 < baseStart_3832791 := by decide
  rcases family_descends (prefixWord ++ tailWord_3832791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3832844 : List Nat := [2, 2, 1, 2, 3, 3, 10]
def baseStart_3832844 : Nat := 118140960795 + 3832844 * 2 ^ 59
def prefixEnd_3832844 : Nat := 4983230072969 + 3 ^ 40 * 3832844 * 2
def baseEnd_3832844 : Nat := 24297422786438360665717

theorem tailTrace_3832844 : CollatzResearch.WordTrace tailWord_3832844 prefixEnd_3832844 24297422786438360665717 := by
  unfold tailWord_3832844
  simp only [CollatzResearch.WordTrace]
  refine ⟨69897652663134130242564793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93196870217512173656753057 69897652663134130242564793)
  ·
    refine ⟨52423239497350597681923595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69897652663134130242564793 52423239497350597681923595)
    ·
      refine ⟨78634859246025896522885393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52423239497350597681923595 78634859246025896522885393)
      ·
        refine ⟨58976144434519422392164045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78634859246025896522885393 58976144434519422392164045)
        ·
          refine ⟨22116054162944783397061517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58976144434519422392164045 22116054162944783397061517)
          ·
            refine ⟨8293520311104293773898069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22116054162944783397061517 8293520311104293773898069)
            ·
              refine ⟨24297422786438360665717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 8293520311104293773898069 24297422786438360665717)
              ·
                rfl

theorem cell23_3832844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 3, 10].length) (baseStart_3832844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3832844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3832844 prefixEnd_3832844 := by exact prefixLift 3832844
  have htrace : WordTrace (prefixWord ++ tailWord_3832844) baseStart_3832844 baseEnd_3832844 := by
    simpa [prefixWord, tailWord_3832844, baseEnd_3832844] using wordTrace_append hprefix tailTrace_3832844
  have hstable : (prefixWord ++ tailWord_3832844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3832844).length < 2 ^ (prefixWord ++ tailWord_3832844).sum := by decide
  have hdescent : baseEnd_3832844 < baseStart_3832844 := by decide
  rcases family_descends (prefixWord ++ tailWord_3832844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3832855 : List Nat := [1, 1, 3, 5, 1, 1, 1, 3, 3, 2, 2]
def baseStart_3832855 : Nat := 118140960795 + 3832855 * 2 ^ 59
def prefixEnd_3832855 : Nat := 4983230072969 + 3 ^ 40 * 3832855 * 2
def baseEnd_3832855 : Nat := 1968096893988706670885527

theorem tailTrace_3832855 : CollatzResearch.WordTrace tailWord_3832855 prefixEnd_3832855 1968096893988706670885527 := by
  unfold tailWord_3832855
  simp only [CollatzResearch.WordTrace]
  refine ⟨139795706529228409363780019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93197137686152272909186679 139795706529228409363780019)
  ·
    refine ⟨209693559793842614045670029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139795706529228409363780019 209693559793842614045670029)
    ·
      refine ⟨78635084922690980267126261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 209693559793842614045670029 78635084922690980267126261)
      ·
        refine ⟨7372039211502279400043087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 78635084922690980267126261 7372039211502279400043087)
        ·
          refine ⟨11058058817253419100064631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7372039211502279400043087 11058058817253419100064631)
          ·
            refine ⟨16587088225880128650096947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11058058817253419100064631 16587088225880128650096947)
            ·
              refine ⟨24880632338820192975145421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16587088225880128650096947 24880632338820192975145421)
              ·
                refine ⟨9330237127057572365679533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24880632338820192975145421 9330237127057572365679533)
                ·
                  refine ⟨3498838922646589637129825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9330237127057572365679533 3498838922646589637129825)
                  ·
                    refine ⟨2624129191984942227847369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3498838922646589637129825 2624129191984942227847369)
                    ·
                      refine ⟨1968096893988706670885527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2624129191984942227847369 1968096893988706670885527)
                      ·
                        rfl

theorem cell23_3832855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 1, 3, 3, 2, 2].length) (baseStart_3832855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3832855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3832855 prefixEnd_3832855 := by exact prefixLift 3832855
  have htrace : WordTrace (prefixWord ++ tailWord_3832855) baseStart_3832855 baseEnd_3832855 := by
    simpa [prefixWord, tailWord_3832855, baseEnd_3832855] using wordTrace_append hprefix tailTrace_3832855
  have hstable : (prefixWord ++ tailWord_3832855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3832855).length < 2 ^ (prefixWord ++ tailWord_3832855).sum := by decide
  have hdescent : baseEnd_3832855 < baseStart_3832855 := by decide
  rcases family_descends (prefixWord ++ tailWord_3832855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3832865 : List Nat := [1, 2, 3, 2, 3, 2, 3, 1, 2, 4]
def baseStart_3832865 : Nat := 118140960795 + 3832865 * 2 ^ 59
def prefixEnd_3832865 : Nat := 4983230072969 + 3 ^ 40 * 3832865 * 2
def baseEnd_3832865 : Nat := 656034009598417210586827

theorem tailTrace_3832865 : CollatzResearch.WordTrace tailWord_3832865 prefixEnd_3832865 656034009598417210586827 := by
  unfold tailWord_3832865
  simp only [CollatzResearch.WordTrace]
  refine ⟨139796071259192181071644049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93197380839461454047762699 139796071259192181071644049)
  ·
    refine ⟨104847053444394135803733037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139796071259192181071644049 104847053444394135803733037)
    ·
      refine ⟨39317645041647800926399889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 104847053444394135803733037 39317645041647800926399889)
      ·
        refine ⟨29488233781235850694799917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39317645041647800926399889 29488233781235850694799917)
        ·
          refine ⟨11058087667963444010549969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29488233781235850694799917 11058087667963444010549969)
          ·
            refine ⟨8293565750972583007912477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11058087667963444010549969 8293565750972583007912477)
            ·
              refine ⟨3110087156614718627967179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8293565750972583007912477 3110087156614718627967179)
              ·
                refine ⟨4665130734922077941950769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3110087156614718627967179 4665130734922077941950769)
                ·
                  refine ⟨3498848051191558456463077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4665130734922077941950769 3498848051191558456463077)
                  ·
                    refine ⟨656034009598417210586827, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3498848051191558456463077 656034009598417210586827)
                    ·
                      rfl

theorem cell23_3832865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 2, 3, 1, 2, 4].length) (baseStart_3832865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3832865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3832865 prefixEnd_3832865 := by exact prefixLift 3832865
  have htrace : WordTrace (prefixWord ++ tailWord_3832865) baseStart_3832865 baseEnd_3832865 := by
    simpa [prefixWord, tailWord_3832865, baseEnd_3832865] using wordTrace_append hprefix tailTrace_3832865
  have hstable : (prefixWord ++ tailWord_3832865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3832865).length < 2 ^ (prefixWord ++ tailWord_3832865).sum := by decide
  have hdescent : baseEnd_3832865 < baseStart_3832865 := by decide
  rcases family_descends (prefixWord ++ tailWord_3832865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3832868 : List Nat := [2, 3, 1, 4, 1, 1, 3, 1, 1, 2, 4]
def baseStart_3832868 : Nat := 118140960795 + 3832868 * 2 ^ 59
def prefixEnd_3832868 : Nat := 4983230072969 + 3 ^ 40 * 3832868 * 2
def baseEnd_3832868 : Nat := 1968103569237215120022967

theorem tailTrace_3832868 : CollatzResearch.WordTrace tailWord_3832868 prefixEnd_3832868 1968103569237215120022967 := by
  unfold tailWord_3832868
  simp only [CollatzResearch.WordTrace]
  refine ⟨69898090339090656292001629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93197453785454208389335505 69898090339090656292001629)
  ·
    refine ⟨26211783877158996109500611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69898090339090656292001629 26211783877158996109500611)
    ·
      refine ⟨39317675815738494164250917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26211783877158996109500611 39317675815738494164250917)
      ·
        refine ⟨7372064215450967655797047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 39317675815738494164250917 7372064215450967655797047)
        ·
          refine ⟨11058096323176451483695571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7372064215450967655797047 11058096323176451483695571)
          ·
            refine ⟨16587144484764677225543357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11058096323176451483695571 16587144484764677225543357)
            ·
              refine ⟨6220179181786753959578759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16587144484764677225543357 6220179181786753959578759)
              ·
                refine ⟨9330268772680130939368139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6220179181786753959578759 9330268772680130939368139)
                ·
                  refine ⟨13995403159020196409052209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9330268772680130939368139 13995403159020196409052209)
                  ·
                    refine ⟨10496552369265147306789157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13995403159020196409052209 10496552369265147306789157)
                    ·
                      refine ⟨1968103569237215120022967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10496552369265147306789157 1968103569237215120022967)
                      ·
                        rfl

theorem cell23_3832868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 3, 1, 1, 2, 4].length) (baseStart_3832868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3832868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3832868 prefixEnd_3832868 := by exact prefixLift 3832868
  have htrace : WordTrace (prefixWord ++ tailWord_3832868) baseStart_3832868 baseEnd_3832868 := by
    simpa [prefixWord, tailWord_3832868, baseEnd_3832868] using wordTrace_append hprefix tailTrace_3832868
  have hstable : (prefixWord ++ tailWord_3832868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3832868).length < 2 ^ (prefixWord ++ tailWord_3832868).sum := by decide
  have hdescent : baseEnd_3832868 < baseStart_3832868 := by decide
  rcases family_descends (prefixWord ++ tailWord_3832868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3832888 : List Nat := [2, 1, 2, 1, 5, 1, 1, 2, 4, 1, 3]
def baseStart_3832888 : Nat := 118140960795 + 3832888 * 2 ^ 59
def prefixEnd_3832888 : Nat := 4983230072969 + 3 ^ 40 * 3832888 * 2
def baseEnd_3832888 : Nat := 1968113838850305041772875

theorem tailTrace_3832888 : CollatzResearch.WordTrace tailWord_3832888 prefixEnd_3832888 1968113838850305041772875 := by
  unfold tailWord_3832888
  simp only [CollatzResearch.WordTrace]
  refine ⟨69898455069054427999865659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93197940092072570666487545 69898455069054427999865659)
  ·
    refine ⟨104847682603581641999798489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69898455069054427999865659 104847682603581641999798489)
    ·
      refine ⟨78635761952686231499848867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104847682603581641999798489 78635761952686231499848867)
      ·
        refine ⟨117953642929029347249773301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78635761952686231499848867 117953642929029347249773301)
        ·
          refine ⟨11058154024596501304666247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 117953642929029347249773301 11058154024596501304666247)
          ·
            refine ⟨16587231036894751956999371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11058154024596501304666247 16587231036894751956999371)
            ·
              refine ⟨24880846555342127935499057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16587231036894751956999371 24880846555342127935499057)
              ·
                refine ⟨18660634916506595951624293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24880846555342127935499057 18660634916506595951624293)
                ·
                  refine ⟨3498869046844986740929555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18660634916506595951624293 3498869046844986740929555)
                  ·
                    refine ⟨5248303570267480111394333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3498869046844986740929555 5248303570267480111394333)
                    ·
                      refine ⟨1968113838850305041772875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5248303570267480111394333 1968113838850305041772875)
                      ·
                        rfl

theorem cell23_3832888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 1, 2, 4, 1, 3].length) (baseStart_3832888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3832888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3832888 prefixEnd_3832888 := by exact prefixLift 3832888
  have htrace : WordTrace (prefixWord ++ tailWord_3832888) baseStart_3832888 baseEnd_3832888 := by
    simpa [prefixWord, tailWord_3832888, baseEnd_3832888] using wordTrace_append hprefix tailTrace_3832888
  have hstable : (prefixWord ++ tailWord_3832888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3832888).length < 2 ^ (prefixWord ++ tailWord_3832888).sum := by decide
  have hdescent : baseEnd_3832888 < baseStart_3832888 := by decide
  rcases family_descends (prefixWord ++ tailWord_3832888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3832889 : List Nat := [1, 2, 1, 5, 2, 3, 1, 3, 1, 2, 2]
def baseStart_3832889 : Nat := 118140960795 + 3832889 * 2 ^ 59
def prefixEnd_3832889 : Nat := 4983230072969 + 3 ^ 40 * 3832889 * 2
def baseEnd_3832889 : Nat := 1968114352330959537860371

theorem tailTrace_3832889 : CollatzResearch.WordTrace tailWord_3832889 prefixEnd_3832889 1968114352330959537860371 := by
  unfold tailWord_3832889
  simp only [CollatzResearch.WordTrace]
  refine ⟨139796946611105233170517721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93197964407403488780345147 139796946611105233170517721)
  ·
    refine ⟨104847709958328924877888291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139796946611105233170517721 104847709958328924877888291)
    ·
      refine ⟨157271564937493387316832437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104847709958328924877888291 157271564937493387316832437)
      ·
        refine ⟨14744209212890005060953041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 157271564937493387316832437 14744209212890005060953041)
        ·
          refine ⟨11058156909667503795714781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14744209212890005060953041 11058156909667503795714781)
          ·
            refine ⟨4146808841125313923393043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11058156909667503795714781 4146808841125313923393043)
            ·
              refine ⟨6220213261687970885089565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4146808841125313923393043 6220213261687970885089565)
              ·
                refine ⟨2332579973132989081908587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6220213261687970885089565 2332579973132989081908587)
                ·
                  refine ⟨3498869959699483622862881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2332579973132989081908587 3498869959699483622862881)
                  ·
                    refine ⟨2624152469774612717147161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3498869959699483622862881 2624152469774612717147161)
                    ·
                      refine ⟨1968114352330959537860371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2624152469774612717147161 1968114352330959537860371)
                      ·
                        rfl

theorem cell23_3832889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 3, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 3, 1, 3, 1, 2, 2].length) (baseStart_3832889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3832889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3832889 prefixEnd_3832889 := by exact prefixLift 3832889
  have htrace : WordTrace (prefixWord ++ tailWord_3832889) baseStart_3832889 baseEnd_3832889 := by
    simpa [prefixWord, tailWord_3832889, baseEnd_3832889] using wordTrace_append hprefix tailTrace_3832889
  have hstable : (prefixWord ++ tailWord_3832889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3832889).length < 2 ^ (prefixWord ++ tailWord_3832889).sum := by decide
  have hdescent : baseEnd_3832889 < baseStart_3832889 := by decide
  rcases family_descends (prefixWord ++ tailWord_3832889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3832911 : List Nat := [1, 1, 2, 1, 1, 2, 2, 1, 2, 8, 2]
def baseStart_3832911 : Nat := 118140960795 + 3832911 * 2 ^ 59
def prefixEnd_3832911 : Nat := 4983230072969 + 3 ^ 40 * 3832911 * 2
def baseEnd_3832911 : Nat := 1968125648905358451785269

theorem tailTrace_3832911 : CollatzResearch.WordTrace tailWord_3832911 prefixEnd_3832911 1968125648905358451785269 := by
  unfold tailWord_3832911
  simp only [CollatzResearch.WordTrace]
  refine ⟨139797749017025530927818587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93198499344683687285212391 139797749017025530927818587)
  ·
    refine ⟨209696623525538296391727881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139797749017025530927818587 209696623525538296391727881)
    ·
      refine ⟨157272467644153722293795911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 209696623525538296391727881 157272467644153722293795911)
      ·
        refine ⟨235908701466230583440693867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157272467644153722293795911 235908701466230583440693867)
        ·
          refine ⟨353863052199345875161040801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 235908701466230583440693867 353863052199345875161040801)
          ·
            refine ⟨265397289149509406370780601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 353863052199345875161040801 265397289149509406370780601)
            ·
              refine ⟨199047966862132054778085451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 265397289149509406370780601 199047966862132054778085451)
              ·
                refine ⟨298571950293198082167128177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 199047966862132054778085451 298571950293198082167128177)
                ·
                  refine ⟨223928962719898561625346133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 298571950293198082167128177 223928962719898561625346133)
                  ·
                    refine ⟨2624167531873811269047025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 223928962719898561625346133 2624167531873811269047025)
                    ·
                      refine ⟨1968125648905358451785269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2624167531873811269047025 1968125648905358451785269)
                      ·
                        rfl

theorem cell23_3832911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 1, 2, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 1, 2, 8, 2].length) (baseStart_3832911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3832911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3832911 prefixEnd_3832911 := by exact prefixLift 3832911
  have htrace : WordTrace (prefixWord ++ tailWord_3832911) baseStart_3832911 baseEnd_3832911 := by
    simpa [prefixWord, tailWord_3832911, baseEnd_3832911] using wordTrace_append hprefix tailTrace_3832911
  have hstable : (prefixWord ++ tailWord_3832911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3832911).length < 2 ^ (prefixWord ++ tailWord_3832911).sum := by decide
  have hdescent : baseEnd_3832911 < baseStart_3832911 := by decide
  rcases family_descends (prefixWord ++ tailWord_3832911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3832928 : List Nat := [2, 1, 1, 3, 2, 2, 2, 3, 1, 4, 2]
def baseStart_3832928 : Nat := 118140960795 + 3832928 * 2 ^ 59
def prefixEnd_3832928 : Nat := 4983230072969 + 3 ^ 40 * 3832928 * 2
def baseEnd_3832928 : Nat := 1968134378076484885272691

theorem tailTrace_3832928 : CollatzResearch.WordTrace tailWord_3832928 prefixEnd_3832928 1968134378076484885272691 := by
  unfold tailWord_3832928
  simp only [CollatzResearch.WordTrace]
  refine ⟨69899184528981971415593719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93198912705309295220791625 69899184528981971415593719)
  ·
    refine ⟨104848776793472957123390579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69899184528981971415593719 104848776793472957123390579)
    ·
      refine ⟨157273165190209435685085869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104848776793472957123390579 157273165190209435685085869)
      ·
        refine ⟨58977436946328538381907201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 157273165190209435685085869 58977436946328538381907201)
        ·
          refine ⟨44233077709746403786430401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58977436946328538381907201 44233077709746403786430401)
          ·
            refine ⟨33174808282309802839822801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44233077709746403786430401 33174808282309802839822801)
            ·
              refine ⟨24881106211732352129867101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33174808282309802839822801 24881106211732352129867101)
              ·
                refine ⟨9330414829399632048700163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24881106211732352129867101 9330414829399632048700163)
                ·
                  refine ⟨13995622244099448073050245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9330414829399632048700163 13995622244099448073050245)
                  ·
                    refine ⟨2624179170768646513696921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13995622244099448073050245 2624179170768646513696921)
                    ·
                      refine ⟨1968134378076484885272691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2624179170768646513696921 1968134378076484885272691)
                      ·
                        rfl

theorem cell23_3832928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 2, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 2, 3, 1, 4, 2].length) (baseStart_3832928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3832928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3832928 prefixEnd_3832928 := by exact prefixLift 3832928
  have htrace : WordTrace (prefixWord ++ tailWord_3832928) baseStart_3832928 baseEnd_3832928 := by
    simpa [prefixWord, tailWord_3832928, baseEnd_3832928] using wordTrace_append hprefix tailTrace_3832928
  have hstable : (prefixWord ++ tailWord_3832928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3832928).length < 2 ^ (prefixWord ++ tailWord_3832928).sum := by decide
  have hdescent : baseEnd_3832928 < baseStart_3832928 := by decide
  rcases family_descends (prefixWord ++ tailWord_3832928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3832978 : List Nat := [3, 2, 3, 1, 1, 2, 1, 1, 1, 5, 3]
def baseStart_3832978 : Nat := 118140960795 + 3832978 * 2 ^ 59
def prefixEnd_3832978 : Nat := 4983230072969 + 3 ^ 40 * 3832978 * 2
def baseEnd_3832978 : Nat := 1968160052109209689647461

theorem tailTrace_3832978 : CollatzResearch.WordTrace tailWord_3832978 prefixEnd_3832978 1968160052109209689647461 := by
  unfold tailWord_3832978
  simp only [CollatzResearch.WordTrace]
  refine ⟨34950048176945700342626897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93200128471855200913671725 34950048176945700342626897)
  ·
    refine ⟨26212536132709275256970173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34950048176945700342626897 26212536132709275256970173)
    ·
      refine ⟨9829701049765978221363815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26212536132709275256970173 9829701049765978221363815)
      ·
        refine ⟨14744551574648967332045723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9829701049765978221363815 14744551574648967332045723)
        ·
          refine ⟨22116827361973450998068585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14744551574648967332045723 22116827361973450998068585)
          ·
            refine ⟨16587620521480088248551439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22116827361973450998068585 16587620521480088248551439)
            ·
              refine ⟨24881430782220132372827159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16587620521480088248551439 24881430782220132372827159)
              ·
                refine ⟨37322146173330198559240739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24881430782220132372827159 37322146173330198559240739)
                ·
                  refine ⟨55983219259995297838861109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37322146173330198559240739 55983219259995297838861109)
                  ·
                    refine ⟨5248426805624559172393229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 55983219259995297838861109 5248426805624559172393229)
                    ·
                      refine ⟨1968160052109209689647461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5248426805624559172393229 1968160052109209689647461)
                      ·
                        rfl

theorem cell23_3832978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 1, 1, 1, 5, 3].length) (baseStart_3832978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3832978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3832978 prefixEnd_3832978 := by exact prefixLift 3832978
  have htrace : WordTrace (prefixWord ++ tailWord_3832978) baseStart_3832978 baseEnd_3832978 := by
    simpa [prefixWord, tailWord_3832978, baseEnd_3832978] using wordTrace_append hprefix tailTrace_3832978
  have hstable : (prefixWord ++ tailWord_3832978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3832978).length < 2 ^ (prefixWord ++ tailWord_3832978).sum := by decide
  have hdescent : baseEnd_3832978 < baseStart_3832978 := by decide
  rcases family_descends (prefixWord ++ tailWord_3832978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3833001 : List Nat := [1, 2, 1, 1, 1, 1, 2, 1, 8, 1, 4]
def baseStart_3833001 : Nat := 118140960795 + 3833001 * 2 ^ 59
def prefixEnd_3833001 : Nat := 4983230072969 + 3 ^ 40 * 3833001 * 2
def baseEnd_3833001 : Nat := 1968171862164263099659855

theorem tailTrace_3833001 : CollatzResearch.WordTrace tailWord_3833001 prefixEnd_3833001 1968171862164263099659855 := by
  unfold tailWord_3833001
  simp only [CollatzResearch.WordTrace]
  refine ⟨139801031586699476298594857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93200687724466317532396571 139801031586699476298594857)
  ·
    refine ⟨104850773690024607223946143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139801031586699476298594857 104850773690024607223946143)
    ·
      refine ⟨157276160535036910835919215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104850773690024607223946143 157276160535036910835919215)
      ·
        refine ⟨235914240802555366253878823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157276160535036910835919215 235914240802555366253878823)
        ·
          refine ⟨353871361203833049380818235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 235914240802555366253878823 353871361203833049380818235)
          ·
            refine ⟨530807041805749574071227353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 353871361203833049380818235 530807041805749574071227353)
            ·
              refine ⟨398105281354312180553420515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 530807041805749574071227353 398105281354312180553420515)
              ·
                refine ⟨597157922031468270830130773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 398105281354312180553420515 597157922031468270830130773)
                ·
                  refine ⟨6997944398806268798790595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 597157922031468270830130773 6997944398806268798790595)
                  ·
                    refine ⟨10496916598209403198185893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6997944398806268798790595 10496916598209403198185893)
                    ·
                      refine ⟨1968171862164263099659855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10496916598209403198185893 1968171862164263099659855)
                      ·
                        rfl

theorem cell23_3833001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 1, 8, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 1, 8, 1, 4].length) (baseStart_3833001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3833001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3833001 prefixEnd_3833001 := by exact prefixLift 3833001
  have htrace : WordTrace (prefixWord ++ tailWord_3833001) baseStart_3833001 baseEnd_3833001 := by
    simpa [prefixWord, tailWord_3833001, baseEnd_3833001] using wordTrace_append hprefix tailTrace_3833001
  have hstable : (prefixWord ++ tailWord_3833001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3833001).length < 2 ^ (prefixWord ++ tailWord_3833001).sum := by decide
  have hdescent : baseEnd_3833001 < baseStart_3833001 := by decide
  rcases family_descends (prefixWord ++ tailWord_3833001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3833002 : List Nat := [3, 1, 5, 1, 1, 2, 2, 3, 5]
def baseStart_3833002 : Nat := 118140960795 + 3833002 * 2 ^ 59
def prefixEnd_3833002 : Nat := 4983230072969 + 3 ^ 40 * 3833002 * 2
def baseEnd_3833002 : Nat := 218685819516101955083039

theorem tailTrace_3833002 : CollatzResearch.WordTrace tailWord_3833002 prefixEnd_3833002 218685819516101955083039 := by
  unfold tailWord_3833002
  simp only [CollatzResearch.WordTrace]
  refine ⟨34950267014923963367345315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93200712039797235646254173 34950267014923963367345315)
  ·
    refine ⟨52425400522385945051017973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34950267014923963367345315 52425400522385945051017973)
    ·
      refine ⟨4914881298973682348532935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 52425400522385945051017973 4914881298973682348532935)
      ·
        refine ⟨7372321948460523522799403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4914881298973682348532935 7372321948460523522799403)
        ·
          refine ⟨11058482922690785284199105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7372321948460523522799403 11058482922690785284199105)
          ·
            refine ⟨8293862192018088963149329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11058482922690785284199105 8293862192018088963149329)
            ·
              refine ⟨6220396644013566722361997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8293862192018088963149329 6220396644013566722361997)
              ·
                refine ⟨2332648741505087520885749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6220396644013566722361997 2332648741505087520885749)
                ·
                  refine ⟨218685819516101955083039, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2332648741505087520885749 218685819516101955083039)
                  ·
                    rfl

theorem cell23_3833002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 2, 2, 3, 5].length) (baseStart_3833002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3833002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3833002 prefixEnd_3833002 := by exact prefixLift 3833002
  have htrace : WordTrace (prefixWord ++ tailWord_3833002) baseStart_3833002 baseEnd_3833002 := by
    simpa [prefixWord, tailWord_3833002, baseEnd_3833002] using wordTrace_append hprefix tailTrace_3833002
  have hstable : (prefixWord ++ tailWord_3833002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3833002).length < 2 ^ (prefixWord ++ tailWord_3833002).sum := by decide
  have hdescent : baseEnd_3833002 < baseStart_3833002 := by decide
  rcases family_descends (prefixWord ++ tailWord_3833002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3833021 : List Nat := [1, 4, 1, 2, 1, 1, 2, 1, 2, 3, 5]
def baseStart_3833021 : Nat := 118140960795 + 3833021 * 2 ^ 59
def prefixEnd_3833021 : Nat := 4983230072969 + 3 ^ 40 * 3833021 * 2
def baseEnd_3833021 : Nat := 1968182131777353021409763

theorem tailTrace_3833021 : CollatzResearch.WordTrace tailWord_3833021 prefixEnd_3833021 1968182131777353021409763 := by
  unfold tailWord_3833021
  simp only [CollatzResearch.WordTrace]
  refine ⟨139801761046627019714322917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93201174031084679809548611 139801761046627019714322917)
  ·
    refine ⟨26212830196242566196435547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 139801761046627019714322917 26212830196242566196435547)
    ·
      refine ⟨39319245294363849294653321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26212830196242566196435547 39319245294363849294653321)
      ·
        refine ⟨29489433970772886970989991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39319245294363849294653321 29489433970772886970989991)
        ·
          refine ⟨44234150956159330456484987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29489433970772886970989991 44234150956159330456484987)
          ·
            refine ⟨66351226434238995684727481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44234150956159330456484987 66351226434238995684727481)
            ·
              refine ⟨49763419825679246763545611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66351226434238995684727481 49763419825679246763545611)
              ·
                refine ⟨74645129738518870145318417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49763419825679246763545611 74645129738518870145318417)
                ·
                  refine ⟨55983847303889152608988813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 74645129738518870145318417 55983847303889152608988813)
                  ·
                    refine ⟨20993942738958432228370805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 55983847303889152608988813 20993942738958432228370805)
                    ·
                      refine ⟨1968182131777353021409763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20993942738958432228370805 1968182131777353021409763)
                      ·
                        rfl

theorem cell23_3833021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 2, 1, 2, 3, 5].length) (baseStart_3833021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3833021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3833021 prefixEnd_3833021 := by exact prefixLift 3833021
  have htrace : WordTrace (prefixWord ++ tailWord_3833021) baseStart_3833021 baseEnd_3833021 := by
    simpa [prefixWord, tailWord_3833021, baseEnd_3833021] using wordTrace_append hprefix tailTrace_3833021
  have hstable : (prefixWord ++ tailWord_3833021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3833021).length < 2 ^ (prefixWord ++ tailWord_3833021).sum := by decide
  have hdescent : baseEnd_3833021 < baseStart_3833021 := by decide
  rcases family_descends (prefixWord ++ tailWord_3833021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3833030 : List Nat := [6, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2]
def baseStart_3833030 : Nat := 118140960795 + 3833030 * 2 ^ 59
def prefixEnd_3833030 : Nat := 4983230072969 + 3 ^ 40 * 3833030 * 2
def baseEnd_3833030 : Nat := 1968186753103243486197223

theorem tailTrace_3833030 : CollatzResearch.WordTrace tailWord_3833030 prefixEnd_3833030 1968186753103243486197223 := by
  unfold tailWord_3833030
  simp only [CollatzResearch.WordTrace]
  refine ⟨4368815290737325445356267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 93201392869062942834267029 4368815290737325445356267)
  ·
    refine ⟨6553222936105988168034401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4368815290737325445356267 6553222936105988168034401)
    ·
      refine ⟨4914917202079491126025801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6553222936105988168034401 4914917202079491126025801)
      ·
        refine ⟨3686187901559618344519351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4914917202079491126025801 3686187901559618344519351)
        ·
          refine ⟨5529281852339427516779027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3686187901559618344519351 5529281852339427516779027)
          ·
            refine ⟨8293922778509141275168541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5529281852339427516779027 8293922778509141275168541)
            ·
              refine ⟨3110221041940927978188203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8293922778509141275168541 3110221041940927978188203)
              ·
                refine ⟨4665331562911391967282305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3110221041940927978188203 4665331562911391967282305)
                ·
                  refine ⟨3498998672183543975461729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4665331562911391967282305 3498998672183543975461729)
                  ·
                    refine ⟨2624249004137657981596297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3498998672183543975461729 2624249004137657981596297)
                    ·
                      refine ⟨1968186753103243486197223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2624249004137657981596297 1968186753103243486197223)
                      ·
                        rfl

theorem cell23_3833030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2].length) (baseStart_3833030 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3833030 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3833030 prefixEnd_3833030 := by exact prefixLift 3833030
  have htrace : WordTrace (prefixWord ++ tailWord_3833030) baseStart_3833030 baseEnd_3833030 := by
    simpa [prefixWord, tailWord_3833030, baseEnd_3833030] using wordTrace_append hprefix tailTrace_3833030
  have hstable : (prefixWord ++ tailWord_3833030).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3833030).length < 2 ^ (prefixWord ++ tailWord_3833030).sum := by decide
  have hdescent : baseEnd_3833030 < baseStart_3833030 := by decide
  rcases family_descends (prefixWord ++ tailWord_3833030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3833045 : List Nat := [1, 3, 2, 4, 1, 1, 2, 2, 3, 4]
def baseStart_3833045 : Nat := 118140960795 + 3833045 * 2 ^ 59
def prefixEnd_3833045 : Nat := 4983230072969 + 3 ^ 40 * 3833045 * 2
def baseEnd_3833045 : Nat := 656064818437686975836551

theorem tailTrace_3833045 : CollatzResearch.WordTrace tailWord_3833045 prefixEnd_3833045 656064818437686975836551 := by
  unfold tailWord_3833045
  simp only [CollatzResearch.WordTrace]
  refine ⟨139802636398540071813196589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93201757599026714542131059 139802636398540071813196589)
  ·
    refine ⟨52425988649452526929948721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 139802636398540071813196589 52425988649452526929948721)
    ·
      refine ⟨39319491487089395197461541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52425988649452526929948721 39319491487089395197461541)
      ·
        refine ⟨7372404653829261599524039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 39319491487089395197461541 7372404653829261599524039)
        ·
          refine ⟨11058606980743892399286059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7372404653829261599524039 11058606980743892399286059)
          ·
            refine ⟨16587910471115838598929089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11058606980743892399286059 16587910471115838598929089)
            ·
              refine ⟨12440932853336878949196817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16587910471115838598929089 12440932853336878949196817)
              ·
                refine ⟨9330699640002659211897613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12440932853336878949196817 9330699640002659211897613)
                ·
                  refine ⟨3499012365000997204461605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9330699640002659211897613 3499012365000997204461605)
                  ·
                    refine ⟨656064818437686975836551, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3499012365000997204461605 656064818437686975836551)
                    ·
                      rfl

theorem cell23_3833045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 2, 2, 3, 4].length) (baseStart_3833045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3833045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3833045 prefixEnd_3833045 := by exact prefixLift 3833045
  have htrace : WordTrace (prefixWord ++ tailWord_3833045) baseStart_3833045 baseEnd_3833045 := by
    simpa [prefixWord, tailWord_3833045, baseEnd_3833045] using wordTrace_append hprefix tailTrace_3833045
  have hstable : (prefixWord ++ tailWord_3833045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3833045).length < 2 ^ (prefixWord ++ tailWord_3833045).sum := by decide
  have hdescent : baseEnd_3833045 < baseStart_3833045 := by decide
  rcases family_descends (prefixWord ++ tailWord_3833045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3833092 : List Nat := [2, 3, 2, 2, 2, 3, 2, 1, 6]
def baseStart_3833092 : Nat := 118140960795 + 3833092 * 2 ^ 59
def prefixEnd_3833092 : Nat := 4983230072969 + 3 ^ 40 * 3833092 * 2
def baseEnd_3833092 : Nat := 218690954322646915957993

theorem tailTrace_3833092 : CollatzResearch.WordTrace tailWord_3833092 prefixEnd_3833092 218690954322646915957993 := by
  unfold tailWord_3833092
  simp only [CollatzResearch.WordTrace]
  refine ⟨69902175314684899420078765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93202900419579865893438353 69902175314684899420078765)
  ·
    refine ⟨26213315743006837282529537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69902175314684899420078765 26213315743006837282529537)
    ·
      refine ⟨19659986807255127961897153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26213315743006837282529537 19659986807255127961897153)
      ·
        refine ⟨14744990105441345971422865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19659986807255127961897153 14744990105441345971422865)
        ·
          refine ⟨11058742579081009478567149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14744990105441345971422865 11058742579081009478567149)
          ·
            refine ⟨4147028467155378554462681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11058742579081009478567149 4147028467155378554462681)
            ·
              refine ⟨3110271350366533915847011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4147028467155378554462681 3110271350366533915847011)
              ·
                refine ⟨4665407025549800873770517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3110271350366533915847011 4665407025549800873770517)
                ·
                  refine ⟨218690954322646915957993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4665407025549800873770517 218690954322646915957993)
                  ·
                    rfl

theorem cell23_3833092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 3, 2, 1, 6].length) (baseStart_3833092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3833092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3833092 prefixEnd_3833092 := by exact prefixLift 3833092
  have htrace : WordTrace (prefixWord ++ tailWord_3833092) baseStart_3833092 baseEnd_3833092 := by
    simpa [prefixWord, tailWord_3833092, baseEnd_3833092] using wordTrace_append hprefix tailTrace_3833092
  have hstable : (prefixWord ++ tailWord_3833092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3833092).length < 2 ^ (prefixWord ++ tailWord_3833092).sum := by decide
  have hdescent : baseEnd_3833092 < baseStart_3833092 := by decide
  rcases family_descends (prefixWord ++ tailWord_3833092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3833112 : List Nat := [2, 1, 2, 3, 1, 4, 2, 1, 2, 3, 2]
def baseStart_3833112 : Nat := 118140960795 + 3833112 * 2 ^ 59
def prefixEnd_3833112 : Nat := 4983230072969 + 3 ^ 40 * 3833112 * 2
def baseEnd_3833112 : Nat := 1968228858516912165371845

theorem tailTrace_3833112 : CollatzResearch.WordTrace tailWord_3833112 prefixEnd_3833112 1968228858516912165371845 := by
  unfold tailWord_3833112
  simp only [CollatzResearch.WordTrace]
  refine ⟨69902540044648671127942795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93203386726198228170590393 69902540044648671127942795)
  ·
    refine ⟨104853810066973006691914193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69902540044648671127942795 104853810066973006691914193)
    ·
      refine ⟨78640357550229755018935645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104853810066973006691914193 78640357550229755018935645)
      ·
        refine ⟨29490134081336158132100867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 78640357550229755018935645 29490134081336158132100867)
        ·
          refine ⟨44235201122004237198151301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29490134081336158132100867 44235201122004237198151301)
          ·
            refine ⟨8294100210375794474653369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 44235201122004237198151301 8294100210375794474653369)
            ·
              refine ⟨6220575157781845855990027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8294100210375794474653369 6220575157781845855990027)
              ·
                refine ⟨9330862736672768783985041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6220575157781845855990027 9330862736672768783985041)
                ·
                  refine ⟨6998147052504576587988781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9330862736672768783985041 6998147052504576587988781)
                  ·
                    refine ⟨2624305144689216220495793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6998147052504576587988781 2624305144689216220495793)
                    ·
                      refine ⟨1968228858516912165371845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2624305144689216220495793 1968228858516912165371845)
                      ·
                        rfl

theorem cell23_3833112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 4, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 4, 2, 1, 2, 3, 2].length) (baseStart_3833112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3833112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3833112 prefixEnd_3833112 := by exact prefixLift 3833112
  have htrace : WordTrace (prefixWord ++ tailWord_3833112) baseStart_3833112 baseEnd_3833112 := by
    simpa [prefixWord, tailWord_3833112, baseEnd_3833112] using wordTrace_append hprefix tailTrace_3833112
  have hstable : (prefixWord ++ tailWord_3833112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3833112).length < 2 ^ (prefixWord ++ tailWord_3833112).sum := by decide
  have hdescent : baseEnd_3833112 < baseStart_3833112 := by decide
  rcases family_descends (prefixWord ++ tailWord_3833112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3833148 : List Nat := [2, 2, 2, 2, 1, 3, 3, 8]
def baseStart_3833148 : Nat := 118140960795 + 3833148 * 2 ^ 59
def prefixEnd_3833148 : Nat := 4983230072969 + 3 ^ 40 * 3833148 * 2
def baseEnd_3833148 : Nat := 72898049771128667574877

theorem tailTrace_3833148 : CollatzResearch.WordTrace tailWord_3833148 prefixEnd_3833148 72898049771128667574877 := by
  unfold tailWord_3833148
  simp only [CollatzResearch.WordTrace]
  refine ⟨69903196558583460202098049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93204262078111280269464065 69903196558583460202098049)
  ·
    refine ⟨52427397418937595151573537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69903196558583460202098049 52427397418937595151573537)
    ·
      refine ⟨39320548064203196363680153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52427397418937595151573537 39320548064203196363680153)
      ·
        refine ⟨29490411048152397272760115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39320548064203196363680153 29490411048152397272760115)
        ·
          refine ⟨44235616572228595909140173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29490411048152397272760115 44235616572228595909140173)
          ·
            refine ⟨16588356214585723465927565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44235616572228595909140173 16588356214585723465927565)
            ·
              refine ⟨6220633580469646299722837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16588356214585723465927565 6220633580469646299722837)
              ·
                refine ⟨72898049771128667574877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6220633580469646299722837 72898049771128667574877)
                ·
                  rfl

theorem cell23_3833148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 3, 8].length) (baseStart_3833148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3833148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3833148 prefixEnd_3833148 := by exact prefixLift 3833148
  have htrace : WordTrace (prefixWord ++ tailWord_3833148) baseStart_3833148 baseEnd_3833148 := by
    simpa [prefixWord, tailWord_3833148, baseEnd_3833148] using wordTrace_append hprefix tailTrace_3833148
  have hstable : (prefixWord ++ tailWord_3833148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3833148).length < 2 ^ (prefixWord ++ tailWord_3833148).sum := by decide
  have hdescent : baseEnd_3833148 < baseStart_3833148 := by decide
  rcases family_descends (prefixWord ++ tailWord_3833148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3833175 : List Nat := [1, 1, 3, 2, 3, 2, 2, 2, 1, 3, 3]
def baseStart_3833175 : Nat := 118140960795 + 3833175 * 2 ^ 59
def prefixEnd_3833175 : Nat := 4983230072969 + 3 ^ 40 * 3833175 * 2
def baseEnd_3833175 : Nat := 1968261207798145418884055

theorem tailTrace_3833175 : CollatzResearch.WordTrace tailWord_3833175 prefixEnd_3833175 1968261207798145418884055 := by
  unfold tailWord_3833175
  simp only [CollatzResearch.WordTrace]
  refine ⟨139807377888069104015428979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93204918592046069343619319 139807377888069104015428979)
  ·
    refine ⟨209711066832103656023143469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139807377888069104015428979 209711066832103656023143469)
    ·
      refine ⟨78641650062038871008678801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 209711066832103656023143469 78641650062038871008678801)
      ·
        refine ⟨58981237546529153256509101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78641650062038871008678801 58981237546529153256509101)
        ·
          refine ⟨22117964079948432471190913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58981237546529153256509101 22117964079948432471190913)
          ·
            refine ⟨16588473059961324353393185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22117964079948432471190913 16588473059961324353393185)
            ·
              refine ⟨12441354794970993265044889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16588473059961324353393185 12441354794970993265044889)
              ·
                refine ⟨9331016096228244948783667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12441354794970993265044889 9331016096228244948783667)
                ·
                  refine ⟨13996524144342367423175501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9331016096228244948783667 13996524144342367423175501)
                  ·
                    refine ⟨5248696554128387783690813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13996524144342367423175501 5248696554128387783690813)
                    ·
                      refine ⟨1968261207798145418884055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5248696554128387783690813 1968261207798145418884055)
                      ·
                        rfl

theorem cell23_3833175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 2, 2, 1, 3, 3].length) (baseStart_3833175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3833175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3833175 prefixEnd_3833175 := by exact prefixLift 3833175
  have htrace : WordTrace (prefixWord ++ tailWord_3833175) baseStart_3833175 baseEnd_3833175 := by
    simpa [prefixWord, tailWord_3833175, baseEnd_3833175] using wordTrace_append hprefix tailTrace_3833175
  have hstable : (prefixWord ++ tailWord_3833175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3833175).length < 2 ^ (prefixWord ++ tailWord_3833175).sum := by decide
  have hdescent : baseEnd_3833175 < baseStart_3833175 := by decide
  rcases family_descends (prefixWord ++ tailWord_3833175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3833219 : List Nat := [1, 1, 1, 3, 5, 2, 2, 2, 1, 3, 2]
def baseStart_3833219 : Nat := 118140960795 + 3833219 * 2 ^ 59
def prefixEnd_3833219 : Nat := 4983230072969 + 3 ^ 40 * 3833219 * 2
def baseEnd_3833219 : Nat := 1968283800946943246733853

theorem tailTrace_3833219 : CollatzResearch.WordTrace tailWord_3833219 prefixEnd_3833219 1968283800946943246733853 := by
  unfold tailWord_3833219
  simp only [CollatzResearch.WordTrace]
  refine ⟨139808982699909699530030711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93205988466606466353353807 139808982699909699530030711)
  ·
    refine ⟨209713474049864549295046067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139808982699909699530030711 209713474049864549295046067)
    ·
      refine ⟨314570211074796823942569101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209713474049864549295046067 314570211074796823942569101)
      ·
        refine ⟨117963829153048808978463413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 314570211074796823942569101 117963829153048808978463413)
        ·
          refine ⟨11059108983098325841730945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 117963829153048808978463413 11059108983098325841730945)
          ·
            refine ⟨8294331737323744381298209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11059108983098325841730945 8294331737323744381298209)
            ·
              refine ⟨6220748802992808285973657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8294331737323744381298209 6220748802992808285973657)
              ·
                refine ⟨4665561602244606214480243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6220748802992808285973657 4665561602244606214480243)
                ·
                  refine ⟨6998342403366909321720365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4665561602244606214480243 6998342403366909321720365)
                  ·
                    refine ⟨2624378401262590995645137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6998342403366909321720365 2624378401262590995645137)
                    ·
                      refine ⟨1968283800946943246733853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2624378401262590995645137 1968283800946943246733853)
                      ·
                        rfl

theorem cell23_3833219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 2, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 2, 2, 2, 1, 3, 2].length) (baseStart_3833219 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3833219 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3833219 prefixEnd_3833219 := by exact prefixLift 3833219
  have htrace : WordTrace (prefixWord ++ tailWord_3833219) baseStart_3833219 baseEnd_3833219 := by
    simpa [prefixWord, tailWord_3833219, baseEnd_3833219] using wordTrace_append hprefix tailTrace_3833219
  have hstable : (prefixWord ++ tailWord_3833219).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3833219).length < 2 ^ (prefixWord ++ tailWord_3833219).sum := by decide
  have hdescent : baseEnd_3833219 < baseStart_3833219 := by decide
  rcases family_descends (prefixWord ++ tailWord_3833219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3833248 : List Nat := [2, 1, 1, 4, 1, 2, 1, 1, 1, 2, 7]
def baseStart_3833248 : Nat := 118140960795 + 3833248 * 2 ^ 59
def prefixEnd_3833248 : Nat := 4983230072969 + 3 ^ 40 * 3833248 * 2
def baseEnd_3833248 : Nat := 1968298691885923633271219

theorem tailTrace_3833248 : CollatzResearch.WordTrace tailWord_3833248 prefixEnd_3833248 1968298691885923633271219 := by
  unfold tailWord_3833248
  simp only [CollatzResearch.WordTrace]
  refine ⟨69905020208402318741418199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93206693611203091655224265 69905020208402318741418199)
  ·
    refine ⟨104857530312603478112127299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69905020208402318741418199 104857530312603478112127299)
    ·
      refine ⟨157286295468905217168190949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104857530312603478112127299 157286295468905217168190949)
      ·
        refine ⟨29491180400419728219035803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 157286295468905217168190949 29491180400419728219035803)
        ·
          refine ⟨44236770600629592328553705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29491180400419728219035803 44236770600629592328553705)
          ·
            refine ⟨33177577950472194246415279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44236770600629592328553705 33177577950472194246415279)
            ·
              refine ⟨49766366925708291369622919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33177577950472194246415279 49766366925708291369622919)
              ·
                refine ⟨74649550388562437054434379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49766366925708291369622919 74649550388562437054434379)
                ·
                  refine ⟨111974325582843655581651569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 74649550388562437054434379 111974325582843655581651569)
                  ·
                    refine ⟨83980744187132741686238677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 111974325582843655581651569 83980744187132741686238677)
                    ·
                      refine ⟨1968298691885923633271219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 83980744187132741686238677 1968298691885923633271219)
                      ·
                        rfl

theorem cell23_3833248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 1, 1, 1, 2, 7].length) (baseStart_3833248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3833248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3833248 prefixEnd_3833248 := by exact prefixLift 3833248
  have htrace : WordTrace (prefixWord ++ tailWord_3833248) baseStart_3833248 baseEnd_3833248 := by
    simpa [prefixWord, tailWord_3833248, baseEnd_3833248] using wordTrace_append hprefix tailTrace_3833248
  have hstable : (prefixWord ++ tailWord_3833248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3833248).length < 2 ^ (prefixWord ++ tailWord_3833248).sum := by decide
  have hdescent : baseEnd_3833248 < baseStart_3833248 := by decide
  rcases family_descends (prefixWord ++ tailWord_3833248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3833265 : List Nat := [1, 2, 2, 4, 1, 1, 2, 1, 1, 5, 3]
def baseStart_3833265 : Nat := 118140960795 + 3833265 * 2 ^ 59
def prefixEnd_3833265 : Nat := 4983230072969 + 3 ^ 40 * 3833265 * 2
def baseEnd_3833265 : Nat := 1968307421057050066758641

theorem tailTrace_3833265 : CollatzResearch.WordTrace tailWord_3833265 prefixEnd_3833265 1968307421057050066758641 := by
  unfold tailWord_3833265
  simp only [CollatzResearch.WordTrace]
  refine ⟨139810660457743049386205249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93207106971828699590803499 139810660457743049386205249)
  ·
    refine ⟨104857995343307287039653937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139810660457743049386205249 104857995343307287039653937)
    ·
      refine ⟨78643496507480465279740453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104857995343307287039653937 78643496507480465279740453)
      ·
        refine ⟨14745655595152587239951335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 78643496507480465279740453 14745655595152587239951335)
        ·
          refine ⟨22118483392728880859927003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14745655595152587239951335 22118483392728880859927003)
          ·
            refine ⟨33177725089093321289890505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22118483392728880859927003 33177725089093321289890505)
            ·
              refine ⟨24883293816819990967417879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33177725089093321289890505 24883293816819990967417879)
              ·
                refine ⟨37324940725229986451126819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24883293816819990967417879 37324940725229986451126819)
                ·
                  refine ⟨55987411087844979676690229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37324940725229986451126819 55987411087844979676690229)
                  ·
                    refine ⟨5248819789485466844689709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 55987411087844979676690229 5248819789485466844689709)
                    ·
                      refine ⟨1968307421057050066758641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5248819789485466844689709 1968307421057050066758641)
                      ·
                        rfl

theorem cell23_3833265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 2, 1, 1, 5, 3].length) (baseStart_3833265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3833265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3833265 prefixEnd_3833265 := by exact prefixLift 3833265
  have htrace : WordTrace (prefixWord ++ tailWord_3833265) baseStart_3833265 baseEnd_3833265 := by
    simpa [prefixWord, tailWord_3833265, baseEnd_3833265] using wordTrace_append hprefix tailTrace_3833265
  have hstable : (prefixWord ++ tailWord_3833265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3833265).length < 2 ^ (prefixWord ++ tailWord_3833265).sum := by decide
  have hdescent : baseEnd_3833265 < baseStart_3833265 := by decide
  rcases family_descends (prefixWord ++ tailWord_3833265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3833365 : List Nat := [1, 3, 2, 1, 3, 2, 1, 1, 1, 2, 6]
def baseStart_3833365 : Nat := 118140960795 + 3833365 * 2 ^ 59
def prefixEnd_3833365 : Nat := 4983230072969 + 3 ^ 40 * 3833365 * 2
def baseEnd_3833365 : Nat := 1968358769122499675508181

theorem tailTrace_3833365 : CollatzResearch.WordTrace tailWord_3833365 prefixEnd_3833365 1968358769122499675508181 := by
  unfold tailWord_3833365
  simp only [CollatzResearch.WordTrace]
  refine ⟨139814307757380766464845549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93209538504920510976563699 139814307757380766464845549)
  ·
    refine ⟨52430365409017787424317081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 139814307757380766464845549 52430365409017787424317081)
    ·
      refine ⟨39322774056763340568237811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52430365409017787424317081 39322774056763340568237811)
      ·
        refine ⟨58984161085145010852356717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39322774056763340568237811 58984161085145010852356717)
        ·
          refine ⟨22119060406929379069633769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58984161085145010852356717 22119060406929379069633769)
          ·
            refine ⟨16589295305197034302225327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22119060406929379069633769 16589295305197034302225327)
            ·
              refine ⟨24883942957795551453337991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16589295305197034302225327 24883942957795551453337991)
              ·
                refine ⟨37325914436693327180006987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24883942957795551453337991 37325914436693327180006987)
                ·
                  refine ⟨55988871655039990770010481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37325914436693327180006987 55988871655039990770010481)
                  ·
                    refine ⟨41991653741279993077507861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 55988871655039990770010481 41991653741279993077507861)
                    ·
                      refine ⟨1968358769122499675508181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 41991653741279993077507861 1968358769122499675508181)
                      ·
                        rfl

theorem cell23_3833365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 1, 1, 1, 2, 6].length) (baseStart_3833365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3833365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3833365 prefixEnd_3833365 := by exact prefixLift 3833365
  have htrace : WordTrace (prefixWord ++ tailWord_3833365) baseStart_3833365 baseEnd_3833365 := by
    simpa [prefixWord, tailWord_3833365, baseEnd_3833365] using wordTrace_append hprefix tailTrace_3833365
  have hstable : (prefixWord ++ tailWord_3833365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3833365).length < 2 ^ (prefixWord ++ tailWord_3833365).sum := by decide
  have hdescent : baseEnd_3833365 < baseStart_3833365 := by decide
  rcases family_descends (prefixWord ++ tailWord_3833365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3833375 : List Nat := [1, 1, 2, 4, 1, 1, 2, 1, 5, 5]
def baseStart_3833375 : Nat := 118140960795 + 3833375 * 2 ^ 59
def prefixEnd_3833375 : Nat := 4983230072969 + 3 ^ 40 * 3833375 * 2
def baseEnd_3833375 : Nat := 656121301309681545461045

theorem tailTrace_3833375 : CollatzResearch.WordTrace tailWord_3833375 prefixEnd_3833375 656121301309681545461045 := by
  unfold tailWord_3833375
  simp only [CollatzResearch.WordTrace]
  refine ⟨139814672487344538172709579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93209781658229692115139719 139814672487344538172709579)
  ·
    refine ⟨209722008731016807259064369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139814672487344538172709579 209722008731016807259064369)
    ·
      refine ⟨157291506548262605444298277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 209722008731016807259064369 157291506548262605444298277)
      ·
        refine ⟨29492157477799238520805927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 157291506548262605444298277 29492157477799238520805927)
        ·
          refine ⟨44238236216698857781208891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29492157477799238520805927 44238236216698857781208891)
          ·
            refine ⟨66357354325048286671813337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44238236216698857781208891 66357354325048286671813337)
            ·
              refine ⟨49768015743786215003860003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66357354325048286671813337 49768015743786215003860003)
              ·
                refine ⟨74652023615679322505790005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49768015743786215003860003 74652023615679322505790005)
                ·
                  refine ⟨6998627213969936484917813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 74652023615679322505790005 6998627213969936484917813)
                  ·
                    refine ⟨656121301309681545461045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6998627213969936484917813 656121301309681545461045)
                    ·
                      rfl

theorem cell23_3833375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 2, 1, 5, 5].length) (baseStart_3833375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3833375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3833375 prefixEnd_3833375 := by exact prefixLift 3833375
  have htrace : WordTrace (prefixWord ++ tailWord_3833375) baseStart_3833375 baseEnd_3833375 := by
    simpa [prefixWord, tailWord_3833375, baseEnd_3833375] using wordTrace_append hprefix tailTrace_3833375
  have hstable : (prefixWord ++ tailWord_3833375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3833375).length < 2 ^ (prefixWord ++ tailWord_3833375).sum := by decide
  have hdescent : baseEnd_3833375 < baseStart_3833375 := by decide
  rcases family_descends (prefixWord ++ tailWord_3833375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3833379 : List Nat := [1, 1, 1, 4, 5, 1, 3, 1, 6]
def baseStart_3833379 : Nat := 118140960795 + 3833379 * 2 ^ 59
def prefixEnd_3833379 : Nat := 4983230072969 + 3 ^ 40 * 3833379 * 2
def baseEnd_3833379 : Nat := 218707328650184735637013

theorem tailTrace_3833379 : CollatzResearch.WordTrace tailWord_3833379 prefixEnd_3833379 218707328650184735637013 := by
  unfold tailWord_3833379
  simp only [CollatzResearch.WordTrace]
  refine ⟨139814818379330046855855191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93209878919553364570570127 139814818379330046855855191)
  ·
    refine ⟨209722227568995070283782787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139814818379330046855855191 209722227568995070283782787)
    ·
      refine ⟨314583341353492605425674181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209722227568995070283782787 314583341353492605425674181)
      ·
        refine ⟨58984376503779863517313909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 314583341353492605425674181 58984376503779863517313909)
        ·
          refine ⟨5529785297229362204748179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 58984376503779863517313909 5529785297229362204748179)
          ·
            refine ⟨8294677945844043307122269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5529785297229362204748179 8294677945844043307122269)
            ·
              refine ⟨3110504229691516240170851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8294677945844043307122269 3110504229691516240170851)
              ·
                refine ⟨4665756344537274360256277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3110504229691516240170851 4665756344537274360256277)
                ·
                  refine ⟨218707328650184735637013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4665756344537274360256277 218707328650184735637013)
                  ·
                    rfl

theorem cell23_3833379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 1, 3, 1, 6].length) (baseStart_3833379 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3833379 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3833379 prefixEnd_3833379 := by exact prefixLift 3833379
  have htrace : WordTrace (prefixWord ++ tailWord_3833379) baseStart_3833379 baseEnd_3833379 := by
    simpa [prefixWord, tailWord_3833379, baseEnd_3833379] using wordTrace_append hprefix tailTrace_3833379
  have hstable : (prefixWord ++ tailWord_3833379).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3833379).length < 2 ^ (prefixWord ++ tailWord_3833379).sum := by decide
  have hdescent : baseEnd_3833379 < baseStart_3833379 := by decide
  rcases family_descends (prefixWord ++ tailWord_3833379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3833425 : List Nat := [1, 2, 2, 1, 3, 2, 1, 1, 3, 1, 6]
def baseStart_3833425 : Nat := 118140960795 + 3833425 * 2 ^ 59
def prefixEnd_3833425 : Nat := 4983230072969 + 3 ^ 40 * 3833425 * 2
def baseEnd_3833425 : Nat := 1968389577961769440757905

theorem tailTrace_3833425 : CollatzResearch.WordTrace tailWord_3833425 prefixEnd_3833425 1968389577961769440757905 := by
  unfold tailWord_3833425
  simp only [CollatzResearch.WordTrace]
  refine ⟨139816496137163396712029729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93210997424775597808019819 139816496137163396712029729)
  ·
    refine ⟨104862372102872547534022297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139816496137163396712029729 104862372102872547534022297)
    ·
      refine ⟨78646779077154410650516723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104862372102872547534022297 78646779077154410650516723)
      ·
        refine ⟨117970168615731615975775085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78646779077154410650516723 117970168615731615975775085)
        ·
          refine ⟨44238813230899355990915657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 117970168615731615975775085 44238813230899355990915657)
          ·
            refine ⟨33179109923174516993186743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44238813230899355990915657 33179109923174516993186743)
            ·
              refine ⟨49768664884761775489780115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33179109923174516993186743 49768664884761775489780115)
              ·
                refine ⟨74652997327142663234670173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49768664884761775489780115 74652997327142663234670173)
                ·
                  refine ⟨27994873997678498713001315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 74652997327142663234670173 27994873997678498713001315)
                  ·
                    refine ⟨41992310996517748069501973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27994873997678498713001315 41992310996517748069501973)
                    ·
                      refine ⟨1968389577961769440757905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 41992310996517748069501973 1968389577961769440757905)
                      ·
                        rfl

theorem cell23_3833425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 1, 1, 3, 1, 6].length) (baseStart_3833425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3833425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3833425 prefixEnd_3833425 := by exact prefixLift 3833425
  have htrace : WordTrace (prefixWord ++ tailWord_3833425) baseStart_3833425 baseEnd_3833425 := by
    simpa [prefixWord, tailWord_3833425, baseEnd_3833425] using wordTrace_append hprefix tailTrace_3833425
  have hstable : (prefixWord ++ tailWord_3833425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3833425).length < 2 ^ (prefixWord ++ tailWord_3833425).sum := by decide
  have hdescent : baseEnd_3833425 < baseStart_3833425 := by decide
  rcases family_descends (prefixWord ++ tailWord_3833425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3833430 : List Nat := [5, 2, 2, 2, 1, 2, 2, 1, 6]
def baseStart_3833430 : Nat := 118140960795 + 3833430 * 2 ^ 59
def prefixEnd_3833430 : Nat := 4983230072969 + 3 ^ 40 * 3833430 * 2
def baseEnd_3833430 : Nat := 218710238373893546799487

theorem tailTrace_3833430 : CollatzResearch.WordTrace tailWord_3833430 prefixEnd_3833430 218710238373893546799487 := by
  unfold tailWord_3833430
  simp only [CollatzResearch.WordTrace]
  refine ⟨8738542406384080160372609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 93211119001430188377307829 8738542406384080160372609)
  ·
    refine ⟨6553906804788060120279457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8738542406384080160372609 6553906804788060120279457)
    ·
      refine ⟨4915430103591045090209593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6553906804788060120279457 4915430103591045090209593)
      ·
        refine ⟨3686572577693283817657195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4915430103591045090209593 3686572577693283817657195)
        ·
          refine ⟨5529858866539925726485793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3686572577693283817657195 5529858866539925726485793)
          ·
            refine ⟨4147394149904944294864345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5529858866539925726485793 4147394149904944294864345)
            ·
              refine ⟨3110545612428708221148259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4147394149904944294864345 3110545612428708221148259)
              ·
                refine ⟨4665818418643062331722389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3110545612428708221148259 4665818418643062331722389)
                ·
                  refine ⟨218710238373893546799487, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4665818418643062331722389 218710238373893546799487)
                  ·
                    rfl

theorem cell23_3833430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 2, 2, 1, 6].length) (baseStart_3833430 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3833430 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3833430 prefixEnd_3833430 := by exact prefixLift 3833430
  have htrace : WordTrace (prefixWord ++ tailWord_3833430) baseStart_3833430 baseEnd_3833430 := by
    simpa [prefixWord, tailWord_3833430, baseEnd_3833430] using wordTrace_append hprefix tailTrace_3833430
  have hstable : (prefixWord ++ tailWord_3833430).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3833430).length < 2 ^ (prefixWord ++ tailWord_3833430).sum := by decide
  have hdescent : baseEnd_3833430 < baseStart_3833430 := by decide
  rcases family_descends (prefixWord ++ tailWord_3833430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3833432 : List Nat := [2, 1, 2, 2, 1, 2, 1, 4, 3, 2, 3]
def baseStart_3833432 : Nat := 118140960795 + 3833432 * 2 ^ 59
def prefixEnd_3833432 : Nat := 4983230072969 + 3 ^ 40 * 3833432 * 2
def baseEnd_3833432 : Nat := 1968393172326350913370373

theorem tailTrace_3833432 : CollatzResearch.WordTrace tailWord_3833432 prefixEnd_3833432 1968393172326350913370373 := by
  unfold tailWord_3833432
  simp only [CollatzResearch.WordTrace]
  refine ⟨69908375724069018453767275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93211167632092024605023033 69908375724069018453767275)
  ·
    refine ⟨104862563586103527680650913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69908375724069018453767275 104862563586103527680650913)
    ·
      refine ⟨78646922689577645760488185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104862563586103527680650913 78646922689577645760488185)
      ·
        refine ⟨58985192017183234320366139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78646922689577645760488185 58985192017183234320366139)
        ·
          refine ⟨88477788025774851480549209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58985192017183234320366139 88477788025774851480549209)
          ·
            refine ⟨66358341019331138610411907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 88477788025774851480549209 66358341019331138610411907)
            ·
              refine ⟨99537511528996707915617861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66358341019331138610411907 99537511528996707915617861)
              ·
                refine ⟨18663283411686882734178349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 99537511528996707915617861 18663283411686882734178349)
                ·
                  refine ⟨6998731279382581025316881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18663283411686882734178349 6998731279382581025316881)
                  ·
                    refine ⟨5249048459536935768987661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6998731279382581025316881 5249048459536935768987661)
                    ·
                      refine ⟨1968393172326350913370373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5249048459536935768987661 1968393172326350913370373)
                      ·
                        rfl

theorem cell23_3833432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 4, 3, 2, 3].length) (baseStart_3833432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3833432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3833432 prefixEnd_3833432 := by exact prefixLift 3833432
  have htrace : WordTrace (prefixWord ++ tailWord_3833432) baseStart_3833432 baseEnd_3833432 := by
    simpa [prefixWord, tailWord_3833432, baseEnd_3833432] using wordTrace_append hprefix tailTrace_3833432
  have hstable : (prefixWord ++ tailWord_3833432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3833432).length < 2 ^ (prefixWord ++ tailWord_3833432).sum := by decide
  have hdescent : baseEnd_3833432 < baseStart_3833432 := by decide
  rcases family_descends (prefixWord ++ tailWord_3833432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3833449 : List Nat := [1, 2, 1, 1, 1, 4, 5, 2, 1, 2, 3]
def baseStart_3833449 : Nat := 118140960795 + 3833449 * 2 ^ 59
def prefixEnd_3833449 : Nat := 4983230072969 + 3 ^ 40 * 3833449 * 2
def baseEnd_3833449 : Nat := 1968401901497477346857795

theorem tailTrace_3833449 : CollatzResearch.WordTrace tailWord_3833449 prefixEnd_3833449 1968401901497477346857795 := by
  unfold tailWord_3833449
  simp only [CollatzResearch.WordTrace]
  refine ⟨139817371489076448810903401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93211580992717632540602267 139817371489076448810903401)
  ·
    refine ⟨104863028616807336608177551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139817371489076448810903401 104863028616807336608177551)
    ·
      refine ⟨157294542925211004912266327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104863028616807336608177551 157294542925211004912266327)
      ·
        refine ⟨235941814387816507368399491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157294542925211004912266327 235941814387816507368399491)
        ·
          refine ⟨353912721581724761052599237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 235941814387816507368399491 353912721581724761052599237)
          ·
            refine ⟨66358635296573392697362357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 353912721581724761052599237 66358635296573392697362357)
            ·
              refine ⟨6221122059053755565377721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 66358635296573392697362357 6221122059053755565377721)
              ·
                refine ⟨4665841544290316674033291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6221122059053755565377721 4665841544290316674033291)
                ·
                  refine ⟨6998762316435475011049937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4665841544290316674033291 6998762316435475011049937)
                  ·
                    refine ⟨5249071737326606258287453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6998762316435475011049937 5249071737326606258287453)
                    ·
                      refine ⟨1968401901497477346857795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5249071737326606258287453 1968401901497477346857795)
                      ·
                        rfl

theorem cell23_3833449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 5, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 5, 2, 1, 2, 3].length) (baseStart_3833449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3833449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3833449 prefixEnd_3833449 := by exact prefixLift 3833449
  have htrace : WordTrace (prefixWord ++ tailWord_3833449) baseStart_3833449 baseEnd_3833449 := by
    simpa [prefixWord, tailWord_3833449, baseEnd_3833449] using wordTrace_append hprefix tailTrace_3833449
  have hstable : (prefixWord ++ tailWord_3833449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3833449).length < 2 ^ (prefixWord ++ tailWord_3833449).sum := by decide
  have hdescent : baseEnd_3833449 < baseStart_3833449 := by decide
  rcases family_descends (prefixWord ++ tailWord_3833449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3833482 : List Nat := [3, 1, 2, 3, 2, 1, 1, 1, 2, 7]
def baseStart_3833482 : Nat := 118140960795 + 3833482 * 2 ^ 59
def prefixEnd_3833482 : Nat := 4983230072969 + 3 ^ 40 * 3833482 * 2
def baseEnd_3833482 : Nat := 656139615453025239248381

theorem tailTrace_3833482 : CollatzResearch.WordTrace tailWord_3833482 prefixEnd_3833482 656139615453025239248381 := by
  unfold tailWord_3833482
  simp only [CollatzResearch.WordTrace]
  refine ⟨34954643774489223861713675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93212383398637930297903133 34954643774489223861713675)
  ·
    refine ⟨52431965661733835792570513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34954643774489223861713675 52431965661733835792570513)
    ·
      refine ⟨39323974246300376844427885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52431965661733835792570513 39323974246300376844427885)
      ·
        refine ⟨14746490342362641316660457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39323974246300376844427885 14746490342362641316660457)
        ·
          refine ⟨11059867756771980987495343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14746490342362641316660457 11059867756771980987495343)
          ·
            refine ⟨16589801635157971481243015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11059867756771980987495343 16589801635157971481243015)
            ·
              refine ⟨24884702452736957221864523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16589801635157971481243015 24884702452736957221864523)
              ·
                refine ⟨37327053679105435832796785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24884702452736957221864523 37327053679105435832796785)
                ·
                  refine ⟨27995290259329076874597589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37327053679105435832796785 27995290259329076874597589)
                  ·
                    refine ⟨656139615453025239248381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 27995290259329076874597589 656139615453025239248381)
                    ·
                      rfl

theorem cell23_3833482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 1, 1, 2, 7].length) (baseStart_3833482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3833482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3833482 prefixEnd_3833482 := by exact prefixLift 3833482
  have htrace : WordTrace (prefixWord ++ tailWord_3833482) baseStart_3833482 baseEnd_3833482 := by
    simpa [prefixWord, tailWord_3833482, baseEnd_3833482] using wordTrace_append hprefix tailTrace_3833482
  have hstable : (prefixWord ++ tailWord_3833482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3833482).length < 2 ^ (prefixWord ++ tailWord_3833482).sum := by decide
  have hdescent : baseEnd_3833482 < baseStart_3833482 := by decide
  rcases family_descends (prefixWord ++ tailWord_3833482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3833496 : List Nat := [2, 1, 2, 4, 1, 2, 2, 3, 2, 1, 3]
def baseStart_3833496 : Nat := 118140960795 + 3833496 * 2 ^ 59
def prefixEnd_3833496 : Nat := 4983230072969 + 3 ^ 40 * 3833496 * 2
def baseEnd_3833496 : Nat := 1968426035088238662970079

theorem tailTrace_3833496 : CollatzResearch.WordTrace tailWord_3833496 prefixEnd_3833496 1968426035088238662970079 := by
  unfold tailWord_3833496
  simp only [CollatzResearch.WordTrace]
  refine ⟨69909542859953087918932171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93212723813270783891909561 69909542859953087918932171)
  ·
    refine ⟨104864314289929631878398257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69909542859953087918932171 104864314289929631878398257)
    ·
      refine ⟨78648235717447223908798693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104864314289929631878398257 78648235717447223908798693)
      ·
        refine ⟨14746544197021354482899755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 78648235717447223908798693 14746544197021354482899755)
        ·
          refine ⟨22119816295532031724349633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14746544197021354482899755 22119816295532031724349633)
          ·
            refine ⟨16589862221649023793262225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22119816295532031724349633 16589862221649023793262225)
            ·
              refine ⟨12442396666236767844946669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16589862221649023793262225 12442396666236767844946669)
              ·
                refine ⟨4665898749838787941855001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12442396666236767844946669 4665898749838787941855001)
                ·
                  refine ⟨3499424062379090956391251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4665898749838787941855001 3499424062379090956391251)
                  ·
                    refine ⟨5249136093568636434586877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3499424062379090956391251 5249136093568636434586877)
                    ·
                      refine ⟨1968426035088238662970079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5249136093568636434586877 1968426035088238662970079)
                      ·
                        rfl

theorem cell23_3833496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 2, 3, 2, 1, 3].length) (baseStart_3833496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3833496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3833496 prefixEnd_3833496 := by exact prefixLift 3833496
  have htrace : WordTrace (prefixWord ++ tailWord_3833496) baseStart_3833496 baseEnd_3833496 := by
    simpa [prefixWord, tailWord_3833496, baseEnd_3833496] using wordTrace_append hprefix tailTrace_3833496
  have hstable : (prefixWord ++ tailWord_3833496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3833496).length < 2 ^ (prefixWord ++ tailWord_3833496).sum := by decide
  have hdescent : baseEnd_3833496 < baseStart_3833496 := by decide
  rcases family_descends (prefixWord ++ tailWord_3833496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3833519 : List Nat := [1, 1, 2, 1, 2, 4, 1, 4, 1, 4, 2]
def baseStart_3833519 : Nat := 118140960795 + 3833519 * 2 ^ 59
def prefixEnd_3833519 : Nat := 4983230072969 + 3 ^ 40 * 3833519 * 2
def baseEnd_3833519 : Nat := 1968437845143292072982473

theorem tailTrace_3833519 : CollatzResearch.WordTrace tailWord_3833519 prefixEnd_3833519 1968437845143292072982473 := by
  unfold tailWord_3833519
  simp only [CollatzResearch.WordTrace]
  refine ⟨139819924598822850765951611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93213283065881900510634407 139819924598822850765951611)
  ·
    refine ⟨209729886898234276148927417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139819924598822850765951611 209729886898234276148927417)
    ·
      refine ⟨157297415173675707111695563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 209729886898234276148927417 157297415173675707111695563)
      ·
        refine ⟨235946122760513560667543345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157297415173675707111695563 235946122760513560667543345)
        ·
          refine ⟨176959592070385170500657509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 235946122760513560667543345 176959592070385170500657509)
          ·
            refine ⟨33179923513197219468873283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 176959592070385170500657509 33179923513197219468873283)
            ·
              refine ⟨49769885269795829203309925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33179923513197219468873283 49769885269795829203309925)
              ·
                refine ⟨9331853488086717975620611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 49769885269795829203309925 9331853488086717975620611)
                ·
                  refine ⟨13997780232130076963430917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9331853488086717975620611 13997780232130076963430917)
                  ·
                    refine ⟨2624583793524389430643297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13997780232130076963430917 2624583793524389430643297)
                    ·
                      refine ⟨1968437845143292072982473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2624583793524389430643297 1968437845143292072982473)
                      ·
                        rfl

theorem cell23_3833519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 1, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 1, 4, 1, 4, 2].length) (baseStart_3833519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3833519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3833519 prefixEnd_3833519 := by exact prefixLift 3833519
  have htrace : WordTrace (prefixWord ++ tailWord_3833519) baseStart_3833519 baseEnd_3833519 := by
    simpa [prefixWord, tailWord_3833519, baseEnd_3833519] using wordTrace_append hprefix tailTrace_3833519
  have hstable : (prefixWord ++ tailWord_3833519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3833519).length < 2 ^ (prefixWord ++ tailWord_3833519).sum := by decide
  have hdescent : baseEnd_3833519 < baseStart_3833519 := by decide
  rcases family_descends (prefixWord ++ tailWord_3833519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3833522 : List Nat := [3, 2, 1, 1, 1, 2, 2, 3, 2, 1, 5]
def baseStart_3833522 : Nat := 118140960795 + 3833522 * 2 ^ 59
def prefixEnd_3833522 : Nat := 4983230072969 + 3 ^ 40 * 3833522 * 2
def baseEnd_3833522 : Nat := 1968439385585255561244959

theorem tailTrace_3833522 : CollatzResearch.WordTrace tailWord_3833522 prefixEnd_3833522 1968439385585255561244959 := by
  unfold tailWord_3833522
  simp only [CollatzResearch.WordTrace]
  refine ⟨34955008504452995569577705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93213356011874654852207213 34955008504452995569577705)
  ·
    refine ⟨26216256378339746677183279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34955008504452995569577705 26216256378339746677183279)
    ·
      refine ⟨39324384567509620015774919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26216256378339746677183279 39324384567509620015774919)
      ·
        refine ⟨58986576851264430023662379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39324384567509620015774919 58986576851264430023662379)
        ·
          refine ⟨88479865276896645035493569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58986576851264430023662379 88479865276896645035493569)
          ·
            refine ⟨66359898957672483776620177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 88479865276896645035493569 66359898957672483776620177)
            ·
              refine ⟨49769924218254362832465133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66359898957672483776620177 49769924218254362832465133)
              ·
                refine ⟨18663721581845386062174425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49769924218254362832465133 18663721581845386062174425)
                ·
                  refine ⟨13997791186384039546630819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18663721581845386062174425 13997791186384039546630819)
                  ·
                    refine ⟨20996686779576059319946229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13997791186384039546630819 20996686779576059319946229)
                    ·
                      refine ⟨1968439385585255561244959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20996686779576059319946229 1968439385585255561244959)
                      ·
                        rfl

theorem cell23_3833522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 2, 3, 2, 1, 5].length) (baseStart_3833522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3833522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3833522 prefixEnd_3833522 := by exact prefixLift 3833522
  have htrace : WordTrace (prefixWord ++ tailWord_3833522) baseStart_3833522 baseEnd_3833522 := by
    simpa [prefixWord, tailWord_3833522, baseEnd_3833522] using wordTrace_append hprefix tailTrace_3833522
  have hstable : (prefixWord ++ tailWord_3833522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3833522).length < 2 ^ (prefixWord ++ tailWord_3833522).sum := by decide
  have hdescent : baseEnd_3833522 < baseStart_3833522 := by decide
  rcases family_descends (prefixWord ++ tailWord_3833522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3833536 : List Nat := [2, 1, 1, 2, 4, 1, 3, 1, 4, 2, 2]
def baseStart_3833536 : Nat := 118140960795 + 3833536 * 2 ^ 59
def prefixEnd_3833536 : Nat := 4983230072969 + 3 ^ 40 * 3833536 * 2
def baseEnd_3833536 : Nat := 1968446574314418506469895

theorem tailTrace_3833536 : CollatzResearch.WordTrace tailWord_3833536 prefixEnd_3833536 1968446574314418506469895 := by
  unfold tailWord_3833536
  simp only [CollatzResearch.WordTrace]
  refine ⟨69910272319880631334660231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93213696426507508446213641 69910272319880631334660231)
  ·
    refine ⟨104865408479820947001990347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69910272319880631334660231 104865408479820947001990347)
    ·
      refine ⟨157298112719731420502985521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104865408479820947001990347 157298112719731420502985521)
      ·
        refine ⟨117973584539798565377239141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 157298112719731420502985521 117973584539798565377239141)
        ·
          refine ⟨22120047101212231008232339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 117973584539798565377239141 22120047101212231008232339)
          ·
            refine ⟨33180070651818346512348509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22120047101212231008232339 33180070651818346512348509)
            ·
              refine ⟨12442526494431879942130691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33180070651818346512348509 12442526494431879942130691)
              ·
                refine ⟨18663789741647819913196037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12442526494431879942130691 18663789741647819913196037)
                ·
                  refine ⟨3499460576558966233724257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18663789741647819913196037 3499460576558966233724257)
                  ·
                    refine ⟨2624595432419224675293193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3499460576558966233724257 2624595432419224675293193)
                    ·
                      refine ⟨1968446574314418506469895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2624595432419224675293193 1968446574314418506469895)
                      ·
                        rfl

theorem cell23_3833536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 3, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 3, 1, 4, 2, 2].length) (baseStart_3833536 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3833536 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3833536 prefixEnd_3833536 := by exact prefixLift 3833536
  have htrace : WordTrace (prefixWord ++ tailWord_3833536) baseStart_3833536 baseEnd_3833536 := by
    simpa [prefixWord, tailWord_3833536, baseEnd_3833536] using wordTrace_append hprefix tailTrace_3833536
  have hstable : (prefixWord ++ tailWord_3833536).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3833536).length < 2 ^ (prefixWord ++ tailWord_3833536).sum := by decide
  have hdescent : baseEnd_3833536 < baseStart_3833536 := by decide
  rcases family_descends (prefixWord ++ tailWord_3833536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3833552 : List Nat := [2, 1, 1, 1, 1, 2, 1, 5, 1, 5, 3]
def baseStart_3833552 : Nat := 118140960795 + 3833552 * 2 ^ 59
def prefixEnd_3833552 : Nat := 4983230072969 + 3 ^ 40 * 3833552 * 2
def baseEnd_3833552 : Nat := 1968454790004890443869821

theorem tailTrace_3833552 : CollatzResearch.WordTrace tailWord_3833552 prefixEnd_3833552 1968454790004890443869821 := by
  unfold tailWord_3833552
  simp only [CollatzResearch.WordTrace]
  refine ⟨69910564103851648700951455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93214085471802198267935273 69910564103851648700951455)
  ·
    refine ⟨104865846155777473051427183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69910564103851648700951455 104865846155777473051427183)
    ·
      refine ⟨157298769233666209577140775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104865846155777473051427183 157298769233666209577140775)
      ·
        refine ⟨235948153850499314365711163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157298769233666209577140775 235948153850499314365711163)
        ·
          refine ⟨353922230775748971548566745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 235948153850499314365711163 353922230775748971548566745)
          ·
            refine ⟨265441673081811728661425059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 353922230775748971548566745 265441673081811728661425059)
            ·
              refine ⟨398162509622717592992137589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 265441673081811728661425059 398162509622717592992137589)
              ·
                refine ⟨37327735277129774343012899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 398162509622717592992137589 37327735277129774343012899)
                ·
                  refine ⟨55991602915694661514519349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37327735277129774343012899 55991602915694661514519349)
                  ·
                    refine ⟨5249212773346374516986189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 55991602915694661514519349 5249212773346374516986189)
                    ·
                      refine ⟨1968454790004890443869821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5249212773346374516986189 1968454790004890443869821)
                      ·
                        rfl

theorem cell23_3833552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 5, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 5, 1, 5, 3].length) (baseStart_3833552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3833552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3833552 prefixEnd_3833552 := by exact prefixLift 3833552
  have htrace : WordTrace (prefixWord ++ tailWord_3833552) baseStart_3833552 baseEnd_3833552 := by
    simpa [prefixWord, tailWord_3833552, baseEnd_3833552] using wordTrace_append hprefix tailTrace_3833552
  have hstable : (prefixWord ++ tailWord_3833552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3833552).length < 2 ^ (prefixWord ++ tailWord_3833552).sum := by decide
  have hdescent : baseEnd_3833552 < baseStart_3833552 := by decide
  rcases family_descends (prefixWord ++ tailWord_3833552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3833572 : List Nat := [2, 3, 1, 1, 1, 3, 1, 3, 1, 7]
def baseStart_3833572 : Nat := 118140960795 + 3833572 * 2 ^ 59
def prefixEnd_3833572 : Nat := 4983230072969 + 3 ^ 40 * 3833572 * 2
def baseEnd_3833572 : Nat := 656155019872660121873243

theorem tailTrace_3833572 : CollatzResearch.WordTrace tailWord_3833572 prefixEnd_3833572 656155019872660121873243 := by
  unfold tailWord_3833572
  simp only [CollatzResearch.WordTrace]
  refine ⟨69910928833815420408815485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93214571778420560545087313 69910928833815420408815485)
  ·
    refine ⟨26216598312680782653305807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69910928833815420408815485 26216598312680782653305807)
    ·
      refine ⟨39324897469021173979958711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26216598312680782653305807 39324897469021173979958711)
      ·
        refine ⟨58987346203531760969938067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39324897469021173979958711 58987346203531760969938067)
        ·
          refine ⟨88481019305297641454907101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58987346203531760969938067 88481019305297641454907101)
          ·
            refine ⟨33180382239486615545590163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 88481019305297641454907101 33180382239486615545590163)
            ·
              refine ⟨49770573359229923318385245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33180382239486615545590163 49770573359229923318385245)
              ·
                refine ⟨18663965009711221244394467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49770573359229923318385245 18663965009711221244394467)
                ·
                  refine ⟨27995947514566831866591701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18663965009711221244394467 27995947514566831866591701)
                  ·
                    refine ⟨656155019872660121873243, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 27995947514566831866591701 656155019872660121873243)
                    ·
                      rfl

theorem cell23_3833572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 1, 3, 1, 7].length) (baseStart_3833572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3833572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3833572 prefixEnd_3833572 := by exact prefixLift 3833572
  have htrace : WordTrace (prefixWord ++ tailWord_3833572) baseStart_3833572 baseEnd_3833572 := by
    simpa [prefixWord, tailWord_3833572, baseEnd_3833572] using wordTrace_append hprefix tailTrace_3833572
  have hstable : (prefixWord ++ tailWord_3833572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3833572).length < 2 ^ (prefixWord ++ tailWord_3833572).sum := by decide
  have hdescent : baseEnd_3833572 < baseStart_3833572 := by decide
  rcases family_descends (prefixWord ++ tailWord_3833572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3833576 : List Nat := [2, 1, 4, 1, 3, 1, 3, 3, 5]
def baseStart_3833576 : Nat := 118140960795 + 3833576 * 2 ^ 59
def prefixEnd_3833576 : Nat := 4983230072969 + 3 ^ 40 * 3833576 * 2
def baseEnd_3833576 : Nat := 218718568171177594441079

theorem tailTrace_3833576 : CollatzResearch.WordTrace tailWord_3833576 prefixEnd_3833576 218718568171177594441079 := by
  unfold tailWord_3833576
  simp only [CollatzResearch.WordTrace]
  refine ⟨69911001779808174750388291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93214669039744233000517721 69911001779808174750388291)
  ·
    refine ⟨104866502669712262125582437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69911001779808174750388291 104866502669712262125582437)
    ·
      refine ⟨19662469250571049148546707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 104866502669712262125582437 19662469250571049148546707)
      ·
        refine ⟨29493703875856573722820061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19662469250571049148546707 29493703875856573722820061)
        ·
          refine ⟨11060138953446215146057523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29493703875856573722820061 11060138953446215146057523)
          ·
            refine ⟨16590208430169322719086285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11060138953446215146057523 16590208430169322719086285)
            ·
              refine ⟨6221328161313496019657357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16590208430169322719086285 6221328161313496019657357)
              ·
                refine ⟨2332998060492561007371509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6221328161313496019657357 2332998060492561007371509)
                ·
                  refine ⟨218718568171177594441079, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2332998060492561007371509 218718568171177594441079)
                  ·
                    rfl

theorem cell23_3833576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 3, 3, 5].length) (baseStart_3833576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3833576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3833576 prefixEnd_3833576 := by exact prefixLift 3833576
  have htrace : WordTrace (prefixWord ++ tailWord_3833576) baseStart_3833576 baseEnd_3833576 := by
    simpa [prefixWord, tailWord_3833576, baseEnd_3833576] using wordTrace_append hprefix tailTrace_3833576
  have hstable : (prefixWord ++ tailWord_3833576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3833576).length < 2 ^ (prefixWord ++ tailWord_3833576).sum := by decide
  have hdescent : baseEnd_3833576 < baseStart_3833576 := by decide
  rcases family_descends (prefixWord ++ tailWord_3833576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3833592 : List Nat := [2, 1, 2, 1, 1, 2, 2, 2, 3, 3, 4]
def baseStart_3833592 : Nat := 118140960795 + 3833592 * 2 ^ 59
def prefixEnd_3833592 : Nat := 4983230072969 + 3 ^ 40 * 3833592 * 2
def baseEnd_3833592 : Nat := 1968475329231070287369637

theorem tailTrace_3833592 : CollatzResearch.WordTrace tailWord_3833592 prefixEnd_3833592 1968475329231070287369637 := by
  unfold tailWord_3833592
  simp only [CollatzResearch.WordTrace]
  refine ⟨69911293563779192116679515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93215058085038922822239353 69911293563779192116679515)
  ·
    refine ⟨104866940345668788175019273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69911293563779192116679515 104866940345668788175019273)
    ·
      refine ⟨78650205259251591131264455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104866940345668788175019273 78650205259251591131264455)
      ·
        refine ⟨117975307888877386696896683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78650205259251591131264455 117975307888877386696896683)
        ·
          refine ⟨176962961833316080045345025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117975307888877386696896683 176962961833316080045345025)
          ·
            refine ⟨132722221374987060034008769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 176962961833316080045345025 132722221374987060034008769)
            ·
              refine ⟨99541666031240295025506577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 132722221374987060034008769 99541666031240295025506577)
              ·
                refine ⟨74656249523430221269129933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 99541666031240295025506577 74656249523430221269129933)
                ·
                  refine ⟨27996093571286332975923725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 74656249523430221269129933 27996093571286332975923725)
                  ·
                    refine ⟨10498535089232374865971397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27996093571286332975923725 10498535089232374865971397)
                    ·
                      refine ⟨1968475329231070287369637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10498535089232374865971397 1968475329231070287369637)
                      ·
                        rfl

theorem cell23_3833592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 2, 3, 3, 4].length) (baseStart_3833592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3833592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3833592 prefixEnd_3833592 := by exact prefixLift 3833592
  have htrace : WordTrace (prefixWord ++ tailWord_3833592) baseStart_3833592 baseEnd_3833592 := by
    simpa [prefixWord, tailWord_3833592, baseEnd_3833592] using wordTrace_append hprefix tailTrace_3833592
  have hstable : (prefixWord ++ tailWord_3833592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3833592).length < 2 ^ (prefixWord ++ tailWord_3833592).sum := by decide
  have hdescent : baseEnd_3833592 < baseStart_3833592 := by decide
  rcases family_descends (prefixWord ++ tailWord_3833592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3833609 : List Nat := [1, 2, 1, 1, 3, 2, 1, 3, 1, 6, 2]
def baseStart_3833609 : Nat := 118140960795 + 3833609 * 2 ^ 59
def prefixEnd_3833609 : Nat := 4983230072969 + 3 ^ 40 * 3833609 * 2
def baseEnd_3833609 : Nat := 1968484058402196720857059

theorem tailTrace_3833609 : CollatzResearch.WordTrace tailWord_3833609 prefixEnd_3833609 1968484058402196720857059 := by
  unfold tailWord_3833609
  simp only [CollatzResearch.WordTrace]
  refine ⟨139823207168496796136727881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93215471445664530757818587 139823207168496796136727881)
  ·
    refine ⟨104867405376372597102545911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139823207168496796136727881 104867405376372597102545911)
    ·
      refine ⟨157301108064558895653818867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104867405376372597102545911 157301108064558895653818867)
      ·
        refine ⟨235951662096838343480728301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157301108064558895653818867 235951662096838343480728301)
        ·
          refine ⟨88481873286314378805273113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 235951662096838343480728301 88481873286314378805273113)
          ·
            refine ⟨66361404964735784103954835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 88481873286314378805273113 66361404964735784103954835)
            ·
              refine ⟨99542107447103676155932253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66361404964735784103954835 99542107447103676155932253)
              ·
                refine ⟨37328290292663878558474595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 99542107447103676155932253 37328290292663878558474595)
                ·
                  refine ⟨55992435438995817837711893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37328290292663878558474595 55992435438995817837711893)
                  ·
                    refine ⟨2624645411202928961142745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 55992435438995817837711893 2624645411202928961142745)
                    ·
                      refine ⟨1968484058402196720857059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2624645411202928961142745 1968484058402196720857059)
                      ·
                        rfl

theorem cell23_3833609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 3, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 3, 1, 6, 2].length) (baseStart_3833609 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3833609 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3833609 prefixEnd_3833609 := by exact prefixLift 3833609
  have htrace : WordTrace (prefixWord ++ tailWord_3833609) baseStart_3833609 baseEnd_3833609 := by
    simpa [prefixWord, tailWord_3833609, baseEnd_3833609] using wordTrace_append hprefix tailTrace_3833609
  have hstable : (prefixWord ++ tailWord_3833609).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3833609).length < 2 ^ (prefixWord ++ tailWord_3833609).sum := by decide
  have hdescent : baseEnd_3833609 < baseStart_3833609 := by decide
  rcases family_descends (prefixWord ++ tailWord_3833609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3833626 : List Nat := [3, 1, 1, 3, 2, 3, 2, 1, 2, 1, 4]
def baseStart_3833626 : Nat := 118140960795 + 3833626 * 2 ^ 59
def prefixEnd_3833626 : Nat := 4983230072969 + 3 ^ 40 * 3833626 * 2
def baseEnd_3833626 : Nat := 1968492787573323154344481

theorem tailTrace_3833626 : CollatzResearch.WordTrace tailWord_3833626 prefixEnd_3833626 1968492787573323154344481 := by
  unfold tailWord_3833626
  simp only [CollatzResearch.WordTrace]
  refine ⟨34955956802358802010024183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93215884806290138693397821 34955956802358802010024183)
  ·
    refine ⟨52433935203538203015036275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34955956802358802010024183 52433935203538203015036275)
    ·
      refine ⟨78650902805307304522554413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52433935203538203015036275 78650902805307304522554413)
      ·
        refine ⟨29494088551990239195957905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 78650902805307304522554413 29494088551990239195957905)
        ·
          refine ⟨22120566413992679396968429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29494088551990239195957905 22120566413992679396968429)
          ·
            refine ⟨8295212405247254773863161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22120566413992679396968429 8295212405247254773863161)
            ·
              refine ⟨6221409303935441080397371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8295212405247254773863161 6221409303935441080397371)
              ·
                refine ⟨9332113955903161620596057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6221409303935441080397371 9332113955903161620596057)
                ·
                  refine ⟨6999085466927371215447043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9332113955903161620596057 6999085466927371215447043)
                  ·
                    refine ⟨10498628200391056823170565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6999085466927371215447043 10498628200391056823170565)
                    ·
                      refine ⟨1968492787573323154344481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10498628200391056823170565 1968492787573323154344481)
                      ·
                        rfl

theorem cell23_3833626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 3, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 3, 2, 1, 2, 1, 4].length) (baseStart_3833626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3833626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3833626 prefixEnd_3833626 := by exact prefixLift 3833626
  have htrace : WordTrace (prefixWord ++ tailWord_3833626) baseStart_3833626 baseEnd_3833626 := by
    simpa [prefixWord, tailWord_3833626, baseEnd_3833626] using wordTrace_append hprefix tailTrace_3833626
  have hstable : (prefixWord ++ tailWord_3833626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3833626).length < 2 ^ (prefixWord ++ tailWord_3833626).sum := by decide
  have hdescent : baseEnd_3833626 < baseStart_3833626 := by decide
  rcases family_descends (prefixWord ++ tailWord_3833626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3833649 : List Nat := [1, 2, 2, 3, 2, 2, 1, 4, 6]
def baseStart_3833649 : Nat := 118140960795 + 3833649 * 2 ^ 59
def prefixEnd_3833649 : Nat := 4983230072969 + 3 ^ 40 * 3833649 * 2
def baseEnd_3833649 : Nat := 218722733069819618261875

theorem tailTrace_3833649 : CollatzResearch.WordTrace tailWord_3833649 prefixEnd_3833649 218722733069819618261875 := by
  unfold tailWord_3833649
  simp only [CollatzResearch.WordTrace]
  refine ⟨139824666088351882968184001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93216444058901255312122667 139824666088351882968184001)
  ·
    refine ⟨104868499566263912226138001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139824666088351882968184001 104868499566263912226138001)
    ·
      refine ⟨78651374674697934169603501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104868499566263912226138001 78651374674697934169603501)
      ·
        refine ⟨29494265503011725313601313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 78651374674697934169603501 29494265503011725313601313)
        ·
          refine ⟨22120699127258793985200985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29494265503011725313601313 22120699127258793985200985)
          ·
            refine ⟨16590524345444095488900739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22120699127258793985200985 16590524345444095488900739)
            ·
              refine ⟨24885786518166143233351109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16590524345444095488900739 24885786518166143233351109)
              ·
                refine ⟨4666084972156151856253333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24885786518166143233351109 4666084972156151856253333)
                ·
                  refine ⟨218722733069819618261875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4666084972156151856253333 218722733069819618261875)
                  ·
                    rfl

theorem cell23_3833649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 1, 4, 6].length) (baseStart_3833649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3833649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3833649 prefixEnd_3833649 := by exact prefixLift 3833649
  have htrace : WordTrace (prefixWord ++ tailWord_3833649) baseStart_3833649 baseEnd_3833649 := by
    simpa [prefixWord, tailWord_3833649, baseEnd_3833649] using wordTrace_append hprefix tailTrace_3833649
  have hstable : (prefixWord ++ tailWord_3833649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3833649).length < 2 ^ (prefixWord ++ tailWord_3833649).sum := by decide
  have hdescent : baseEnd_3833649 < baseStart_3833649 := by decide
  rcases family_descends (prefixWord ++ tailWord_3833649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3833670 : List Nat := [6, 1, 1, 2, 1, 2, 1, 2, 3, 4]
def baseStart_3833670 : Nat := 118140960795 + 3833670 * 2 ^ 59
def prefixEnd_3833670 : Nat := 4983230072969 + 3 ^ 40 * 3833670 * 2
def baseEnd_3833670 : Nat := 656171793574040327398093

theorem tailTrace_3833670 : CollatzResearch.WordTrace tailWord_3833670 prefixEnd_3833670 656171793574040327398093 := by
  unfold tailWord_3833670
  simp only [CollatzResearch.WordTrace]
  refine ⟨4369544750664868861084327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 93216954680850535703132309 4369544750664868861084327)
  ·
    refine ⟨6554317125997303291626491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4369544750664868861084327 6554317125997303291626491)
    ·
      refine ⟨9831475688995954937439737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6554317125997303291626491 9831475688995954937439737)
      ·
        refine ⟨7373606766746966203079803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9831475688995954937439737 7373606766746966203079803)
        ·
          refine ⟨11060410150120449304619705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7373606766746966203079803 11060410150120449304619705)
          ·
            refine ⟨8295307612590336978464779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11060410150120449304619705 8295307612590336978464779)
            ·
              refine ⟨12442961418885505467697169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8295307612590336978464779 12442961418885505467697169)
              ·
                refine ⟨9332221064164129100772877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12442961418885505467697169 9332221064164129100772877)
                ·
                  refine ⟨3499582899061548412789829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9332221064164129100772877 3499582899061548412789829)
                  ·
                    refine ⟨656171793574040327398093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3499582899061548412789829 656171793574040327398093)
                    ·
                      rfl

theorem cell23_3833670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 2, 1, 2, 3, 4].length) (baseStart_3833670 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3833670 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3833670 prefixEnd_3833670 := by exact prefixLift 3833670
  have htrace : WordTrace (prefixWord ++ tailWord_3833670) baseStart_3833670 baseEnd_3833670 := by
    simpa [prefixWord, tailWord_3833670, baseEnd_3833670] using wordTrace_append hprefix tailTrace_3833670
  have hstable : (prefixWord ++ tailWord_3833670).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3833670).length < 2 ^ (prefixWord ++ tailWord_3833670).sum := by decide
  have hdescent : baseEnd_3833670 < baseStart_3833670 := by decide
  rcases family_descends (prefixWord ++ tailWord_3833670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3833696 : List Nat := [2, 1, 1, 3, 3, 3, 1, 3, 1, 5]
def baseStart_3833696 : Nat := 118140960795 + 3833696 * 2 ^ 59
def prefixEnd_3833696 : Nat := 4983230072969 + 3 ^ 40 * 3833696 * 2
def baseEnd_3833696 : Nat := 656176243739712626823053

theorem tailTrace_3833696 : CollatzResearch.WordTrace tailWord_3833696 prefixEnd_3833696 656176243739712626823053 := by
  unfold tailWord_3833696
  simp only [CollatzResearch.WordTrace]
  refine ⟨69913190159590804997572471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93217586879454406663429961 69913190159590804997572471)
  ·
    refine ⟨104869785239386207496358707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69913190159590804997572471 104869785239386207496358707)
    ·
      refine ⟨157304677859079311244538061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104869785239386207496358707 157304677859079311244538061)
      ·
        refine ⟨58989254197154741716701773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 157304677859079311244538061 58989254197154741716701773)
        ·
          refine ⟨22120970323933028143763165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58989254197154741716701773 22120970323933028143763165)
          ·
            refine ⟨8295363871474885553911187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22120970323933028143763165 8295363871474885553911187)
            ·
              refine ⟨12443045807212328330866781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8295363871474885553911187 12443045807212328330866781)
              ·
                refine ⟨4666142177704623124075043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12443045807212328330866781 4666142177704623124075043)
                ·
                  refine ⟨6999213266556934686112565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4666142177704623124075043 6999213266556934686112565)
                  ·
                    refine ⟨656176243739712626823053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6999213266556934686112565 656176243739712626823053)
                    ·
                      rfl

theorem cell23_3833696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 3, 1, 3, 1, 5].length) (baseStart_3833696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3833696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3833696 prefixEnd_3833696 := by exact prefixLift 3833696
  have htrace : WordTrace (prefixWord ++ tailWord_3833696) baseStart_3833696 baseEnd_3833696 := by
    simpa [prefixWord, tailWord_3833696, baseEnd_3833696] using wordTrace_append hprefix tailTrace_3833696
  have hstable : (prefixWord ++ tailWord_3833696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3833696).length < 2 ^ (prefixWord ++ tailWord_3833696).sum := by decide
  have hdescent : baseEnd_3833696 < baseStart_3833696 := by decide
  rcases family_descends (prefixWord ++ tailWord_3833696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3833709 : List Nat := [1, 5, 1, 1, 1, 1, 2, 2, 3, 6]
def baseStart_3833709 : Nat := 118140960795 + 3833709 * 2 ^ 59
def prefixEnd_3833709 : Nat := 4983230072969 + 3 ^ 40 * 3833709 * 2
def baseEnd_3833709 : Nat := 656178468822548776535533

theorem tailTrace_3833709 : CollatzResearch.WordTrace tailWord_3833709 prefixEnd_3833709 656178468822548776535533 := by
  unfold tailWord_3833709
  simp only [CollatzResearch.WordTrace]
  refine ⟨139826854468134513215368181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93217902978756342143578787 139826854468134513215368181)
  ·
    refine ⟨13108767606387610613940767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 139826854468134513215368181 13108767606387610613940767)
    ·
      refine ⟨19663151409581415920911151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13108767606387610613940767 19663151409581415920911151)
      ·
        refine ⟨29494727114372123881366727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19663151409581415920911151 29494727114372123881366727)
        ·
          refine ⟨44242090671558185822050091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29494727114372123881366727 44242090671558185822050091)
          ·
            refine ⟨66363136007337278733075137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44242090671558185822050091 66363136007337278733075137)
            ·
              refine ⟨49772352005502959049806353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66363136007337278733075137 49772352005502959049806353)
              ·
                refine ⟨37329264004127219287354765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49772352005502959049806353 37329264004127219287354765)
                ·
                  refine ⟨13998474001547707232758037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37329264004127219287354765 13998474001547707232758037)
                  ·
                    refine ⟨656178468822548776535533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13998474001547707232758037 656178468822548776535533)
                    ·
                      rfl

theorem cell23_3833709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 2, 2, 3, 6].length) (baseStart_3833709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3833709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3833709 prefixEnd_3833709 := by exact prefixLift 3833709
  have htrace : WordTrace (prefixWord ++ tailWord_3833709) baseStart_3833709 baseEnd_3833709 := by
    simpa [prefixWord, tailWord_3833709, baseEnd_3833709] using wordTrace_append hprefix tailTrace_3833709
  have hstable : (prefixWord ++ tailWord_3833709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3833709).length < 2 ^ (prefixWord ++ tailWord_3833709).sum := by decide
  have hdescent : baseEnd_3833709 < baseStart_3833709 := by decide
  rcases family_descends (prefixWord ++ tailWord_3833709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3833710 : List Nat := [4, 1, 2, 3, 1, 2, 2, 1, 3, 1, 3]
def baseStart_3833710 : Nat := 118140960795 + 3833710 * 2 ^ 59
def prefixEnd_3833710 : Nat := 4983230072969 + 3 ^ 40 * 3833710 * 2
def baseEnd_3833710 : Nat := 1968535919948300825694095

theorem tailTrace_3833710 : CollatzResearch.WordTrace tailWord_3833710 prefixEnd_3833710 1968535919948300825694095 := by
  unfold tailWord_3833710
  simp only [CollatzResearch.WordTrace]
  refine ⟨17478361367641361298269323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 93217927294087260257436389 17478361367641361298269323)
  ·
    refine ⟨26217542051462041947403985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17478361367641361298269323 26217542051462041947403985)
    ·
      refine ⟨19663156538596531460552989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26217542051462041947403985 19663156538596531460552989)
      ·
        refine ⟨7373683701973699297707371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19663156538596531460552989 7373683701973699297707371)
        ·
          refine ⟨11060525552960548946561057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7373683701973699297707371 11060525552960548946561057)
          ·
            refine ⟨8295394164720411709920793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11060525552960548946561057 8295394164720411709920793)
            ·
              refine ⟨6221545623540308782440595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8295394164720411709920793 6221545623540308782440595)
              ·
                refine ⟨9332318435310463173660893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6221545623540308782440595 9332318435310463173660893)
                ·
                  refine ⟨3499619413241423690122835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9332318435310463173660893 3499619413241423690122835)
                  ·
                    refine ⟨5249429119862135535184253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3499619413241423690122835 5249429119862135535184253)
                    ·
                      refine ⟨1968535919948300825694095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5249429119862135535184253 1968535919948300825694095)
                      ·
                        rfl

theorem cell23_3833710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 2, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 2, 2, 1, 3, 1, 3].length) (baseStart_3833710 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3833710 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3833710 prefixEnd_3833710 := by exact prefixLift 3833710
  have htrace : WordTrace (prefixWord ++ tailWord_3833710) baseStart_3833710 baseEnd_3833710 := by
    simpa [prefixWord, tailWord_3833710, baseEnd_3833710] using wordTrace_append hprefix tailTrace_3833710
  have hstable : (prefixWord ++ tailWord_3833710).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3833710).length < 2 ^ (prefixWord ++ tailWord_3833710).sum := by decide
  have hdescent : baseEnd_3833710 < baseStart_3833710 := by decide
  rcases family_descends (prefixWord ++ tailWord_3833710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3833733 : List Nat := [1, 3, 1, 1, 3, 2, 1, 4, 3, 2, 2]
def baseStart_3833733 : Nat := 118140960795 + 3833733 * 2 ^ 59
def prefixEnd_3833733 : Nat := 4983230072969 + 3 ^ 40 * 3833733 * 2
def baseEnd_3833733 : Nat := 1968547730003354235706489

theorem tailTrace_3833733 : CollatzResearch.WordTrace tailWord_3833733 prefixEnd_3833733 1968547730003354235706489 := by
  unfold tailWord_3833733
  simp only [CollatzResearch.WordTrace]
  refine ⟨139827729820047565314241853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93218486546698376876161235 139827729820047565314241853)
  ·
    refine ⟨52435398682517836992840695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 139827729820047565314241853 52435398682517836992840695)
    ·
      refine ⟨78653098023776755489261043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52435398682517836992840695 78653098023776755489261043)
      ·
        refine ⟨117979647035665133233891565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78653098023776755489261043 117979647035665133233891565)
        ·
          refine ⟨44242367638374424962709337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 117979647035665133233891565 44242367638374424962709337)
          ·
            refine ⟨33181775728780818722032003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44242367638374424962709337 33181775728780818722032003)
            ·
              refine ⟨49772663593171228083048005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33181775728780818722032003 49772663593171228083048005)
              ·
                refine ⟨9332374423719605265571501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 49772663593171228083048005 9332374423719605265571501)
                ·
                  refine ⟨3499640408894851974589313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9332374423719605265571501 3499640408894851974589313)
                  ·
                    refine ⟨2624730306671138980941985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3499640408894851974589313 2624730306671138980941985)
                    ·
                      refine ⟨1968547730003354235706489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2624730306671138980941985 1968547730003354235706489)
                      ·
                        rfl

theorem cell23_3833733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 1, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 1, 4, 3, 2, 2].length) (baseStart_3833733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3833733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3833733 prefixEnd_3833733 := by exact prefixLift 3833733
  have htrace : WordTrace (prefixWord ++ tailWord_3833733) baseStart_3833733 baseEnd_3833733 := by
    simpa [prefixWord, tailWord_3833733, baseEnd_3833733] using wordTrace_append hprefix tailTrace_3833733
  have hstable : (prefixWord ++ tailWord_3833733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3833733).length < 2 ^ (prefixWord ++ tailWord_3833733).sum := by decide
  have hdescent : baseEnd_3833733 < baseStart_3833733 := by decide
  rcases family_descends (prefixWord ++ tailWord_3833733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3833756 : List Nat := [2, 2, 3, 3, 1, 3, 9]
def baseStart_3833756 : Nat := 118140960795 + 3833756 * 2 ^ 59
def prefixEnd_3833756 : Nat := 4983230072969 + 3 ^ 40 * 3833756 * 2
def baseEnd_3833756 : Nat := 24303204198251946243443

theorem tailTrace_3833756 : CollatzResearch.WordTrace tailWord_3833756 prefixEnd_3833756 24303204198251946243443 := by
  unfold tailWord_3833756
  simp only [CollatzResearch.WordTrace]
  refine ⟨69914284349482120121164561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93219045799309493494886081 69914284349482120121164561)
  ·
    refine ⟨52435713262111590090873421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69914284349482120121164561 52435713262111590090873421)
    ·
      refine ⟨19663392473291846284077533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52435713262111590090873421 19663392473291846284077533)
      ·
        refine ⟨7373772177484442356529075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19663392473291846284077533 7373772177484442356529075)
        ·
          refine ⟨11060658266226663534793613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7373772177484442356529075 11060658266226663534793613)
          ·
            refine ⟨4147746849834998825547605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11060658266226663534793613 4147746849834998825547605)
            ·
              refine ⟨24303204198251946243443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 4147746849834998825547605 24303204198251946243443)
              ·
                rfl

theorem cell23_3833756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 3, 9].length) (baseStart_3833756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3833756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3833756 prefixEnd_3833756 := by exact prefixLift 3833756
  have htrace : WordTrace (prefixWord ++ tailWord_3833756) baseStart_3833756 baseEnd_3833756 := by
    simpa [prefixWord, tailWord_3833756, baseEnd_3833756] using wordTrace_append hprefix tailTrace_3833756
  have hstable : (prefixWord ++ tailWord_3833756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3833756).length < 2 ^ (prefixWord ++ tailWord_3833756).sum := by decide
  have hdescent : baseEnd_3833756 < baseStart_3833756 := by decide
  rcases family_descends (prefixWord ++ tailWord_3833756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3833767 : List Nat := [1, 1, 6, 1, 2, 3, 1, 1, 3, 2, 2]
def baseStart_3833767 : Nat := 118140960795 + 3833767 * 2 ^ 59
def prefixEnd_3833767 : Nat := 4983230072969 + 3 ^ 40 * 3833767 * 2
def baseEnd_3833767 : Nat := 1968565188345607102681333

theorem tailTrace_3833767 : CollatzResearch.WordTrace tailWord_3833767 prefixEnd_3833767 1968565188345607102681333 := by
  unfold tailWord_3833767
  simp only [CollatzResearch.WordTrace]
  refine ⟨139828969901924389120979555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93219313267949592747319703 139828969901924389120979555)
  ·
    refine ⟨209743454852886583681469333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139828969901924389120979555 209743454852886583681469333)
    ·
      refine ⟨9831724446229058610068875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 209743454852886583681469333 9831724446229058610068875)
      ·
        refine ⟨14747586669343587915103313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9831724446229058610068875 14747586669343587915103313)
        ·
          refine ⟨11060690002007690936327485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14747586669343587915103313 11060690002007690936327485)
          ·
            refine ⟨4147758750752884101122807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11060690002007690936327485 4147758750752884101122807)
            ·
              refine ⟨6221638126129326151684211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4147758750752884101122807 6221638126129326151684211)
              ·
                refine ⟨9332457189193989227526317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6221638126129326151684211 9332457189193989227526317)
                ·
                  refine ⟨3499671445947745960322369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9332457189193989227526317 3499671445947745960322369)
                  ·
                    refine ⟨2624753584460809470241777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3499671445947745960322369 2624753584460809470241777)
                    ·
                      refine ⟨1968565188345607102681333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2624753584460809470241777 1968565188345607102681333)
                      ·
                        rfl

theorem cell23_3833767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 3, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 3, 1, 1, 3, 2, 2].length) (baseStart_3833767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3833767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3833767 prefixEnd_3833767 := by exact prefixLift 3833767
  have htrace : WordTrace (prefixWord ++ tailWord_3833767) baseStart_3833767 baseEnd_3833767 := by
    simpa [prefixWord, tailWord_3833767, baseEnd_3833767] using wordTrace_append hprefix tailTrace_3833767
  have hstable : (prefixWord ++ tailWord_3833767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3833767).length < 2 ^ (prefixWord ++ tailWord_3833767).sum := by decide
  have hdescent : baseEnd_3833767 < baseStart_3833767 := by decide
  rcases family_descends (prefixWord ++ tailWord_3833767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3833799 : List Nat := [1, 1, 4, 1, 1, 2, 1, 2, 4, 6]
def baseStart_3833799 : Nat := 118140960795 + 3833799 * 2 ^ 59
def prefixEnd_3833799 : Nat := 4983230072969 + 3 ^ 40 * 3833799 * 2
def baseEnd_3833799 : Nat := 656193873242183659160395

theorem tailTrace_3833799 : CollatzResearch.WordTrace tailWord_3833799 prefixEnd_3833799 656193873242183659160395 := by
  unfold tailWord_3833799
  simp only [CollatzResearch.WordTrace]
  refine ⟨139830137037808458586144451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93220091358538972390762967 139830137037808458586144451)
  ·
    refine ⟨209745205556712687879216677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139830137037808458586144451 209745205556712687879216677)
    ·
      refine ⟨39327226041883628977353127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 209745205556712687879216677 39327226041883628977353127)
      ·
        refine ⟨58990839062825443466029691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39327226041883628977353127 58990839062825443466029691)
        ·
          refine ⟨88486258594238165199044537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58990839062825443466029691 88486258594238165199044537)
          ·
            refine ⟨66364693945678623899283403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 88486258594238165199044537 66364693945678623899283403)
            ·
              refine ⟨99547040918517935848925105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66364693945678623899283403 99547040918517935848925105)
              ·
                refine ⟨74660280688888451886693829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 99547040918517935848925105 74660280688888451886693829)
                ·
                  refine ⟨13998802629166584728755093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 74660280688888451886693829 13998802629166584728755093)
                  ·
                    refine ⟨656193873242183659160395, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13998802629166584728755093 656193873242183659160395)
                    ·
                      rfl

theorem cell23_3833799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 2, 4, 6].length) (baseStart_3833799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3833799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3833799 prefixEnd_3833799 := by exact prefixLift 3833799
  have htrace : WordTrace (prefixWord ++ tailWord_3833799) baseStart_3833799 baseEnd_3833799 := by
    simpa [prefixWord, tailWord_3833799, baseEnd_3833799] using wordTrace_append hprefix tailTrace_3833799
  have hstable : (prefixWord ++ tailWord_3833799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3833799).length < 2 ^ (prefixWord ++ tailWord_3833799).sum := by decide
  have hdescent : baseEnd_3833799 < baseStart_3833799 := by decide
  rcases family_descends (prefixWord ++ tailWord_3833799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3833809 : List Nat := [1, 2, 2, 1, 2, 1, 2, 3, 1, 3, 5]
def baseStart_3833809 : Nat := 118140960795 + 3833809 * 2 ^ 59
def prefixEnd_3833809 : Nat := 4983230072969 + 3 ^ 40 * 3833809 * 2
def baseEnd_3833809 : Nat := 1968586754533095938356139

theorem tailTrace_3833809 : CollatzResearch.WordTrace tailWord_3833809 prefixEnd_3833809 1968586754533095938356139 := by
  unfold tailWord_3833809
  simp only [CollatzResearch.WordTrace]
  refine ⟨139830501767772230294008481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93220334511848153529338987 139830501767772230294008481)
  ·
    refine ⟨104872876325829172720506361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139830501767772230294008481 104872876325829172720506361)
    ·
      refine ⟨78654657244371879540379771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104872876325829172720506361 78654657244371879540379771)
      ·
        refine ⟨117981985866557819310569657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78654657244371879540379771 117981985866557819310569657)
        ·
          refine ⟨88486489399918364482927243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 117981985866557819310569657 88486489399918364482927243)
          ·
            refine ⟨132729734099877546724390865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88486489399918364482927243 132729734099877546724390865)
            ·
              refine ⟨99547300574908160043293149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 132729734099877546724390865 99547300574908160043293149)
              ·
                refine ⟨37330237715590560016234931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 99547300574908160043293149 37330237715590560016234931)
                ·
                  refine ⟨55995356573385840024352397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37330237715590560016234931 55995356573385840024352397)
                  ·
                    refine ⟨20998258715019690009132149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 55995356573385840024352397 20998258715019690009132149)
                    ·
                      refine ⟨1968586754533095938356139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20998258715019690009132149 1968586754533095938356139)
                      ·
                        rfl

theorem cell23_3833809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 3, 1, 3, 5].length) (baseStart_3833809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3833809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3833809 prefixEnd_3833809 := by exact prefixLift 3833809
  have htrace : WordTrace (prefixWord ++ tailWord_3833809) baseStart_3833809 baseEnd_3833809 := by
    simpa [prefixWord, tailWord_3833809, baseEnd_3833809] using wordTrace_append hprefix tailTrace_3833809
  have hstable : (prefixWord ++ tailWord_3833809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3833809).length < 2 ^ (prefixWord ++ tailWord_3833809).sum := by decide
  have hdescent : baseEnd_3833809 < baseStart_3833809 := by decide
  rcases family_descends (prefixWord ++ tailWord_3833809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3833840 : List Nat := [2, 1, 1, 1, 3, 2, 4, 3, 2, 2, 2]
def baseStart_3833840 : Nat := 118140960795 + 3833840 * 2 ^ 59
def prefixEnd_3833840 : Nat := 4983230072969 + 3 ^ 40 * 3833840 * 2
def baseEnd_3833840 : Nat := 1968602672433385317068497

theorem tailTrace_3833840 : CollatzResearch.WordTrace tailWord_3833840 prefixEnd_3833840 1968602672433385317068497 := by
  unfold tailWord_3833840
  simp only [CollatzResearch.WordTrace]
  refine ⟨69915816215329961294193487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93221088287106615058924649 69915816215329961294193487)
  ·
    refine ⟨104873724322994941941290231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69915816215329961294193487 104873724322994941941290231)
    ·
      refine ⟨157310586484492412911935347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104873724322994941941290231 157310586484492412911935347)
      ·
        refine ⟨235965879726738619367903021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157310586484492412911935347 235965879726738619367903021)
        ·
          refine ⟨88487204897526982262963633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 235965879726738619367903021 88487204897526982262963633)
          ·
            refine ⟨66365403673145236697222725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 88487204897526982262963633 66365403673145236697222725)
            ·
              refine ⟨12443513188714731880729261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 66365403673145236697222725 12443513188714731880729261)
              ·
                refine ⟨4666317445768024455273473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12443513188714731880729261 4666317445768024455273473)
                ·
                  refine ⟨3499738084326018341455105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4666317445768024455273473 3499738084326018341455105)
                  ·
                    refine ⟨2624803563244513756091329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3499738084326018341455105 2624803563244513756091329)
                    ·
                      refine ⟨1968602672433385317068497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2624803563244513756091329 1968602672433385317068497)
                      ·
                        rfl

theorem cell23_3833840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 4, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 4, 3, 2, 2, 2].length) (baseStart_3833840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3833840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3833840 prefixEnd_3833840 := by exact prefixLift 3833840
  have htrace : WordTrace (prefixWord ++ tailWord_3833840) baseStart_3833840 baseEnd_3833840 := by
    simpa [prefixWord, tailWord_3833840, baseEnd_3833840] using wordTrace_append hprefix tailTrace_3833840
  have hstable : (prefixWord ++ tailWord_3833840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3833840).length < 2 ^ (prefixWord ++ tailWord_3833840).sum := by decide
  have hdescent : baseEnd_3833840 < baseStart_3833840 := by decide
  rcases family_descends (prefixWord ++ tailWord_3833840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3833863 : List Nat := [1, 1, 4, 3, 1, 2, 1, 5, 5]
def baseStart_3833863 : Nat := 118140960795 + 3833863 * 2 ^ 59
def prefixEnd_3833863 : Nat := 4983230072969 + 3 ^ 40 * 3833863 * 2
def baseEnd_3833863 : Nat := 218734942498715414120099

theorem tailTrace_3833863 : CollatzResearch.WordTrace tailWord_3833863 prefixEnd_3833863 218734942498715414120099 := by
  unfold tailWord_3833863
  simp only [CollatzResearch.WordTrace]
  refine ⟨139832471309576597516474243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93221647539717731677649495 139832471309576597516474243)
  ·
    refine ⟨209748706964364896274711365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139832471309576597516474243 209748706964364896274711365)
    ·
      refine ⟨39327882555818418051508381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 209748706964364896274711365 39327882555818418051508381)
      ·
        refine ⟨14747955958431906769315643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39327882555818418051508381 14747955958431906769315643)
        ·
          refine ⟨22121933937647860153973465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14747955958431906769315643 22121933937647860153973465)
          ·
            refine ⟨16591450453235895115480099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22121933937647860153973465 16591450453235895115480099)
            ·
              refine ⟨24887175679853842673220149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16591450453235895115480099 24887175679853842673220149)
              ·
                refine ⟨2333172719986297750614389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 24887175679853842673220149 2333172719986297750614389)
                ·
                  refine ⟨218734942498715414120099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2333172719986297750614389 218734942498715414120099)
                  ·
                    rfl

theorem cell23_3833863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 1, 5, 5].length) (baseStart_3833863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3833863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3833863 prefixEnd_3833863 := by exact prefixLift 3833863
  have htrace : WordTrace (prefixWord ++ tailWord_3833863) baseStart_3833863 baseEnd_3833863 := by
    simpa [prefixWord, tailWord_3833863, baseEnd_3833863] using wordTrace_append hprefix tailTrace_3833863
  have hstable : (prefixWord ++ tailWord_3833863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3833863).length < 2 ^ (prefixWord ++ tailWord_3833863).sum := by decide
  have hdescent : baseEnd_3833863 < baseStart_3833863 := by decide
  rcases family_descends (prefixWord ++ tailWord_3833863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3833956 : List Nat := [2, 3, 1, 1, 2, 1, 2, 2, 1, 2, 6]
def baseStart_3833956 : Nat := 118140960795 + 3833956 * 2 ^ 59
def prefixEnd_3833956 : Nat := 4983230072969 + 3 ^ 40 * 3833956 * 2
def baseEnd_3833956 : Nat := 1968662236189306863217963

theorem tailTrace_3833956 : CollatzResearch.WordTrace tailWord_3833956 prefixEnd_3833956 1968662236189306863217963 := by
  unfold tailWord_3833956
  simp only [CollatzResearch.WordTrace]
  refine ⟨69917931649119837199804861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93223908865493116266406481 69917931649119837199804861)
  ·
    refine ⟨26219224368419938949926823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69917931649119837199804861 26219224368419938949926823)
    ·
      refine ⟨39328836552629908424890235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26219224368419938949926823 39328836552629908424890235)
      ·
        refine ⟨58993254828944862637335353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39328836552629908424890235 58993254828944862637335353)
        ·
          refine ⟨44244941121708646978001515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58993254828944862637335353 44244941121708646978001515)
          ·
            refine ⟨66367411682562970467002273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44244941121708646978001515 66367411682562970467002273)
            ·
              refine ⟨49775558761922227850251705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66367411682562970467002273 49775558761922227850251705)
              ·
                refine ⟨37331669071441670887688779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49775558761922227850251705 37331669071441670887688779)
                ·
                  refine ⟨55997503607162506331533169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37331669071441670887688779 55997503607162506331533169)
                  ·
                    refine ⟨41998127705371879748649877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 55997503607162506331533169 41998127705371879748649877)
                    ·
                      refine ⟨1968662236189306863217963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 41998127705371879748649877 1968662236189306863217963)
                      ·
                        rfl

theorem cell23_3833956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 2, 2, 1, 2, 6].length) (baseStart_3833956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3833956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3833956 prefixEnd_3833956 := by exact prefixLift 3833956
  have htrace : WordTrace (prefixWord ++ tailWord_3833956) baseStart_3833956 baseEnd_3833956 := by
    simpa [prefixWord, tailWord_3833956, baseEnd_3833956] using wordTrace_append hprefix tailTrace_3833956
  have hstable : (prefixWord ++ tailWord_3833956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3833956).length < 2 ^ (prefixWord ++ tailWord_3833956).sum := by decide
  have hdescent : baseEnd_3833956 < baseStart_3833956 := by decide
  rcases family_descends (prefixWord ++ tailWord_3833956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3834003 : List Nat := [1, 1, 1, 2, 1, 2, 3, 2, 2, 6, 2]
def baseStart_3834003 : Nat := 118140960795 + 3834003 * 2 ^ 59
def prefixEnd_3834003 : Nat := 4983230072969 + 3 ^ 40 * 3834003 * 2
def baseEnd_3834003 : Nat := 1968686369780068179330247

theorem tailTrace_3834003 : CollatzResearch.WordTrace tailWord_3834003 prefixEnd_3834003 1968686369780068179330247 := by
  unfold tailWord_3834003
  simp only [CollatzResearch.WordTrace]
  refine ⟨139837577529069401426570663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93225051686046267617713775 139837577529069401426570663)
  ·
    refine ⟨209756366293604102139855995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139837577529069401426570663 209756366293604102139855995)
    ·
      refine ⟨314634549440406153209783993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209756366293604102139855995 314634549440406153209783993)
      ·
        refine ⟨235975912080304614907337995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 314634549440406153209783993 235975912080304614907337995)
        ·
          refine ⟨353963868120456922361006993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 235975912080304614907337995 353963868120456922361006993)
          ·
            refine ⟨265472901090342691770755245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 353963868120456922361006993 265472901090342691770755245)
            ·
              refine ⟨99552337908878509414033217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 265472901090342691770755245 99552337908878509414033217)
              ·
                refine ⟨74664253431658882060524913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 99552337908878509414033217 74664253431658882060524913)
                ·
                  refine ⟨55998190073744161545393685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 74664253431658882060524913 55998190073744161545393685)
                  ·
                    refine ⟨2624915159706757572440329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 55998190073744161545393685 2624915159706757572440329)
                    ·
                      refine ⟨1968686369780068179330247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2624915159706757572440329 1968686369780068179330247)
                      ·
                        rfl

theorem cell23_3834003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 2, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 2, 2, 6, 2].length) (baseStart_3834003 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3834003 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3834003 prefixEnd_3834003 := by exact prefixLift 3834003
  have htrace : WordTrace (prefixWord ++ tailWord_3834003) baseStart_3834003 baseEnd_3834003 := by
    simpa [prefixWord, tailWord_3834003, baseEnd_3834003] using wordTrace_append hprefix tailTrace_3834003
  have hstable : (prefixWord ++ tailWord_3834003).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3834003).length < 2 ^ (prefixWord ++ tailWord_3834003).sum := by decide
  have hdescent : baseEnd_3834003 < baseStart_3834003 := by decide
  rcases family_descends (prefixWord ++ tailWord_3834003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3834013 : List Nat := [1, 4, 2, 1, 1, 3, 1, 3, 1, 6]
def baseStart_3834013 : Nat := 118140960795 + 3834013 * 2 ^ 59
def prefixEnd_3834013 : Nat := 4983230072969 + 3 ^ 40 * 3834013 * 2
def baseEnd_3834013 : Nat := 656230501528871046735067

theorem tailTrace_3834013 : CollatzResearch.WordTrace tailWord_3834013 prefixEnd_3834013 656230501528871046735067 := by
  unfold tailWord_3834013
  simp only [CollatzResearch.WordTrace]
  refine ⟨139837942259033173134434693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93225294839355448756289795 139837942259033173134434693)
  ·
    refine ⟨26219614173568719962706505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 139837942259033173134434693 26219614173568719962706505)
    ·
      refine ⟨19664710630176539972029879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26219614173568719962706505 19664710630176539972029879)
      ·
        refine ⟨29497065945264809958044819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19664710630176539972029879 29497065945264809958044819)
        ·
          refine ⟨44245598917897214937067229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29497065945264809958044819 44245598917897214937067229)
          ·
            refine ⟨16592099594211455601400211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44245598917897214937067229 16592099594211455601400211)
            ·
              refine ⟨24888149391317183402100317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16592099594211455601400211 24888149391317183402100317)
              ·
                refine ⟨9333056021743943775787619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24888149391317183402100317 9333056021743943775787619)
                ·
                  refine ⟨13999584032615915663681429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9333056021743943775787619 13999584032615915663681429)
                  ·
                    refine ⟨656230501528871046735067, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13999584032615915663681429 656230501528871046735067)
                    ·
                      rfl

theorem cell23_3834013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 1, 3, 1, 6].length) (baseStart_3834013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3834013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3834013 prefixEnd_3834013 := by exact prefixLift 3834013
  have htrace : WordTrace (prefixWord ++ tailWord_3834013) baseStart_3834013 baseEnd_3834013 := by
    simpa [prefixWord, tailWord_3834013, baseEnd_3834013] using wordTrace_append hprefix tailTrace_3834013
  have hstable : (prefixWord ++ tailWord_3834013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3834013).length < 2 ^ (prefixWord ++ tailWord_3834013).sum := by decide
  have hdescent : baseEnd_3834013 < baseStart_3834013 := by decide
  rcases family_descends (prefixWord ++ tailWord_3834013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3834014 : List Nat := [4, 3, 1, 1, 3, 1, 1, 2, 3, 1, 3]
def baseStart_3834014 : Nat := 118140960795 + 3834014 * 2 ^ 59
def prefixEnd_3834014 : Nat := 4983230072969 + 3 ^ 40 * 3834014 * 2
def baseEnd_3834014 : Nat := 1968692018067267636292697

theorem tailTrace_3834014 : CollatzResearch.WordTrace tailWord_3834014 prefixEnd_3834014 1968692018067267636292697 := by
  unfold tailWord_3834014
  simp only [CollatzResearch.WordTrace]
  refine ⟨17479747341503693788152637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 93225319154686366870147397 17479747341503693788152637)
  ·
    refine ⟨6554905253063885170557239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17479747341503693788152637 6554905253063885170557239)
    ·
      refine ⟨9832357879595827755835859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6554905253063885170557239 9832357879595827755835859)
      ·
        refine ⟨14748536819393741633753789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9832357879595827755835859 14748536819393741633753789)
        ·
          refine ⟨5530701307272653112657671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14748536819393741633753789 5530701307272653112657671)
          ·
            refine ⟨8296051960908979668986507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5530701307272653112657671 8296051960908979668986507)
            ·
              refine ⟨12444077941363469503479761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8296051960908979668986507 12444077941363469503479761)
              ·
                refine ⟨9333058456022602127609821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12444077941363469503479761 9333058456022602127609821)
                ·
                  refine ⟨3499896921008475797853683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9333058456022602127609821 3499896921008475797853683)
                  ·
                    refine ⟨5249845381512713696780525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3499896921008475797853683 5249845381512713696780525)
                    ·
                      refine ⟨1968692018067267636292697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5249845381512713696780525 1968692018067267636292697)
                      ·
                        rfl

theorem cell23_3834014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 1, 1, 2, 3, 1, 3].length) (baseStart_3834014 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3834014 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3834014 prefixEnd_3834014 := by exact prefixLift 3834014
  have htrace : WordTrace (prefixWord ++ tailWord_3834014) baseStart_3834014 baseEnd_3834014 := by
    simpa [prefixWord, tailWord_3834014, baseEnd_3834014] using wordTrace_append hprefix tailTrace_3834014
  have hstable : (prefixWord ++ tailWord_3834014).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3834014).length < 2 ^ (prefixWord ++ tailWord_3834014).sum := by decide
  have hdescent : baseEnd_3834014 < baseStart_3834014 := by decide
  rcases family_descends (prefixWord ++ tailWord_3834014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3834040 : List Nat := [2, 1, 2, 1, 2, 1, 5, 3, 1, 2, 3]
def baseStart_3834040 : Nat := 118140960795 + 3834040 * 2 ^ 59
def prefixEnd_3834040 : Nat := 4983230072969 + 3 ^ 40 * 3834040 * 2
def baseEnd_3834040 : Nat := 1968705368564284534567577

theorem tailTrace_3834040 : CollatzResearch.WordTrace tailWord_3834040 prefixEnd_3834040 1968705368564284534567577 := by
  unfold tailWord_3834040
  simp only [CollatzResearch.WordTrace]
  refine ⟨69919463514967678372833787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93225951353290237830445049 69919463514967678372833787)
  ·
    refine ⟨104879195272451517559250681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69919463514967678372833787 104879195272451517559250681)
    ·
      refine ⟨78659396454338638169438011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104879195272451517559250681 78659396454338638169438011)
      ·
        refine ⟨117989094681507957254157017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78659396454338638169438011 117989094681507957254157017)
        ·
          refine ⟨88491821011130967940617763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 117989094681507957254157017 88491821011130967940617763)
          ·
            refine ⟨132737731516696451910926645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88491821011130967940617763 132737731516696451910926645)
            ·
              refine ⟨12444162329690292366649373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 132737731516696451910926645 12444162329690292366649373)
              ·
                refine ⟨4666560873633859637493515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12444162329690292366649373 4666560873633859637493515)
                ·
                  refine ⟨6999841310450789456240273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4666560873633859637493515 6999841310450789456240273)
                  ·
                    refine ⟨5249880982838092092180205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6999841310450789456240273 5249880982838092092180205)
                    ·
                      refine ⟨1968705368564284534567577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5249880982838092092180205 1968705368564284534567577)
                      ·
                        rfl

theorem cell23_3834040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 5, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 5, 3, 1, 2, 3].length) (baseStart_3834040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3834040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3834040 prefixEnd_3834040 := by exact prefixLift 3834040
  have htrace : WordTrace (prefixWord ++ tailWord_3834040) baseStart_3834040 baseEnd_3834040 := by
    simpa [prefixWord, tailWord_3834040, baseEnd_3834040] using wordTrace_append hprefix tailTrace_3834040
  have hstable : (prefixWord ++ tailWord_3834040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3834040).length < 2 ^ (prefixWord ++ tailWord_3834040).sum := by decide
  have hdescent : baseEnd_3834040 < baseStart_3834040 := by decide
  rcases family_descends (prefixWord ++ tailWord_3834040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3834053 : List Nat := [1, 3, 1, 1, 1, 1, 4, 2, 3, 3, 3]
def baseStart_3834053 : Nat := 118140960795 + 3834053 * 2 ^ 59
def prefixEnd_3834053 : Nat := 4983230072969 + 3 ^ 40 * 3834053 * 2
def baseEnd_3834053 : Nat := 1968712043812792983705017

theorem tailTrace_3834053 : CollatzResearch.WordTrace tailWord_3834053 prefixEnd_3834053 1968712043812792983705017 := by
  unfold tailWord_3834053
  simp only [CollatzResearch.WordTrace]
  refine ⟨139839401178888259965890813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93226267452592173310593875 139839401178888259965890813)
  ·
    refine ⟨52439775442083097487209055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 139839401178888259965890813 52439775442083097487209055)
    ·
      refine ⟨78659663163124646230813583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52439775442083097487209055 78659663163124646230813583)
      ·
        refine ⟨117989494744686969346220375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78659663163124646230813583 117989494744686969346220375)
        ·
          refine ⟨176984242117030454019330563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117989494744686969346220375 176984242117030454019330563)
          ·
            refine ⟨265476363175545681028995845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 176984242117030454019330563 265476363175545681028995845)
            ·
              refine ⟨49776818095414815192936721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 265476363175545681028995845 49776818095414815192936721)
              ·
                refine ⟨37332613571561111394702541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49776818095414815192936721 37332613571561111394702541)
                ·
                  refine ⟨13999730089335416773013453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37332613571561111394702541 13999730089335416773013453)
                  ·
                    refine ⟨5249898783500781289880045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13999730089335416773013453 5249898783500781289880045)
                    ·
                      refine ⟨1968712043812792983705017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5249898783500781289880045 1968712043812792983705017)
                      ·
                        rfl

theorem cell23_3834053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 4, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 4, 2, 3, 3, 3].length) (baseStart_3834053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3834053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3834053 prefixEnd_3834053 := by exact prefixLift 3834053
  have htrace : WordTrace (prefixWord ++ tailWord_3834053) baseStart_3834053 baseEnd_3834053 := by
    simpa [prefixWord, tailWord_3834053, baseEnd_3834053] using wordTrace_append hprefix tailTrace_3834053
  have hstable : (prefixWord ++ tailWord_3834053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3834053).length < 2 ^ (prefixWord ++ tailWord_3834053).sum := by decide
  have hdescent : baseEnd_3834053 < baseStart_3834053 := by decide
  rcases family_descends (prefixWord ++ tailWord_3834053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3834077 : List Nat := [1, 4, 3, 2, 1, 3, 2, 7]
def baseStart_3834077 : Nat := 118140960795 + 3834077 * 2 ^ 59
def prefixEnd_3834077 : Nat := 4983230072969 + 3 ^ 40 * 3834077 * 2
def baseEnd_3834077 : Nat := 72915717309203736659441

theorem tailTrace_3834077 : CollatzResearch.WordTrace tailWord_3834077 prefixEnd_3834077 72915717309203736659441 := by
  unfold tailWord_3834077
  simp only [CollatzResearch.WordTrace]
  refine ⟨139840276530801312064764485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93226851020534208043176323 139840276530801312064764485)
  ·
    refine ⟨26220051849525246012143341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 139840276530801312064764485 26220051849525246012143341)
    ·
      refine ⟨9832519443571967254553753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26220051849525246012143341 9832519443571967254553753)
      ·
        refine ⟨7374389582678975440915315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9832519443571967254553753 7374389582678975440915315)
        ·
          refine ⟨11061584374018463161372973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7374389582678975440915315 11061584374018463161372973)
          ·
            refine ⟨4148094140256923685514865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11061584374018463161372973 4148094140256923685514865)
            ·
              refine ⟨3111070605192692764136149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4148094140256923685514865 3111070605192692764136149)
              ·
                refine ⟨72915717309203736659441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3111070605192692764136149 72915717309203736659441)
                ·
                  rfl

theorem cell23_3834077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 3, 2, 7].length) (baseStart_3834077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3834077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3834077 prefixEnd_3834077 := by exact prefixLift 3834077
  have htrace : WordTrace (prefixWord ++ tailWord_3834077) baseStart_3834077 baseEnd_3834077 := by
    simpa [prefixWord, tailWord_3834077, baseEnd_3834077] using wordTrace_append hprefix tailTrace_3834077
  have hstable : (prefixWord ++ tailWord_3834077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3834077).length < 2 ^ (prefixWord ++ tailWord_3834077).sum := by decide
  have hdescent : baseEnd_3834077 < baseStart_3834077 := by decide
  rcases family_descends (prefixWord ++ tailWord_3834077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3834082 : List Nat := [3, 3, 4, 1, 2, 1, 1, 3, 1, 1, 3]
def baseStart_3834082 : Nat := 118140960795 + 3834082 * 2 ^ 59
def prefixEnd_3834082 : Nat := 4983230072969 + 3 ^ 40 * 3834082 * 2
def baseEnd_3834082 : Nat := 1968726934751773370242385

theorem tailTrace_3834082 : CollatzResearch.WordTrace tailWord_3834082 prefixEnd_3834082 1968726934751773370242385 := by
  unfold tailWord_3834082
  simp only [CollatzResearch.WordTrace]
  refine ⟨34960114723945799479674125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93226972597188798612464333 34960114723945799479674125)
  ·
    refine ⟨13110043021479674804877797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34960114723945799479674125 13110043021479674804877797)
    ·
      refine ⟨2458133066527439025914587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13110043021479674804877797 2458133066527439025914587)
      ·
        refine ⟨3687199599791158538871881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2458133066527439025914587 3687199599791158538871881)
        ·
          refine ⟨2765399699843368904153911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3687199599791158538871881 2765399699843368904153911)
          ·
            refine ⟨4148099549765053356230867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2765399699843368904153911 4148099549765053356230867)
            ·
              refine ⟨6222149324647580034346301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4148099549765053356230867 6222149324647580034346301)
              ·
                refine ⟨2333305996742842512879863, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6222149324647580034346301 2333305996742842512879863)
                ·
                  refine ⟨3499958995114263769319795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2333305996742842512879863 3499958995114263769319795)
                  ·
                    refine ⟨5249938492671395653979693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3499958995114263769319795 5249938492671395653979693)
                    ·
                      refine ⟨1968726934751773370242385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5249938492671395653979693 1968726934751773370242385)
                      ·
                        rfl

theorem cell23_3834082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 2, 1, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 2, 1, 1, 3, 1, 1, 3].length) (baseStart_3834082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3834082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3834082 prefixEnd_3834082 := by exact prefixLift 3834082
  have htrace : WordTrace (prefixWord ++ tailWord_3834082) baseStart_3834082 baseEnd_3834082 := by
    simpa [prefixWord, tailWord_3834082, baseEnd_3834082] using wordTrace_append hprefix tailTrace_3834082
  have hstable : (prefixWord ++ tailWord_3834082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3834082).length < 2 ^ (prefixWord ++ tailWord_3834082).sum := by decide
  have hdescent : baseEnd_3834082 < baseStart_3834082 := by decide
  rcases family_descends (prefixWord ++ tailWord_3834082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3834087 : List Nat := [1, 1, 5, 3, 1, 1, 1, 2, 4, 1, 3]
def baseStart_3834087 : Nat := 118140960795 + 3834087 * 2 ^ 59
def prefixEnd_3834087 : Nat := 4983230072969 + 3 ^ 40 * 3834087 * 2
def baseEnd_3834087 : Nat := 1968729502155045850679861

theorem tailTrace_3834087 : CollatzResearch.WordTrace tailWord_3834087 prefixEnd_3834087 1968729502155045850679861 := by
  unfold tailWord_3834087
  simp only [CollatzResearch.WordTrace]
  refine ⟨139840641260765083772628515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93227094173843389181752343 139840641260765083772628515)
  ·
    refine ⟨209760961891147625658942773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139840641260765083772628515 209760961891147625658942773)
    ·
      refine ⟨19665090177295089905525885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 209760961891147625658942773 19665090177295089905525885)
      ·
        refine ⟨7374408816485658714572207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19665090177295089905525885 7374408816485658714572207)
        ·
          refine ⟨11061613224728488071858311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7374408816485658714572207 11061613224728488071858311)
          ·
            refine ⟨16592419837092732107787467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11061613224728488071858311 16592419837092732107787467)
            ·
              refine ⟨24888629755639098161681201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16592419837092732107787467 24888629755639098161681201)
              ·
                refine ⟨18666472316729323621260901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24888629755639098161681201 18666472316729323621260901)
                ·
                  refine ⟨3499963559386748178986419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18666472316729323621260901 3499963559386748178986419)
                  ·
                    refine ⟨5249945339080122268479629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3499963559386748178986419 5249945339080122268479629)
                    ·
                      refine ⟨1968729502155045850679861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5249945339080122268479629 1968729502155045850679861)
                      ·
                        rfl

theorem cell23_3834087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 1, 2, 4, 1, 3].length) (baseStart_3834087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3834087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3834087 prefixEnd_3834087 := by exact prefixLift 3834087
  have htrace : WordTrace (prefixWord ++ tailWord_3834087) baseStart_3834087 baseEnd_3834087 := by
    simpa [prefixWord, tailWord_3834087, baseEnd_3834087] using wordTrace_append hprefix tailTrace_3834087
  have hstable : (prefixWord ++ tailWord_3834087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3834087).length < 2 ^ (prefixWord ++ tailWord_3834087).sum := by decide
  have hdescent : baseEnd_3834087 < baseStart_3834087 := by decide
  rcases family_descends (prefixWord ++ tailWord_3834087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3834097 : List Nat := [1, 2, 2, 2, 2, 1, 4, 3, 1, 3, 2]
def baseStart_3834097 : Nat := 118140960795 + 3834097 * 2 ^ 59
def prefixEnd_3834097 : Nat := 4983230072969 + 3 ^ 40 * 3834097 * 2
def baseEnd_3834097 : Nat := 1968734636961590811554815

theorem tailTrace_3834097 : CollatzResearch.WordTrace tailWord_3834097 prefixEnd_3834097 1968734636961590811554815 := by
  unfold tailWord_3834097
  simp only [CollatzResearch.WordTrace]
  refine ⟨139841005990728855480492545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93227337327152570320328363 139841005990728855480492545)
  ·
    refine ⟨104880754493046641610369409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139841005990728855480492545 104880754493046641610369409)
    ·
      refine ⟨78660565869784981207777057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104880754493046641610369409 78660565869784981207777057)
      ·
        refine ⟨58995424402338735905832793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78660565869784981207777057 58995424402338735905832793)
        ·
          refine ⟨44246568301754051929374595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58995424402338735905832793 44246568301754051929374595)
          ·
            refine ⟨66369852452631077894061893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44246568301754051929374595 66369852452631077894061893)
            ·
              refine ⟨12444347334868327105136605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 66369852452631077894061893 12444347334868327105136605)
              ·
                refine ⟨4666630250575622664426227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12444347334868327105136605 4666630250575622664426227)
                ·
                  refine ⟨6999945375863433996639341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4666630250575622664426227 6999945375863433996639341)
                  ·
                    refine ⟨2624979515948787748739753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6999945375863433996639341 2624979515948787748739753)
                    ·
                      refine ⟨1968734636961590811554815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2624979515948787748739753 1968734636961590811554815)
                      ·
                        rfl

theorem cell23_3834097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 4, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 4, 3, 1, 3, 2].length) (baseStart_3834097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3834097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3834097 prefixEnd_3834097 := by exact prefixLift 3834097
  have htrace : WordTrace (prefixWord ++ tailWord_3834097) baseStart_3834097 baseEnd_3834097 := by
    simpa [prefixWord, tailWord_3834097, baseEnd_3834097] using wordTrace_append hprefix tailTrace_3834097
  have hstable : (prefixWord ++ tailWord_3834097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3834097).length < 2 ^ (prefixWord ++ tailWord_3834097).sum := by decide
  have hdescent : baseEnd_3834097 < baseStart_3834097 := by decide
  rcases family_descends (prefixWord ++ tailWord_3834097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3834110 : List Nat := [4, 2, 2, 1, 1, 1, 2, 1, 2, 3, 4]
def baseStart_3834110 : Nat := 118140960795 + 3834110 * 2 ^ 59
def prefixEnd_3834110 : Nat := 4983230072969 + 3 ^ 40 * 3834110 * 2
def baseEnd_3834110 : Nat := 1968741312210099260692255

theorem tailTrace_3834110 : CollatzResearch.WordTrace tailWord_3834110 prefixEnd_3834110 1968741312210099260692255 := by
  unfold tailWord_3834110
  simp only [CollatzResearch.WordTrace]
  refine ⟨17480185017460219837589473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 93227653426454505800477189 17480185017460219837589473)
  ·
    refine ⟨13110138763095164878192105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17480185017460219837589473 13110138763095164878192105)
    ·
      refine ⟨9832604072321373658644079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13110138763095164878192105 9832604072321373658644079)
      ·
        refine ⟨14748906108482060487966119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9832604072321373658644079 14748906108482060487966119)
        ·
          refine ⟨22123359162723090731949179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14748906108482060487966119 22123359162723090731949179)
          ·
            refine ⟨33185038744084636097923769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22123359162723090731949179 33185038744084636097923769)
            ·
              refine ⟨24888779058063477073442827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33185038744084636097923769 24888779058063477073442827)
              ·
                refine ⟨37333168587095215610164241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24888779058063477073442827 37333168587095215610164241)
                ·
                  refine ⟨27999876440321411707623181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37333168587095215610164241 27999876440321411707623181)
                  ·
                    refine ⟨10499953665120529390358693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27999876440321411707623181 10499953665120529390358693)
                    ·
                      refine ⟨1968741312210099260692255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10499953665120529390358693 1968741312210099260692255)
                      ·
                        rfl

theorem cell23_3834110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 2, 1, 2, 3, 4].length) (baseStart_3834110 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3834110 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3834110 prefixEnd_3834110 := by exact prefixLift 3834110
  have htrace : WordTrace (prefixWord ++ tailWord_3834110) baseStart_3834110 baseEnd_3834110 := by
    simpa [prefixWord, tailWord_3834110, baseEnd_3834110] using wordTrace_append hprefix tailTrace_3834110
  have hstable : (prefixWord ++ tailWord_3834110).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3834110).length < 2 ^ (prefixWord ++ tailWord_3834110).sum := by decide
  have hdescent : baseEnd_3834110 < baseStart_3834110 := by decide
  rcases family_descends (prefixWord ++ tailWord_3834110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3834113 : List Nat := [1, 2, 4, 1, 1, 2, 1, 2, 1, 3, 5]
def baseStart_3834113 : Nat := 118140960795 + 3834113 * 2 ^ 59
def prefixEnd_3834113 : Nat := 4983230072969 + 3 ^ 40 * 3834113 * 2
def baseEnd_3834113 : Nat := 1968742852652062748954741

theorem tailTrace_3834113 : CollatzResearch.WordTrace tailWord_3834113 prefixEnd_3834113 1968742852652062748954741 := by
  unfold tailWord_3834113
  simp only [CollatzResearch.WordTrace]
  refine ⟨139841589558670890213074993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93227726372447260142049995 139841589558670890213074993)
  ·
    refine ⟨104881192169003167659806245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139841589558670890213074993 104881192169003167659806245)
    ·
      refine ⟨19665223531688093936213671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 104881192169003167659806245 19665223531688093936213671)
      ·
        refine ⟨29497835297532140904320507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19665223531688093936213671 29497835297532140904320507)
        ·
          refine ⟨44246752946298211356480761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29497835297532140904320507 44246752946298211356480761)
          ·
            refine ⟨33185064709723658517360571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44246752946298211356480761 33185064709723658517360571)
            ·
              refine ⟨49777597064585487776040857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33185064709723658517360571 49777597064585487776040857)
              ·
                refine ⟨37333197798439115832030643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49777597064585487776040857 37333197798439115832030643)
                ·
                  refine ⟨55999796697658673748045965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37333197798439115832030643 55999796697658673748045965)
                  ·
                    refine ⟨20999923761622002655517237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 55999796697658673748045965 20999923761622002655517237)
                    ·
                      refine ⟨1968742852652062748954741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20999923761622002655517237 1968742852652062748954741)
                      ·
                        rfl

theorem cell23_3834113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 1, 2, 1, 3, 5].length) (baseStart_3834113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3834113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3834113 prefixEnd_3834113 := by exact prefixLift 3834113
  have htrace : WordTrace (prefixWord ++ tailWord_3834113) baseStart_3834113 baseEnd_3834113 := by
    simpa [prefixWord, tailWord_3834113, baseEnd_3834113] using wordTrace_append hprefix tailTrace_3834113
  have hstable : (prefixWord ++ tailWord_3834113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3834113).length < 2 ^ (prefixWord ++ tailWord_3834113).sum := by decide
  have hdescent : baseEnd_3834113 < baseStart_3834113 := by decide
  rcases family_descends (prefixWord ++ tailWord_3834113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3834123 : List Nat := [1, 1, 1, 1, 5, 2, 2, 1, 1, 4, 4]
def baseStart_3834123 : Nat := 118140960795 + 3834123 * 2 ^ 59
def prefixEnd_3834123 : Nat := 4983230072969 + 3 ^ 40 * 3834123 * 2
def baseEnd_3834123 : Nat := 1968747987458607709829695

theorem tailTrace_3834123 : CollatzResearch.WordTrace tailWord_3834123 prefixEnd_3834123 1968747987458607709829695 := by
  unfold tailWord_3834123
  simp only [CollatzResearch.WordTrace]
  refine ⟨139841954288634661920939023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93227969525756441280626015 139841954288634661920939023)
  ·
    refine ⟨209762931432951992881408535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139841954288634661920939023 209762931432951992881408535)
    ·
      refine ⟨314644397149427989322112803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209762931432951992881408535 314644397149427989322112803)
      ·
        refine ⟨471966595724141983983169205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 314644397149427989322112803 471966595724141983983169205)
        ·
          refine ⟨44246868349138310998422113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 471966595724141983983169205 44246868349138310998422113)
          ·
            refine ⟨33185151261853733248816585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44246868349138310998422113 33185151261853733248816585)
            ·
              refine ⟨24888863446390299936612439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33185151261853733248816585 24888863446390299936612439)
              ·
                refine ⟨37333295169585449904918659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24888863446390299936612439 37333295169585449904918659)
                ·
                  refine ⟨55999942754378174857377989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37333295169585449904918659 55999942754378174857377989)
                  ·
                    refine ⟨10499989266445907785758373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 55999942754378174857377989 10499989266445907785758373)
                    ·
                      refine ⟨1968747987458607709829695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10499989266445907785758373 1968747987458607709829695)
                      ·
                        rfl

theorem cell23_3834123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 2, 1, 1, 4, 4].length) (baseStart_3834123 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3834123 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3834123 prefixEnd_3834123 := by exact prefixLift 3834123
  have htrace : WordTrace (prefixWord ++ tailWord_3834123) baseStart_3834123 baseEnd_3834123 := by
    simpa [prefixWord, tailWord_3834123, baseEnd_3834123] using wordTrace_append hprefix tailTrace_3834123
  have hstable : (prefixWord ++ tailWord_3834123).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3834123).length < 2 ^ (prefixWord ++ tailWord_3834123).sum := by decide
  have hdescent : baseEnd_3834123 < baseStart_3834123 := by decide
  rcases family_descends (prefixWord ++ tailWord_3834123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3834133 : List Nat := [1, 3, 2, 1, 2, 1, 2, 4, 7]
def baseStart_3834133 : Nat := 118140960795 + 3834133 * 2 ^ 59
def prefixEnd_3834133 : Nat := 4983230072969 + 3 ^ 40 * 3834133 * 2
def baseEnd_3834133 : Nat := 218750346918350296744961

theorem tailTrace_3834133 : CollatzResearch.WordTrace tailWord_3834133 prefixEnd_3834133 218750346918350296744961 := by
  unfold tailWord_3834133
  simp only [CollatzResearch.WordTrace]
  refine ⟨139842319018598433628803053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93228212679065622419202035 139842319018598433628803053)
  ·
    refine ⟨52440869631974412610801145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 139842319018598433628803053 52440869631974412610801145)
    ·
      refine ⟨39330652223980809458100859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52440869631974412610801145 39330652223980809458100859)
      ·
        refine ⟨58995978335971214187151289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39330652223980809458100859 58995978335971214187151289)
        ·
          refine ⟨44246983751978410640363467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58995978335971214187151289 44246983751978410640363467)
          ·
            refine ⟨66370475627967615960545201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44246983751978410640363467 66370475627967615960545201)
            ·
              refine ⟨49777856720975711970408901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66370475627967615960545201 49777856720975711970408901)
              ·
                refine ⟨9333348135182945994451669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 49777856720975711970408901 9333348135182945994451669)
                ·
                  refine ⟨218750346918350296744961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9333348135182945994451669 218750346918350296744961)
                  ·
                    rfl

theorem cell23_3834133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 2, 4, 7].length) (baseStart_3834133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3834133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3834133 prefixEnd_3834133 := by exact prefixLift 3834133
  have htrace : WordTrace (prefixWord ++ tailWord_3834133) baseStart_3834133 baseEnd_3834133 := by
    simpa [prefixWord, tailWord_3834133, baseEnd_3834133] using wordTrace_append hprefix tailTrace_3834133
  have hstable : (prefixWord ++ tailWord_3834133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3834133).length < 2 ^ (prefixWord ++ tailWord_3834133).sum := by decide
  have hdescent : baseEnd_3834133 < baseStart_3834133 := by decide
  rcases family_descends (prefixWord ++ tailWord_3834133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3834161 : List Nat := [1, 2, 2, 3, 4, 1, 2, 2, 2, 2, 2]
def baseStart_3834161 : Nat := 118140960795 + 3834161 * 2 ^ 59
def prefixEnd_3834161 : Nat := 4983230072969 + 3 ^ 40 * 3834161 * 2
def baseEnd_3834161 : Nat := 1968767499723478561154521

theorem tailTrace_3834161 : CollatzResearch.WordTrace tailWord_3834161 prefixEnd_3834161 1968767499723478561154521 := by
  unfold tailWord_3834161
  simp only [CollatzResearch.WordTrace]
  refine ⟨139843340262496994410822337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93228893508331329607214891 139843340262496994410822337)
  ·
    refine ⟨104882505196872745808116753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139843340262496994410822337 104882505196872745808116753)
    ·
      refine ⟨78661878897654559356087565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104882505196872745808116753 78661878897654559356087565)
      ·
        refine ⟨29498204586620459758532837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 78661878897654559356087565 29498204586620459758532837)
        ·
          refine ⟨5530913359991336204724907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29498204586620459758532837 5530913359991336204724907)
          ·
            refine ⟨8296370039987004307087361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5530913359991336204724907 8296370039987004307087361)
            ·
              refine ⟨6222277529990253230315521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8296370039987004307087361 6222277529990253230315521)
              ·
                refine ⟨4666708147492689922736641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6222277529990253230315521 4666708147492689922736641)
                ·
                  refine ⟨3500031110619517442052481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4666708147492689922736641 3500031110619517442052481)
                  ·
                    refine ⟨2625023332964638081539361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3500031110619517442052481 2625023332964638081539361)
                    ·
                      refine ⟨1968767499723478561154521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2625023332964638081539361 1968767499723478561154521)
                      ·
                        rfl

theorem cell23_3834161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 1, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 1, 2, 2, 2, 2, 2].length) (baseStart_3834161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3834161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3834161 prefixEnd_3834161 := by exact prefixLift 3834161
  have htrace : WordTrace (prefixWord ++ tailWord_3834161) baseStart_3834161 baseEnd_3834161 := by
    simpa [prefixWord, tailWord_3834161, baseEnd_3834161] using wordTrace_append hprefix tailTrace_3834161
  have hstable : (prefixWord ++ tailWord_3834161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3834161).length < 2 ^ (prefixWord ++ tailWord_3834161).sum := by decide
  have hdescent : baseEnd_3834161 < baseStart_3834161 := by decide
  rcases family_descends (prefixWord ++ tailWord_3834161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3834200 : List Nat := [2, 1, 2, 2, 1, 1, 2, 5, 2, 1, 4]
def baseStart_3834200 : Nat := 118140960795 + 3834200 * 2 ^ 59
def prefixEnd_3834200 : Nat := 4983230072969 + 3 ^ 40 * 3834200 * 2
def baseEnd_3834200 : Nat := 1968787525469003908566841

theorem tailTrace_3834200 : CollatzResearch.WordTrace tailWord_3834200 prefixEnd_3834200 1968787525469003908566841 := by
  unfold tailWord_3834200
  simp only [CollatzResearch.WordTrace]
  refine ⟨69922381354677852035746027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93229841806237136047661369 69922381354677852035746027)
  ·
    refine ⟨104883572032016778053619041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69922381354677852035746027 104883572032016778053619041)
    ·
      refine ⟨78662679024012583540214281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104883572032016778053619041 78662679024012583540214281)
      ·
        refine ⟨58997009268009437655160711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78662679024012583540214281 58997009268009437655160711)
        ·
          refine ⟨88495513902014156482741067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58997009268009437655160711 88495513902014156482741067)
          ·
            refine ⟨132743270853021234724111601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88495513902014156482741067 132743270853021234724111601)
            ·
              refine ⟨99557453139765926043083701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 132743270853021234724111601 99557453139765926043083701)
              ·
                refine ⟨9333511231853055566539097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 99557453139765926043083701 9333511231853055566539097)
                ·
                  refine ⟨7000133423889791674904323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9333511231853055566539097 7000133423889791674904323)
                  ·
                    refine ⟨10500200135834687512356485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7000133423889791674904323 10500200135834687512356485)
                    ·
                      refine ⟨1968787525469003908566841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10500200135834687512356485 1968787525469003908566841)
                      ·
                        rfl

theorem cell23_3834200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 5, 2, 1, 4].length) (baseStart_3834200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3834200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3834200 prefixEnd_3834200 := by exact prefixLift 3834200
  have htrace : WordTrace (prefixWord ++ tailWord_3834200) baseStart_3834200 baseEnd_3834200 := by
    simpa [prefixWord, tailWord_3834200, baseEnd_3834200] using wordTrace_append hprefix tailTrace_3834200
  have hstable : (prefixWord ++ tailWord_3834200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3834200).length < 2 ^ (prefixWord ++ tailWord_3834200).sum := by decide
  have hdescent : baseEnd_3834200 < baseStart_3834200 := by decide
  rcases family_descends (prefixWord ++ tailWord_3834200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3834360 : List Nat := [2, 1, 2, 1, 1, 4, 1, 2, 2, 7]
def baseStart_3834360 : Nat := 118140960795 + 3834360 * 2 ^ 59
def prefixEnd_3834360 : Nat := 4983230072969 + 3 ^ 40 * 3834360 * 2
def baseEnd_3834360 : Nat := 656289894124574427522035

theorem tailTrace_3834360 : CollatzResearch.WordTrace tailWord_3834360 prefixEnd_3834360 656289894124574427522035 := by
  unfold tailWord_3834360
  simp only [CollatzResearch.WordTrace]
  refine ⟨69925299194388025698658267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93233732259184034264877689 69925299194388025698658267)
  ·
    refine ⟨104887948791582038547987401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69925299194388025698658267 104887948791582038547987401)
    ·
      refine ⟨78665961593686528910990551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104887948791582038547987401 78665961593686528910990551)
      ·
        refine ⟨117998942390529793366485827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78665961593686528910990551 117998942390529793366485827)
        ·
          refine ⟨176998413585794690049728741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117998942390529793366485827 176998413585794690049728741)
          ·
            refine ⟨33187202547336504384324139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 176998413585794690049728741 33187202547336504384324139)
            ·
              refine ⟨49780803821004756576486209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33187202547336504384324139 49780803821004756576486209)
              ·
                refine ⟨37335602865753567432364657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49780803821004756576486209 37335602865753567432364657)
                ·
                  refine ⟨28001702149315175574273493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37335602865753567432364657 28001702149315175574273493)
                  ·
                    refine ⟨656289894124574427522035, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 28001702149315175574273493 656289894124574427522035)
                    ·
                      rfl

theorem cell23_3834360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 1, 2, 2, 7].length) (baseStart_3834360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3834360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3834360 prefixEnd_3834360 := by exact prefixLift 3834360
  have htrace : WordTrace (prefixWord ++ tailWord_3834360) baseStart_3834360 baseEnd_3834360 := by
    simpa [prefixWord, tailWord_3834360, baseEnd_3834360] using wordTrace_append hprefix tailTrace_3834360
  have hstable : (prefixWord ++ tailWord_3834360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3834360).length < 2 ^ (prefixWord ++ tailWord_3834360).sum := by decide
  have hdescent : baseEnd_3834360 < baseStart_3834360 := by decide
  rcases family_descends (prefixWord ++ tailWord_3834360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3834375 : List Nat := [1, 1, 4, 3, 3, 1, 2, 3, 1, 2, 2]
def baseStart_3834375 : Nat := 118140960795 + 3834375 * 2 ^ 59
def prefixEnd_3834375 : Nat := 4983230072969 + 3 ^ 40 * 3834375 * 2
def baseEnd_3834375 : Nat := 1968877384583540723878537

theorem tailTrace_3834375 : CollatzResearch.WordTrace tailWord_3834375 prefixEnd_3834375 1968877384583540723878537 := by
  unfold tailWord_3834375
  simp only [CollatzResearch.WordTrace]
  refine ⟨139851145483721708959112579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93234096989147805972741719 139851145483721708959112579)
  ·
    refine ⟨209776718225582563438668869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139851145483721708959112579 209776718225582563438668869)
    ·
      refine ⟨39333134667296730644750413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 209776718225582563438668869 39333134667296730644750413)
      ·
        refine ⟨14749925500236273991781405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39333134667296730644750413 14749925500236273991781405)
        ·
          refine ⟨5531222062588602746918027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14749925500236273991781405 5531222062588602746918027)
          ·
            refine ⟨8296833093882904120377041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5531222062588602746918027 8296833093882904120377041)
            ·
              refine ⟨6222624820412178090282781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8296833093882904120377041 6222624820412178090282781)
              ·
                refine ⟨2333484307654566783856043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6222624820412178090282781 2333484307654566783856043)
                ·
                  refine ⟨3500226461481850175784065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2333484307654566783856043 3500226461481850175784065)
                  ·
                    refine ⟨2625169846111387631838049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3500226461481850175784065 2625169846111387631838049)
                    ·
                      refine ⟨1968877384583540723878537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2625169846111387631838049 1968877384583540723878537)
                      ·
                        rfl

theorem cell23_3834375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 1, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 1, 2, 3, 1, 2, 2].length) (baseStart_3834375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3834375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3834375 prefixEnd_3834375 := by exact prefixLift 3834375
  have htrace : WordTrace (prefixWord ++ tailWord_3834375) baseStart_3834375 baseEnd_3834375 := by
    simpa [prefixWord, tailWord_3834375, baseEnd_3834375] using wordTrace_append hprefix tailTrace_3834375
  have hstable : (prefixWord ++ tailWord_3834375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3834375).length < 2 ^ (prefixWord ++ tailWord_3834375).sum := by decide
  have hdescent : baseEnd_3834375 < baseStart_3834375 := by decide
  rcases family_descends (prefixWord ++ tailWord_3834375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3834417 : List Nat := [1, 2, 2, 3, 1, 1, 2, 2, 2, 4, 3]
def baseStart_3834417 : Nat := 118140960795 + 3834417 * 2 ^ 59
def prefixEnd_3834417 : Nat := 4983230072969 + 3 ^ 40 * 3834417 * 2
def baseEnd_3834417 : Nat := 1968898950771029559553343

theorem tailTrace_3834417 : CollatzResearch.WordTrace tailWord_3834417 prefixEnd_3834417 1968898950771029559553343 := by
  unfold tailWord_3834417
  simp only [CollatzResearch.WordTrace]
  refine ⟨139852677349569550132141505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93235118233046366754761003 139852677349569550132141505)
  ·
    refine ⟨104889508012177162599106129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139852677349569550132141505 104889508012177162599106129)
    ·
      refine ⟨78667131009132871949329597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104889508012177162599106129 78667131009132871949329597)
      ·
        refine ⟨29500174128424826980998599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 78667131009132871949329597 29500174128424826980998599)
        ·
          refine ⟨44250261192637240471497899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29500174128424826980998599 44250261192637240471497899)
          ·
            refine ⟨66375391788955860707246849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44250261192637240471497899 66375391788955860707246849)
            ·
              refine ⟨49781543841716895530435137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66375391788955860707246849 49781543841716895530435137)
              ·
                refine ⟨37336157881287671647826353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49781543841716895530435137 37336157881287671647826353)
                ·
                  refine ⟨28002118410965753735869765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37336157881287671647826353 28002118410965753735869765)
                  ·
                    refine ⟨5250397202056078825475581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28002118410965753735869765 5250397202056078825475581)
                    ·
                      refine ⟨1968898950771029559553343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5250397202056078825475581 1968898950771029559553343)
                      ·
                        rfl

theorem cell23_3834417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 2, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 2, 2, 2, 4, 3].length) (baseStart_3834417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3834417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3834417 prefixEnd_3834417 := by exact prefixLift 3834417
  have htrace : WordTrace (prefixWord ++ tailWord_3834417) baseStart_3834417 baseEnd_3834417 := by
    simpa [prefixWord, tailWord_3834417, baseEnd_3834417] using wordTrace_append hprefix tailTrace_3834417
  have hstable : (prefixWord ++ tailWord_3834417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3834417).length < 2 ^ (prefixWord ++ tailWord_3834417).sum := by decide
  have hdescent : baseEnd_3834417 < baseStart_3834417 := by decide
  rcases family_descends (prefixWord ++ tailWord_3834417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3834447 : List Nat := [1, 1, 2, 1, 1, 2, 4, 1, 4, 3, 3]
def baseStart_3834447 : Nat := 118140960795 + 3834447 * 2 ^ 59
def prefixEnd_3834447 : Nat := 4983230072969 + 3 ^ 40 * 3834447 * 2
def baseEnd_3834447 : Nat := 1968914355190664442178205

theorem tailTrace_3834447 : CollatzResearch.WordTrace tailWord_3834447 prefixEnd_3834447 1968914355190664442178205 := by
  unfold tailWord_3834447
  simp only [CollatzResearch.WordTrace]
  refine ⟨139853771539460865255733595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93235847692973910170489063 139853771539460865255733595)
  ·
    refine ⟨209780657309191297883600393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139853771539460865255733595 209780657309191297883600393)
    ·
      refine ⟨157335492981893473412700295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 209780657309191297883600393 157335492981893473412700295)
      ·
        refine ⟨236003239472840210119050443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157335492981893473412700295 236003239472840210119050443)
        ·
          refine ⟨354004859209260315178575665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 236003239472840210119050443 354004859209260315178575665)
          ·
            refine ⟨265503644406945236383931749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 354004859209260315178575665 265503644406945236383931749)
            ·
              refine ⟨49781933326302231821987203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 265503644406945236383931749 49781933326302231821987203)
              ·
                refine ⟨74672899989453347732980805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49781933326302231821987203 74672899989453347732980805)
                ·
                  refine ⟨14001168748022502699933901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 74672899989453347732980805 14001168748022502699933901)
                  ·
                    refine ⟨5250438280508438512475213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14001168748022502699933901 5250438280508438512475213)
                    ·
                      refine ⟨1968914355190664442178205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5250438280508438512475213 1968914355190664442178205)
                      ·
                        rfl

theorem cell23_3834447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 4, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 4, 1, 4, 3, 3].length) (baseStart_3834447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3834447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3834447 prefixEnd_3834447 := by exact prefixLift 3834447
  have htrace : WordTrace (prefixWord ++ tailWord_3834447) baseStart_3834447 baseEnd_3834447 := by
    simpa [prefixWord, tailWord_3834447, baseEnd_3834447] using wordTrace_append hprefix tailTrace_3834447
  have hstable : (prefixWord ++ tailWord_3834447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3834447).length < 2 ^ (prefixWord ++ tailWord_3834447).sum := by decide
  have hdescent : baseEnd_3834447 < baseStart_3834447 := by decide
  rcases family_descends (prefixWord ++ tailWord_3834447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3834465 : List Nat := [1, 2, 3, 1, 1, 6, 2, 1, 2, 2, 2]
def baseStart_3834465 : Nat := 118140960795 + 3834465 * 2 ^ 59
def prefixEnd_3834465 : Nat := 4983230072969 + 3 ^ 40 * 3834465 * 2
def baseEnd_3834465 : Nat := 1968923597842445371753123

theorem tailTrace_3834465 : CollatzResearch.WordTrace tailWord_3834465 prefixEnd_3834465 1968923597842445371753123 := by
  unfold tailWord_3834465
  simp only [CollatzResearch.WordTrace]
  refine ⟨139854428053395654329888849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93236285368930436219925899 139854428053395654329888849)
  ·
    refine ⟨104890821040046740747416637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139854428053395654329888849 104890821040046740747416637)
    ·
      refine ⟨39334057890017527780281239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 104890821040046740747416637 39334057890017527780281239)
      ·
        refine ⟨59001086835026291670421859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39334057890017527780281239 59001086835026291670421859)
        ·
          refine ⟨88501630252539437505632789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59001086835026291670421859 88501630252539437505632789)
          ·
            refine ⟨4148513918087786133076537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 88501630252539437505632789 4148513918087786133076537)
            ·
              refine ⟨3111385438565839599807403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4148513918087786133076537 3111385438565839599807403)
              ·
                refine ⟨4667078157848759399711105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3111385438565839599807403 4667078157848759399711105)
                ·
                  refine ⟨3500308618386569549783329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4667078157848759399711105 3500308618386569549783329)
                  ·
                    refine ⟨2625231463789927162337497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3500308618386569549783329 2625231463789927162337497)
                    ·
                      refine ⟨1968923597842445371753123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2625231463789927162337497 1968923597842445371753123)
                      ·
                        rfl

theorem cell23_3834465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 6, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 6, 2, 1, 2, 2, 2].length) (baseStart_3834465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3834465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3834465 prefixEnd_3834465 := by exact prefixLift 3834465
  have htrace : WordTrace (prefixWord ++ tailWord_3834465) baseStart_3834465 baseEnd_3834465 := by
    simpa [prefixWord, tailWord_3834465, baseEnd_3834465] using wordTrace_append hprefix tailTrace_3834465
  have hstable : (prefixWord ++ tailWord_3834465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3834465).length < 2 ^ (prefixWord ++ tailWord_3834465).sum := by decide
  have hdescent : baseEnd_3834465 < baseStart_3834465 := by decide
  rcases family_descends (prefixWord ++ tailWord_3834465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3834467 : List Nat := [1, 1, 1, 5, 1, 2, 1, 2, 4, 5]
def baseStart_3834467 : Nat := 118140960795 + 3834467 * 2 ^ 59
def prefixEnd_3834467 : Nat := 4983230072969 + 3 ^ 40 * 3834467 * 2
def baseEnd_3834467 : Nat := 656308208267918121309371

theorem tailTrace_3834467 : CollatzResearch.WordTrace tailWord_3834467 prefixEnd_3834467 656308208267918121309371 := by
  unfold tailWord_3834467
  simp only [CollatzResearch.WordTrace]
  refine ⟨139854500999388408671461655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93236333999592272447641103 139854500999388408671461655)
  ·
    refine ⟨209781751499082613007192483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139854500999388408671461655 209781751499082613007192483)
    ·
      refine ⟨314672627248623919510788725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209781751499082613007192483 314672627248623919510788725)
      ·
        refine ⟨29500558804558492454136443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 314672627248623919510788725 29500558804558492454136443)
        ·
          refine ⟨44250838206837738681204665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29500558804558492454136443 44250838206837738681204665)
          ·
            refine ⟨33188128655128304010903499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44250838206837738681204665 33188128655128304010903499)
            ·
              refine ⟨49782192982692456016355249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33188128655128304010903499 49782192982692456016355249)
              ·
                refine ⟨37336644737019342012266437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49782192982692456016355249 37336644737019342012266437)
                ·
                  refine ⟨7000620888191126627299957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37336644737019342012266437 7000620888191126627299957)
                  ·
                    refine ⟨656308208267918121309371, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7000620888191126627299957 656308208267918121309371)
                    ·
                      rfl

theorem cell23_3834467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 1, 2, 4, 5].length) (baseStart_3834467 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3834467 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3834467 prefixEnd_3834467 := by exact prefixLift 3834467
  have htrace : WordTrace (prefixWord ++ tailWord_3834467) baseStart_3834467 baseEnd_3834467 := by
    simpa [prefixWord, tailWord_3834467, baseEnd_3834467] using wordTrace_append hprefix tailTrace_3834467
  have hstable : (prefixWord ++ tailWord_3834467).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3834467).length < 2 ^ (prefixWord ++ tailWord_3834467).sum := by decide
  have hdescent : baseEnd_3834467 < baseStart_3834467 := by decide
  rcases family_descends (prefixWord ++ tailWord_3834467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3834487 : List Nat := [1, 1, 3, 1, 1, 3, 2, 3, 1, 3, 4]
def baseStart_3834487 : Nat := 118140960795 + 3834487 * 2 ^ 59
def prefixEnd_3834487 : Nat := 4983230072969 + 3 ^ 40 * 3834487 * 2
def baseEnd_3834487 : Nat := 1968934894416844285678021

theorem tailTrace_3834487 : CollatzResearch.WordTrace tailWord_3834487 prefixEnd_3834487 1968934894416844285678021 := by
  unfold tailWord_3834487
  simp only [CollatzResearch.WordTrace]
  refine ⟨139855230459315952087189715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93236820306210634724793143 139855230459315952087189715)
  ·
    refine ⟨209782845688973928130784573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139855230459315952087189715 209782845688973928130784573)
    ·
      refine ⟨78668567133365223049044215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 209782845688973928130784573 78668567133365223049044215)
      ·
        refine ⟨118002850700047834573566323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78668567133365223049044215 118002850700047834573566323)
        ·
          refine ⟨177004276050071751860349485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118002850700047834573566323 177004276050071751860349485)
          ·
            refine ⟨66376603518776906947631057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 177004276050071751860349485 66376603518776906947631057)
            ·
              refine ⟨49782452639082680210723293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66376603518776906947631057 49782452639082680210723293)
              ·
                refine ⟨18668419739656005079021235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49782452639082680210723293 18668419739656005079021235)
                ·
                  refine ⟨28002629609484007618531853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18668419739656005079021235 28002629609484007618531853)
                  ·
                    refine ⟨10500986103556502856949445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28002629609484007618531853 10500986103556502856949445)
                    ·
                      refine ⟨1968934894416844285678021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10500986103556502856949445 1968934894416844285678021)
                      ·
                        rfl

theorem cell23_3834487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 2, 3, 1, 3, 4].length) (baseStart_3834487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3834487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3834487 prefixEnd_3834487 := by exact prefixLift 3834487
  have htrace : WordTrace (prefixWord ++ tailWord_3834487) baseStart_3834487 baseEnd_3834487 := by
    simpa [prefixWord, tailWord_3834487, baseEnd_3834487] using wordTrace_append hprefix tailTrace_3834487
  have hstable : (prefixWord ++ tailWord_3834487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3834487).length < 2 ^ (prefixWord ++ tailWord_3834487).sum := by decide
  have hdescent : baseEnd_3834487 < baseStart_3834487 := by decide
  rcases family_descends (prefixWord ++ tailWord_3834487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3834517 : List Nat := [1, 3, 2, 1, 1, 1, 1, 1, 4, 4, 4]
def baseStart_3834517 : Nat := 118140960795 + 3834517 * 2 ^ 59
def prefixEnd_3834517 : Nat := 4983230072969 + 3 ^ 40 * 3834517 * 2
def baseEnd_3834517 : Nat := 1968950298836479168302883

theorem tailTrace_3834517 : CollatzResearch.WordTrace tailWord_3834517 prefixEnd_3834517 1968950298836479168302883 := by
  unfold tailWord_3834517
  simp only [CollatzResearch.WordTrace]
  refine ⟨139856324649207267210781805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93237549766138178140521203 139856324649207267210781805)
  ·
    refine ⟨52446121743452725204043177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 139856324649207267210781805 52446121743452725204043177)
    ·
      refine ⟨39334591307589543903032383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52446121743452725204043177 39334591307589543903032383)
      ·
        refine ⟨59001886961384315854548575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39334591307589543903032383 59001886961384315854548575)
        ·
          refine ⟨88502830442076473781822863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59001886961384315854548575 88502830442076473781822863)
          ·
            refine ⟨132754245663114710672734295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88502830442076473781822863 132754245663114710672734295)
            ·
              refine ⟨199131368494672066009101443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 132754245663114710672734295 199131368494672066009101443)
              ·
                refine ⟨298697052742008099013652165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 199131368494672066009101443 298697052742008099013652165)
                ·
                  refine ⟨56005697389126518565059781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 298697052742008099013652165 56005697389126518565059781)
                  ·
                    refine ⟨10501068260461222230948709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 56005697389126518565059781 10501068260461222230948709)
                    ·
                      refine ⟨1968950298836479168302883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10501068260461222230948709 1968950298836479168302883)
                      ·
                        rfl

theorem cell23_3834517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 1, 4, 4, 4].length) (baseStart_3834517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3834517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3834517 prefixEnd_3834517 := by exact prefixLift 3834517
  have htrace : WordTrace (prefixWord ++ tailWord_3834517) baseStart_3834517 baseEnd_3834517 := by
    simpa [prefixWord, tailWord_3834517, baseEnd_3834517] using wordTrace_append hprefix tailTrace_3834517
  have hstable : (prefixWord ++ tailWord_3834517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3834517).length < 2 ^ (prefixWord ++ tailWord_3834517).sum := by decide
  have hdescent : baseEnd_3834517 < baseStart_3834517 := by decide
  rcases family_descends (prefixWord ++ tailWord_3834517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3834535 : List Nat := [1, 1, 6, 3, 2, 1, 1, 1, 2, 5]
def baseStart_3834535 : Nat := 118140960795 + 3834535 * 2 ^ 59
def prefixEnd_3834535 : Nat := 4983230072969 + 3 ^ 40 * 3834535 * 2
def baseEnd_3834535 : Nat := 656319847162753365959267

theorem tailTrace_3834535 : CollatzResearch.WordTrace tailWord_3834535 prefixEnd_3834535 656319847162753365959267 := by
  unfold tailWord_3834535
  simp only [CollatzResearch.WordTrace]
  refine ⟨139856981163142056284937059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93237987442094704189958039 139856981163142056284937059)
  ·
    refine ⟨209785471744713084427405589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139856981163142056284937059 209785471744713084427405589)
    ·
      refine ⟨9833693988033425832534637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 209785471744713084427405589 9833693988033425832534637)
      ·
        refine ⟨3687635245512534687200489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9833693988033425832534637 3687635245512534687200489)
        ·
          refine ⟨2765726434134401015400367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3687635245512534687200489 2765726434134401015400367)
          ·
            refine ⟨4148589651201601523100551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2765726434134401015400367 4148589651201601523100551)
            ·
              refine ⟨6222884476802402284650827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4148589651201601523100551 6222884476802402284650827)
              ·
                refine ⟨9334326715203603426976241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6222884476802402284650827 9334326715203603426976241)
                ·
                  refine ⟨7000745036402702570232181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9334326715203603426976241 7000745036402702570232181)
                  ·
                    refine ⟨656319847162753365959267, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7000745036402702570232181 656319847162753365959267)
                    ·
                      rfl

theorem cell23_3834535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 2, 1, 1, 1, 2, 5].length) (baseStart_3834535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3834535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3834535 prefixEnd_3834535 := by exact prefixLift 3834535
  have htrace : WordTrace (prefixWord ++ tailWord_3834535) baseStart_3834535 baseEnd_3834535 := by
    simpa [prefixWord, tailWord_3834535, baseEnd_3834535] using wordTrace_append hprefix tailTrace_3834535
  have hstable : (prefixWord ++ tailWord_3834535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3834535).length < 2 ^ (prefixWord ++ tailWord_3834535).sum := by decide
  have hdescent : baseEnd_3834535 < baseStart_3834535 := by decide
  rcases family_descends (prefixWord ++ tailWord_3834535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3834538 : List Nat := [3, 1, 5, 2, 1, 1, 1, 1, 1, 3, 4]
def baseStart_3834538 : Nat := 118140960795 + 3834538 * 2 ^ 59
def prefixEnd_3834538 : Nat := 4983230072969 + 3 ^ 40 * 3834538 * 2
def baseEnd_3834538 : Nat := 1968961081930223586140287

theorem tailTrace_3834538 : CollatzResearch.WordTrace tailWord_3834538 prefixEnd_3834538 1968961081930223586140287 := by
  unfold tailWord_3834538
  simp only [CollatzResearch.WordTrace]
  refine ⟨34964272645532796949324067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93238060388087458531530845 34964272645532796949324067)
  ·
    refine ⟨52446408968299195423986101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34964272645532796949324067 52446408968299195423986101)
    ·
      refine ⟨4916850840778049570998697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 52446408968299195423986101 4916850840778049570998697)
      ·
        refine ⟨3687638130583537178249023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4916850840778049570998697 3687638130583537178249023)
        ·
          refine ⟨5531457195875305767373535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3687638130583537178249023 5531457195875305767373535)
          ·
            refine ⟨8297185793812958651060303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5531457195875305767373535 8297185793812958651060303)
            ·
              refine ⟨12445778690719437976590455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8297185793812958651060303 12445778690719437976590455)
              ·
                refine ⟨18668668036079156964885683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12445778690719437976590455 18668668036079156964885683)
                ·
                  refine ⟨28003002054118735447328525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18668668036079156964885683 28003002054118735447328525)
                  ·
                    refine ⟨10501125770294525792748197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28003002054118735447328525 10501125770294525792748197)
                    ·
                      refine ⟨1968961081930223586140287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10501125770294525792748197 1968961081930223586140287)
                      ·
                        rfl

theorem cell23_3834538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 1, 1, 1, 1, 3, 4].length) (baseStart_3834538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3834538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3834538 prefixEnd_3834538 := by exact prefixLift 3834538
  have htrace : WordTrace (prefixWord ++ tailWord_3834538) baseStart_3834538 baseEnd_3834538 := by
    simpa [prefixWord, tailWord_3834538, baseEnd_3834538] using wordTrace_append hprefix tailTrace_3834538
  have hstable : (prefixWord ++ tailWord_3834538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3834538).length < 2 ^ (prefixWord ++ tailWord_3834538).sum := by decide
  have hdescent : baseEnd_3834538 < baseStart_3834538 := by decide
  rcases family_descends (prefixWord ++ tailWord_3834538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3834541 : List Nat := [1, 5, 2, 1, 1, 3, 1, 1, 1, 4, 3]
def baseStart_3834541 : Nat := 118140960795 + 3834541 * 2 ^ 59
def prefixEnd_3834541 : Nat := 4983230072969 + 3 ^ 40 * 3834541 * 2
def baseEnd_3834541 : Nat := 1968962622372187074402773

theorem tailTrace_3834541 : CollatzResearch.WordTrace tailWord_3834541 prefixEnd_3834541 1968962622372187074402773 := by
  unfold tailWord_3834541
  simp only [CollatzResearch.WordTrace]
  refine ⟨139857200001120319309655477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93238133334080212873103651 139857200001120319309655477)
  ·
    refine ⟨13111612500105029935280201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 139857200001120319309655477 13111612500105029935280201)
    ·
      refine ⟨9833709375078772451460151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13111612500105029935280201 9833709375078772451460151)
      ·
        refine ⟨14750564062618158677190227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9833709375078772451460151 14750564062618158677190227)
        ·
          refine ⟨22125846093927238015785341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14750564062618158677190227 22125846093927238015785341)
          ·
            refine ⟨8297192285222714255919503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22125846093927238015785341 8297192285222714255919503)
            ·
              refine ⟨12445788427834071383879255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8297192285222714255919503 12445788427834071383879255)
              ·
                refine ⟨18668682641751107075818883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12445788427834071383879255 18668682641751107075818883)
                ·
                  refine ⟨28003023962626660613728325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18668682641751107075818883 28003023962626660613728325)
                  ·
                    refine ⟨5250566992992498865074061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28003023962626660613728325 5250566992992498865074061)
                    ·
                      refine ⟨1968962622372187074402773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5250566992992498865074061 1968962622372187074402773)
                      ·
                        rfl

theorem cell23_3834541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 3, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 3, 1, 1, 1, 4, 3].length) (baseStart_3834541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3834541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3834541 prefixEnd_3834541 := by exact prefixLift 3834541
  have htrace : WordTrace (prefixWord ++ tailWord_3834541) baseStart_3834541 baseEnd_3834541 := by
    simpa [prefixWord, tailWord_3834541, baseEnd_3834541] using wordTrace_append hprefix tailTrace_3834541
  have hstable : (prefixWord ++ tailWord_3834541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3834541).length < 2 ^ (prefixWord ++ tailWord_3834541).sum := by decide
  have hdescent : baseEnd_3834541 < baseStart_3834541 := by decide
  rcases family_descends (prefixWord ++ tailWord_3834541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3834564 : List Nat := [2, 3, 3, 1, 1, 2, 1, 1, 1, 2, 6]
def baseStart_3834564 : Nat := 118140960795 + 3834564 * 2 ^ 59
def prefixEnd_3834564 : Nat := 4983230072969 + 3 ^ 40 * 3834564 * 2
def baseEnd_3834564 : Nat := 1968974432427240484415167

theorem tailTrace_3834564 : CollatzResearch.WordTrace tailWord_3834564 prefixEnd_3834564 1968974432427240484415167 := by
  unfold tailWord_3834564
  simp only [CollatzResearch.WordTrace]
  refine ⟨69929019440018497118871373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93238692586691329491828497 69929019440018497118871373)
  ·
    refine ⟨26223382290006936419576765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69929019440018497118871373 26223382290006936419576765)
    ·
      refine ⟨9833768358752601157341287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26223382290006936419576765 9833768358752601157341287)
      ·
        refine ⟨14750652538128901736011931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9833768358752601157341287 14750652538128901736011931)
        ·
          refine ⟨22125978807193352604017897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14750652538128901736011931 22125978807193352604017897)
          ·
            refine ⟨16594484105395014453013423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22125978807193352604017897 16594484105395014453013423)
            ·
              refine ⟨24891726158092521679520135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16594484105395014453013423 24891726158092521679520135)
              ·
                refine ⟨37337589237138782519280203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24891726158092521679520135 37337589237138782519280203)
                ·
                  refine ⟨56006383855708173778920305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37337589237138782519280203 56006383855708173778920305)
                  ·
                    refine ⟨42004787891781130334190229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 56006383855708173778920305 42004787891781130334190229)
                    ·
                      refine ⟨1968974432427240484415167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 42004787891781130334190229 1968974432427240484415167)
                      ·
                        rfl

theorem cell23_3834564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 1, 1, 1, 2, 6].length) (baseStart_3834564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3834564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3834564 prefixEnd_3834564 := by exact prefixLift 3834564
  have htrace : WordTrace (prefixWord ++ tailWord_3834564) baseStart_3834564 baseEnd_3834564 := by
    simpa [prefixWord, tailWord_3834564, baseEnd_3834564] using wordTrace_append hprefix tailTrace_3834564
  have hstable : (prefixWord ++ tailWord_3834564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3834564).length < 2 ^ (prefixWord ++ tailWord_3834564).sum := by decide
  have hdescent : baseEnd_3834564 < baseStart_3834564 := by decide
  rcases family_descends (prefixWord ++ tailWord_3834564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3834567 : List Nat := [1, 1, 4, 1, 1, 1, 2, 2, 2, 1, 7]
def baseStart_3834567 : Nat := 118140960795 + 3834567 * 2 ^ 59
def prefixEnd_3834567 : Nat := 4983230072969 + 3 ^ 40 * 3834567 * 2
def baseEnd_3834567 : Nat := 1968975972869203972677653

theorem tailTrace_3834567 : CollatzResearch.WordTrace tailWord_3834567 prefixEnd_3834567 1968975972869203972677653 := by
  unfold tailWord_3834567
  simp only [CollatzResearch.WordTrace]
  refine ⟨139858148299026125750101955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93238765532684083833401303 139858148299026125750101955)
  ·
    refine ⟨209787222448539188625152933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139858148299026125750101955 209787222448539188625152933)
    ·
      refine ⟨39335104209101097867216175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 209787222448539188625152933 39335104209101097867216175)
      ·
        refine ⟨59002656313651646800824263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39335104209101097867216175 59002656313651646800824263)
        ·
          refine ⟨88503984470477470201236395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59002656313651646800824263 88503984470477470201236395)
          ·
            refine ⟨132755976705716205301854593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88503984470477470201236395 132755976705716205301854593)
            ·
              refine ⟨99566982529287153976390945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 132755976705716205301854593 99566982529287153976390945)
              ·
                refine ⟨74675236896965365482293209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 99566982529287153976390945 74675236896965365482293209)
                ·
                  refine ⟨56006427672724024111719907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 74675236896965365482293209 56006427672724024111719907)
                  ·
                    refine ⟨84009641509086036167579861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 56006427672724024111719907 84009641509086036167579861)
                    ·
                      refine ⟨1968975972869203972677653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 84009641509086036167579861 1968975972869203972677653)
                      ·
                        rfl

theorem cell23_3834567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 2, 2, 1, 7].length) (baseStart_3834567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3834567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3834567 prefixEnd_3834567 := by exact prefixLift 3834567
  have htrace : WordTrace (prefixWord ++ tailWord_3834567) baseStart_3834567 baseEnd_3834567 := by
    simpa [prefixWord, tailWord_3834567, baseEnd_3834567] using wordTrace_append hprefix tailTrace_3834567
  have hstable : (prefixWord ++ tailWord_3834567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3834567).length < 2 ^ (prefixWord ++ tailWord_3834567).sum := by decide
  have hdescent : baseEnd_3834567 < baseStart_3834567 := by decide
  rcases family_descends (prefixWord ++ tailWord_3834567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3834578 : List Nat := [3, 2, 2, 2, 3, 1, 3, 1, 6]
def baseStart_3834578 : Nat := 118140960795 + 3834578 * 2 ^ 59
def prefixEnd_3834578 : Nat := 4983230072969 + 3 ^ 40 * 3834578 * 2
def baseEnd_3834578 : Nat := 218775735684044825515567

theorem tailTrace_3834578 : CollatzResearch.WordTrace tailWord_3834578 prefixEnd_3834578 218775735684044825515567 := by
  unfold tailWord_3834578
  simp only [CollatzResearch.WordTrace]
  refine ⟨34964637375496568657188097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93239033001324183085834925 34964637375496568657188097)
  ·
    refine ⟨26223478031622426492891073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34964637375496568657188097 26223478031622426492891073)
    ·
      refine ⟨19667608523716819869668305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26223478031622426492891073 19667608523716819869668305)
      ·
        refine ⟨14750706392787614902251229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19667608523716819869668305 14750706392787614902251229)
        ·
          refine ⟨5531514897295355588344211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14750706392787614902251229 5531514897295355588344211)
          ·
            refine ⟨8297272345943033382516317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5531514897295355588344211 8297272345943033382516317)
            ·
              refine ⟨3111477129728637518443619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8297272345943033382516317 3111477129728637518443619)
              ·
                refine ⟨4667215694592956277665429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3111477129728637518443619 4667215694592956277665429)
                ·
                  refine ⟨218775735684044825515567, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4667215694592956277665429 218775735684044825515567)
                  ·
                    rfl

theorem cell23_3834578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 1, 3, 1, 6].length) (baseStart_3834578 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3834578 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3834578 prefixEnd_3834578 := by exact prefixLift 3834578
  have htrace : WordTrace (prefixWord ++ tailWord_3834578) baseStart_3834578 baseEnd_3834578 := by
    simpa [prefixWord, tailWord_3834578, baseEnd_3834578] using wordTrace_append hprefix tailTrace_3834578
  have hstable : (prefixWord ++ tailWord_3834578).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3834578).length < 2 ^ (prefixWord ++ tailWord_3834578).sum := by decide
  have hdescent : baseEnd_3834578 < baseStart_3834578 := by decide
  rcases family_descends (prefixWord ++ tailWord_3834578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3834587 : List Nat := [1, 1, 1, 1, 1, 1, 1, 3, 7, 6]
def baseStart_3834587 : Nat := 118140960795 + 3834587 * 2 ^ 59
def prefixEnd_3834587 : Nat := 4983230072969 + 3 ^ 40 * 3834587 * 2
def baseEnd_3834587 : Nat := 656328747494097964809187

theorem tailTrace_3834587 : CollatzResearch.WordTrace tailWord_3834587 prefixEnd_3834587 656328747494097964809187 := by
  unfold tailWord_3834587
  simp only [CollatzResearch.WordTrace]
  refine ⟨139858877758953669165830015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93239251839302446110553343 139858877758953669165830015)
  ·
    refine ⟨209788316638430503748745023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139858877758953669165830015 209788316638430503748745023)
    ·
      refine ⟨314682474957645755623117535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209788316638430503748745023 314682474957645755623117535)
      ·
        refine ⟨472023712436468633434676303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 314682474957645755623117535 472023712436468633434676303)
        ·
          refine ⟨708035568654702950152014455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 472023712436468633434676303 708035568654702950152014455)
          ·
            refine ⟨1062053352982054425228021683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 708035568654702950152014455 1062053352982054425228021683)
            ·
              refine ⟨1593080029473081637842032525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1062053352982054425228021683 1593080029473081637842032525)
              ·
                refine ⟨597405011052405614190762197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1593080029473081637842032525 597405011052405614190762197)
                ·
                  refine ⟨14001679946540756582595989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 597405011052405614190762197 14001679946540756582595989)
                  ·
                    refine ⟨656328747494097964809187, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14001679946540756582595989 656328747494097964809187)
                    ·
                      rfl

theorem cell23_3834587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 7, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 7, 6].length) (baseStart_3834587 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3834587 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3834587 prefixEnd_3834587 := by exact prefixLift 3834587
  have htrace : WordTrace (prefixWord ++ tailWord_3834587) baseStart_3834587 baseEnd_3834587 := by
    simpa [prefixWord, tailWord_3834587, baseEnd_3834587] using wordTrace_append hprefix tailTrace_3834587
  have hstable : (prefixWord ++ tailWord_3834587).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3834587).length < 2 ^ (prefixWord ++ tailWord_3834587).sum := by decide
  have hdescent : baseEnd_3834587 < baseStart_3834587 := by decide
  rcases family_descends (prefixWord ++ tailWord_3834587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3834591 : List Nat := [1, 1, 2, 3, 2, 4, 2, 2, 1, 5]
def baseStart_3834591 : Nat := 118140960795 + 3834591 * 2 ^ 59
def prefixEnd_3834591 : Nat := 4983230072969 + 3 ^ 40 * 3834591 * 2
def baseEnd_3834591 : Nat := 656329432134970626259181

theorem tailTrace_3834591 : CollatzResearch.WordTrace tailWord_3834591 prefixEnd_3834591 656329432134970626259181 := by
  unfold tailWord_3834591
  simp only [CollatzResearch.WordTrace]
  refine ⟨139859023650939177848975627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93239349100626118565983751 139859023650939177848975627)
  ·
    refine ⟨209788535476408766773463441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139859023650939177848975627 209788535476408766773463441)
    ·
      refine ⟨157341401607306575080097581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 209788535476408766773463441 157341401607306575080097581)
      ·
        refine ⟨59003025602739965655036593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 157341401607306575080097581 59003025602739965655036593)
        ·
          refine ⟨44252269202054974241277445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59003025602739965655036593 44252269202054974241277445)
          ·
            refine ⟨8297300475385307670239521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 44252269202054974241277445 8297300475385307670239521)
            ·
              refine ⟨6222975356538980752679641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8297300475385307670239521 6222975356538980752679641)
              ·
                refine ⟨4667231517404235564509731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6222975356538980752679641 4667231517404235564509731)
                ·
                  refine ⟨7000847276106353346764597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4667231517404235564509731 7000847276106353346764597)
                  ·
                    refine ⟨656329432134970626259181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7000847276106353346764597 656329432134970626259181)
                    ·
                      rfl

theorem cell23_3834591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 4, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 4, 2, 2, 1, 5].length) (baseStart_3834591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3834591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3834591 prefixEnd_3834591 := by exact prefixLift 3834591
  have htrace : WordTrace (prefixWord ++ tailWord_3834591) baseStart_3834591 baseEnd_3834591 := by
    simpa [prefixWord, tailWord_3834591, baseEnd_3834591] using wordTrace_append hprefix tailTrace_3834591
  have hstable : (prefixWord ++ tailWord_3834591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3834591).length < 2 ^ (prefixWord ++ tailWord_3834591).sum := by decide
  have hdescent : baseEnd_3834591 < baseStart_3834591 := by decide
  rcases family_descends (prefixWord ++ tailWord_3834591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3834621 : List Nat := [1, 4, 1, 1, 1, 1, 4, 4, 2, 4]
def baseStart_3834621 : Nat := 118140960795 + 3834621 * 2 ^ 59
def prefixEnd_3834621 : Nat := 4983230072969 + 3 ^ 40 * 3834621 * 2
def baseEnd_3834621 : Nat := 656334566941515587134135

theorem tailTrace_3834621 : CollatzResearch.WordTrace tailWord_3834621 prefixEnd_3834621 656334566941515587134135 := by
  unfold tailWord_3834621
  simp only [CollatzResearch.WordTrace]
  refine ⟨139860117840830492972567717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93240078560553661981711811 139860117840830492972567717)
  ·
    refine ⟨26223772095155717432356447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 139860117840830492972567717 26223772095155717432356447)
    ·
      refine ⟨39335658142733576148534671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26223772095155717432356447 39335658142733576148534671)
      ·
        refine ⟨59003487214100364222802007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39335658142733576148534671 59003487214100364222802007)
        ·
          refine ⟨88505230821150546334203011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59003487214100364222802007 88505230821150546334203011)
          ·
            refine ⟨132757846231725819501304517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88505230821150546334203011 132757846231725819501304517)
            ·
              refine ⟨24892096168448591156494597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 132757846231725819501304517 24892096168448591156494597)
              ·
                refine ⟨4667268031584110841842737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24892096168448591156494597 4667268031584110841842737)
                ·
                  refine ⟨3500451023688083131382053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4667268031584110841842737 3500451023688083131382053)
                  ·
                    refine ⟨656334566941515587134135, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3500451023688083131382053 656334566941515587134135)
                    ·
                      rfl

theorem cell23_3834621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 4, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 4, 4, 2, 4].length) (baseStart_3834621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3834621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3834621 prefixEnd_3834621 := by exact prefixLift 3834621
  have htrace : WordTrace (prefixWord ++ tailWord_3834621) baseStart_3834621 baseEnd_3834621 := by
    simpa [prefixWord, tailWord_3834621, baseEnd_3834621] using wordTrace_append hprefix tailTrace_3834621
  have hstable : (prefixWord ++ tailWord_3834621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3834621).length < 2 ^ (prefixWord ++ tailWord_3834621).sum := by decide
  have hdescent : baseEnd_3834621 < baseStart_3834621 := by decide
  rcases family_descends (prefixWord ++ tailWord_3834621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3834631 : List Nat := [1, 1, 4, 4, 1, 1, 2, 2, 1, 1, 5]
def baseStart_3834631 : Nat := 118140960795 + 3834631 * 2 ^ 59
def prefixEnd_3834631 : Nat := 4983230072969 + 3 ^ 40 * 3834631 * 2
def baseEnd_3834631 : Nat := 1969008835631091722277359

theorem tailTrace_3834631 : CollatzResearch.WordTrace tailWord_3834631 prefixEnd_3834631 1969008835631091722277359 := by
  unfold tailWord_3834631
  simp only [CollatzResearch.WordTrace]
  refine ⟨139860482570794264680431747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93240321713862843120287831 139860482570794264680431747)
  ·
    refine ⟨209790723856191397020647621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139860482570794264680431747 209790723856191397020647621)
    ·
      refine ⟨39335760723035886941371429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 209790723856191397020647621 39335760723035886941371429)
      ·
        refine ⟨7375455135569228801507143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 39335760723035886941371429 7375455135569228801507143)
        ·
          refine ⟨11063182703353843202260715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7375455135569228801507143 11063182703353843202260715)
          ·
            refine ⟨16594774055030764803391073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11063182703353843202260715 16594774055030764803391073)
            ·
              refine ⟨12446080541273073602543305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16594774055030764803391073 12446080541273073602543305)
              ·
                refine ⟨9334560405954805201907479, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12446080541273073602543305 9334560405954805201907479)
                ·
                  refine ⟨14001840608932207802861219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9334560405954805201907479 14001840608932207802861219)
                  ·
                    refine ⟨21002760913398311704291829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14001840608932207802861219 21002760913398311704291829)
                    ·
                      refine ⟨1969008835631091722277359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21002760913398311704291829 1969008835631091722277359)
                      ·
                        rfl

theorem cell23_3834631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 2, 2, 1, 1, 5].length) (baseStart_3834631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3834631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3834631 prefixEnd_3834631 := by exact prefixLift 3834631
  have htrace : WordTrace (prefixWord ++ tailWord_3834631) baseStart_3834631 baseEnd_3834631 := by
    simpa [prefixWord, tailWord_3834631, baseEnd_3834631] using wordTrace_append hprefix tailTrace_3834631
  have hstable : (prefixWord ++ tailWord_3834631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3834631).length < 2 ^ (prefixWord ++ tailWord_3834631).sum := by decide
  have hdescent : baseEnd_3834631 < baseStart_3834631 := by decide
  rcases family_descends (prefixWord ++ tailWord_3834631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3834634 : List Nat := [3, 1, 2, 2, 1, 2, 4, 8]
def baseStart_3834634 : Nat := 118140960795 + 3834634 * 2 ^ 59
def prefixEnd_3834634 : Nat := 4983230072969 + 3 ^ 40 * 3834634 * 2
def baseEnd_3834634 : Nat := 72926310224927970760735

theorem tailTrace_3834634 : CollatzResearch.WordTrace tailWord_3834634 prefixEnd_3834634 72926310224927970760735 := by
  unfold tailWord_3834634
  simp only [CollatzResearch.WordTrace]
  refine ⟨34965147997445849048197739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93240394659855597461860637 34965147997445849048197739)
  ·
    refine ⟨52447721996168773572296609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34965147997445849048197739 52447721996168773572296609)
    ·
      refine ⟨39335791497126580179222457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52447721996168773572296609 39335791497126580179222457)
      ·
        refine ⟨29501843622844935134416843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39335791497126580179222457 29501843622844935134416843)
        ·
          refine ⟨44252765434267402701625265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29501843622844935134416843 44252765434267402701625265)
          ·
            refine ⟨33189574075700552026218949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44252765434267402701625265 33189574075700552026218949)
            ·
              refine ⟨6223045139193853504916053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33189574075700552026218949 6223045139193853504916053)
              ·
                refine ⟨72926310224927970760735, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6223045139193853504916053 72926310224927970760735)
                ·
                  rfl

theorem cell23_3834634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 4, 8].length) (baseStart_3834634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3834634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3834634 prefixEnd_3834634 := by exact prefixLift 3834634
  have htrace : WordTrace (prefixWord ++ tailWord_3834634) baseStart_3834634 baseEnd_3834634 := by
    simpa [prefixWord, tailWord_3834634, baseEnd_3834634] using wordTrace_append hprefix tailTrace_3834634
  have hstable : (prefixWord ++ tailWord_3834634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3834634).length < 2 ^ (prefixWord ++ tailWord_3834634).sum := by decide
  have hdescent : baseEnd_3834634 < baseStart_3834634 := by decide
  rcases family_descends (prefixWord ++ tailWord_3834634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3834642 : List Nat := [3, 2, 4, 1, 3, 1, 1, 2, 1, 5]
def baseStart_3834642 : Nat := 118140960795 + 3834642 * 2 ^ 59
def prefixEnd_3834642 : Nat := 4983230072969 + 3 ^ 40 * 3834642 * 2
def baseEnd_3834642 : Nat := 656338161306097059746603

theorem tailTrace_3834642 : CollatzResearch.WordTrace tailWord_3834642 prefixEnd_3834642 656338161306097059746603 := by
  unfold tailWord_3834642
  simp only [CollatzResearch.WordTrace]
  refine ⟨34965220943438603389770545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93240589182502942372721453 34965220943438603389770545)
  ·
    refine ⟨26223915707578952542327909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34965220943438603389770545 26223915707578952542327909)
    ·
      refine ⟨4916984195171053601686483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26223915707578952542327909 4916984195171053601686483)
      ·
        refine ⟨7375476292756580402529725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4916984195171053601686483 7375476292756580402529725)
        ·
          refine ⟨2765803609783717650948647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7375476292756580402529725 2765803609783717650948647)
          ·
            refine ⟨4148705414675576476422971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2765803609783717650948647 4148705414675576476422971)
            ·
              refine ⟨6223058122013364714634457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4148705414675576476422971 6223058122013364714634457)
              ·
                refine ⟨4667293591510023535975843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6223058122013364714634457 4667293591510023535975843)
                ·
                  refine ⟨7000940387265035303963765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4667293591510023535975843 7000940387265035303963765)
                  ·
                    refine ⟨656338161306097059746603, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7000940387265035303963765 656338161306097059746603)
                    ·
                      rfl

theorem cell23_3834642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 3, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 3, 1, 1, 2, 1, 5].length) (baseStart_3834642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3834642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3834642 prefixEnd_3834642 := by exact prefixLift 3834642
  have htrace : WordTrace (prefixWord ++ tailWord_3834642) baseStart_3834642 baseEnd_3834642 := by
    simpa [prefixWord, tailWord_3834642, baseEnd_3834642] using wordTrace_append hprefix tailTrace_3834642
  have hstable : (prefixWord ++ tailWord_3834642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3834642).length < 2 ^ (prefixWord ++ tailWord_3834642).sum := by decide
  have hdescent : baseEnd_3834642 < baseStart_3834642 := by decide
  rcases family_descends (prefixWord ++ tailWord_3834642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3834661 : List Nat := [1, 3, 1, 2, 3, 1, 3, 2, 1, 3, 3]
def baseStart_3834661 : Nat := 118140960795 + 3834661 * 2 ^ 59
def prefixEnd_3834661 : Nat := 4983230072969 + 3 ^ 40 * 3834661 * 2
def baseEnd_3834661 : Nat := 1969024240050726604902221

theorem tailTrace_3834661 : CollatzResearch.WordTrace tailWord_3834661 prefixEnd_3834661 1969024240050726604902221 := by
  unfold tailWord_3834661
  simp only [CollatzResearch.WordTrace]
  refine ⟨139861576760685579804023837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93241051173790386536015891 139861576760685579804023837)
  ·
    refine ⟨52448091285257092426508939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 139861576760685579804023837 52448091285257092426508939)
    ·
      refine ⟨78672136927885638639763409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52448091285257092426508939 78672136927885638639763409)
      ·
        refine ⟨59004102695914228979822557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78672136927885638639763409 59004102695914228979822557)
        ·
          refine ⟨22126538510967835867433459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59004102695914228979822557 22126538510967835867433459)
          ·
            refine ⟨33189807766451753801150189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22126538510967835867433459 33189807766451753801150189)
            ·
              refine ⟨12446177912419407675431321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33189807766451753801150189 12446177912419407675431321)
              ·
                refine ⟨9334633434314555756573491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12446177912419407675431321 9334633434314555756573491)
                ·
                  refine ⟨14001950151471833634860237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9334633434314555756573491 14001950151471833634860237)
                  ·
                    refine ⟨5250731306801937613072589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14001950151471833634860237 5250731306801937613072589)
                    ·
                      refine ⟨1969024240050726604902221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5250731306801937613072589 1969024240050726604902221)
                      ·
                        rfl

theorem cell23_3834661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 3, 2, 1, 3, 3].length) (baseStart_3834661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3834661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3834661 prefixEnd_3834661 := by exact prefixLift 3834661
  have htrace : WordTrace (prefixWord ++ tailWord_3834661) baseStart_3834661 baseEnd_3834661 := by
    simpa [prefixWord, tailWord_3834661, baseEnd_3834661] using wordTrace_append hprefix tailTrace_3834661
  have hstable : (prefixWord ++ tailWord_3834661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3834661).length < 2 ^ (prefixWord ++ tailWord_3834661).sum := by decide
  have hdescent : baseEnd_3834661 < baseStart_3834661 := by decide
  rcases family_descends (prefixWord ++ tailWord_3834661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3834671 : List Nat := [1, 1, 2, 1, 2, 1, 2, 1, 7, 3, 2]
def baseStart_3834671 : Nat := 118140960795 + 3834671 * 2 ^ 59
def prefixEnd_3834671 : Nat := 4983230072969 + 3 ^ 40 * 3834671 * 2
def baseEnd_3834671 : Nat := 1969029374857271565777175

theorem tailTrace_3834671 : CollatzResearch.WordTrace tailWord_3834671 prefixEnd_3834671 1969029374857271565777175 := by
  unfold tailWord_3834671
  simp only [CollatzResearch.WordTrace]
  refine ⟨139861941490649351511887867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93241294327099567674591911 139861941490649351511887867)
  ·
    refine ⟨209792912235974027267831801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139861941490649351511887867 209792912235974027267831801)
    ·
      refine ⟨157344684176980520450873851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 209792912235974027267831801 157344684176980520450873851)
      ·
        refine ⟨236017026265470780676310777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157344684176980520450873851 236017026265470780676310777)
        ·
          refine ⟨177012769699103085507233083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 236017026265470780676310777 177012769699103085507233083)
          ·
            refine ⟨265519154548654628260849625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 177012769699103085507233083 265519154548654628260849625)
            ·
              refine ⟨199139365911490971195637219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 265519154548654628260849625 199139365911490971195637219)
              ·
                refine ⟨298709048867236456793455829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 199139365911490971195637219 298709048867236456793455829)
                ·
                  refine ⟨7000993332825854456096621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 298709048867236456793455829 7000993332825854456096621)
                  ·
                    refine ⟨2625372499809695421036233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7000993332825854456096621 2625372499809695421036233)
                    ·
                      refine ⟨1969029374857271565777175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2625372499809695421036233 1969029374857271565777175)
                      ·
                        rfl

theorem cell23_3834671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 1, 7, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 1, 7, 3, 2].length) (baseStart_3834671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3834671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3834671 prefixEnd_3834671 := by exact prefixLift 3834671
  have htrace : WordTrace (prefixWord ++ tailWord_3834671) baseStart_3834671 baseEnd_3834671 := by
    simpa [prefixWord, tailWord_3834671, baseEnd_3834671] using wordTrace_append hprefix tailTrace_3834671
  have hstable : (prefixWord ++ tailWord_3834671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3834671).length < 2 ^ (prefixWord ++ tailWord_3834671).sum := by decide
  have hdescent : baseEnd_3834671 < baseStart_3834671 := by decide
  rcases family_descends (prefixWord ++ tailWord_3834671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3834704 : List Nat := [2, 1, 1, 1, 1, 4, 2, 1, 4, 1, 5]
def baseStart_3834704 : Nat := 118140960795 + 3834704 * 2 ^ 59
def prefixEnd_3834704 : Nat := 4983230072969 + 3 ^ 40 * 3834704 * 2
def baseEnd_3834704 : Nat := 1969046319718869936664523

theorem tailTrace_3834704 : CollatzResearch.WordTrace tailWord_3834704 prefixEnd_3834704 1969046319718869936664523 := by
  unfold tailWord_3834704
  simp only [CollatzResearch.WordTrace]
  refine ⟨69931572549764899073919583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93242096733019865431892777 69931572549764899073919583)
  ·
    refine ⟨104897358824647348610879375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69931572549764899073919583 104897358824647348610879375)
    ·
      refine ⟨157346038236971022916319063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104897358824647348610879375 157346038236971022916319063)
      ·
        refine ⟨236019057355456534374478595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157346038236971022916319063 236019057355456534374478595)
        ·
          refine ⟨354028586033184801561717893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 236019057355456534374478595 354028586033184801561717893)
          ·
            refine ⟨66380359881222150292822105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 354028586033184801561717893 66380359881222150292822105)
            ·
              refine ⟨49785269910916612719616579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66380359881222150292822105 49785269910916612719616579)
              ·
                refine ⟨74677904866374919079424869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49785269910916612719616579 74677904866374919079424869)
                ·
                  refine ⟨14002107162445297327392163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 74677904866374919079424869 14002107162445297327392163)
                  ·
                    refine ⟨21003160743667945991088245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14002107162445297327392163 21003160743667945991088245)
                    ·
                      refine ⟨1969046319718869936664523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21003160743667945991088245 1969046319718869936664523)
                      ·
                        rfl

theorem cell23_3834704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 2, 1, 4, 1, 5].length) (baseStart_3834704 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3834704 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3834704 prefixEnd_3834704 := by exact prefixLift 3834704
  have htrace : WordTrace (prefixWord ++ tailWord_3834704) baseStart_3834704 baseEnd_3834704 := by
    simpa [prefixWord, tailWord_3834704, baseEnd_3834704] using wordTrace_append hprefix tailTrace_3834704
  have hstable : (prefixWord ++ tailWord_3834704).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3834704).length < 2 ^ (prefixWord ++ tailWord_3834704).sum := by decide
  have hdescent : baseEnd_3834704 < baseStart_3834704 := by decide
  rcases family_descends (prefixWord ++ tailWord_3834704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3834722 : List Nat := [3, 3, 2, 1, 3, 1, 1, 3, 1, 3, 2]
def baseStart_3834722 : Nat := 118140960795 + 3834722 * 2 ^ 59
def prefixEnd_3834722 : Nat := 4983230072969 + 3 ^ 40 * 3834722 * 2
def baseEnd_3834722 : Nat := 1969055562370650866239441

theorem tailTrace_3834722 : CollatzResearch.WordTrace tailWord_3834722 prefixEnd_3834722 1969055562370650866239441 := by
  unfold tailWord_3834722
  simp only [CollatzResearch.WordTrace]
  refine ⟨34965950403366146805498605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93242534408976391481329613 34965950403366146805498605)
  ·
    refine ⟨13112231401262305052061977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34965950403366146805498605 13112231401262305052061977)
    ·
      refine ⟨9834173550946728789046483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13112231401262305052061977 9834173550946728789046483)
      ·
        refine ⟨14751260326420093183569725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9834173550946728789046483 14751260326420093183569725)
        ·
          refine ⟨5531722622407534943838647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14751260326420093183569725 5531722622407534943838647)
          ·
            refine ⟨8297583933611302415757971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5531722622407534943838647 8297583933611302415757971)
            ·
              refine ⟨12446375900416953623636957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8297583933611302415757971 12446375900416953623636957)
              ·
                refine ⟨4667390962656357608863859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12446375900416953623636957 4667390962656357608863859)
                ·
                  refine ⟨7001086443984536413295789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4667390962656357608863859 7001086443984536413295789)
                  ·
                    refine ⟨2625407416494201154985921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7001086443984536413295789 2625407416494201154985921)
                    ·
                      refine ⟨1969055562370650866239441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2625407416494201154985921 1969055562370650866239441)
                      ·
                        rfl

theorem cell23_3834722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 1, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 1, 1, 3, 1, 3, 2].length) (baseStart_3834722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3834722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3834722 prefixEnd_3834722 := by exact prefixLift 3834722
  have htrace : WordTrace (prefixWord ++ tailWord_3834722) baseStart_3834722 baseEnd_3834722 := by
    simpa [prefixWord, tailWord_3834722, baseEnd_3834722] using wordTrace_append hprefix tailTrace_3834722
  have hstable : (prefixWord ++ tailWord_3834722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3834722).length < 2 ^ (prefixWord ++ tailWord_3834722).sum := by decide
  have hdescent : baseEnd_3834722 < baseStart_3834722 := by decide
  rcases family_descends (prefixWord ++ tailWord_3834722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3834741 : List Nat := [1, 3, 4, 1, 1, 2, 1, 3, 7]
def baseStart_3834741 : Nat := 118140960795 + 3834741 * 2 ^ 59
def prefixEnd_3834741 : Nat := 4983230072969 + 3 ^ 40 * 3834741 * 2
def baseEnd_3834741 : Nat := 218785035389231810211317

theorem tailTrace_3834741 : CollatzResearch.WordTrace tailWord_3834741 prefixEnd_3834741 218785035389231810211317 := by
  unfold tailWord_3834741
  simp only [CollatzResearch.WordTrace]
  refine ⟨139864494600395753466936077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93242996400263835644624051 139864494600395753466936077)
  ·
    refine ⟨52449185475148407550101029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 139864494600395753466936077 52449185475148407550101029)
    ·
      refine ⟨9834222276590326415643943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 52449185475148407550101029 9834222276590326415643943)
      ·
        refine ⟨14751333414885489623465915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9834222276590326415643943 14751333414885489623465915)
        ·
          refine ⟨22127000122328234435198873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14751333414885489623465915 22127000122328234435198873)
          ·
            refine ⟨16595250091746175826399155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22127000122328234435198873 16595250091746175826399155)
            ·
              refine ⟨24892875137619263739598733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16595250091746175826399155 24892875137619263739598733)
              ·
                refine ⟨9334828176607223902349525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24892875137619263739598733 9334828176607223902349525)
                ·
                  refine ⟨218785035389231810211317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9334828176607223902349525 218785035389231810211317)
                  ·
                    rfl

theorem cell23_3834741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 1, 3, 7].length) (baseStart_3834741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3834741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3834741 prefixEnd_3834741 := by exact prefixLift 3834741
  have htrace : WordTrace (prefixWord ++ tailWord_3834741) baseStart_3834741 baseEnd_3834741 := by
    simpa [prefixWord, tailWord_3834741, baseEnd_3834741] using wordTrace_append hprefix tailTrace_3834741
  have hstable : (prefixWord ++ tailWord_3834741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3834741).length < 2 ^ (prefixWord ++ tailWord_3834741).sum := by decide
  have hdescent : baseEnd_3834741 < baseStart_3834741 := by decide
  rcases family_descends (prefixWord ++ tailWord_3834741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3834751 : List Nat := [1, 1, 2, 2, 1, 1, 6, 1, 2, 3, 3]
def baseStart_3834751 : Nat := 118140960795 + 3834751 * 2 ^ 59
def prefixEnd_3834751 : Nat := 4983230072969 + 3 ^ 40 * 3834751 * 2
def baseEnd_3834751 : Nat := 1969070453309631252776807

theorem tailTrace_3834751 : CollatzResearch.WordTrace tailWord_3834751 prefixEnd_3834751 1969070453309631252776807 := by
  unfold tailWord_3834751
  simp only [CollatzResearch.WordTrace]
  refine ⟨139864859330359525174800107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93243239553573016783200071 139864859330359525174800107)
  ·
    refine ⟨209797288995539287762200161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139864859330359525174800107 209797288995539287762200161)
    ·
      refine ⟨157347966746654465821650121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 209797288995539287762200161 157347966746654465821650121)
      ·
        refine ⟨118010975059990849366237591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 157347966746654465821650121 118010975059990849366237591)
        ·
          refine ⟨177016462589986274049356387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118010975059990849366237591 177016462589986274049356387)
          ·
            refine ⟨265524693884979411074034581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 177016462589986274049356387 265524693884979411074034581)
            ·
              refine ⟨12446470025858409894095371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 265524693884979411074034581 12446470025858409894095371)
              ·
                refine ⟨18669705038787614841143057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12446470025858409894095371 18669705038787614841143057)
                ·
                  refine ⟨14002278779090711130857293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18669705038787614841143057 14002278779090711130857293)
                  ·
                    refine ⟨5250854542159016674071485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14002278779090711130857293 5250854542159016674071485)
                    ·
                      refine ⟨1969070453309631252776807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5250854542159016674071485 1969070453309631252776807)
                      ·
                        rfl

theorem cell23_3834751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 6, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 6, 1, 2, 3, 3].length) (baseStart_3834751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3834751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3834751 prefixEnd_3834751 := by exact prefixLift 3834751
  have htrace : WordTrace (prefixWord ++ tailWord_3834751) baseStart_3834751 baseEnd_3834751 := by
    simpa [prefixWord, tailWord_3834751, baseEnd_3834751] using wordTrace_append hprefix tailTrace_3834751
  have hstable : (prefixWord ++ tailWord_3834751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3834751).length < 2 ^ (prefixWord ++ tailWord_3834751).sum := by decide
  have hdescent : baseEnd_3834751 < baseStart_3834751 := by decide
  rcases family_descends (prefixWord ++ tailWord_3834751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3834781 : List Nat := [1, 4, 2, 1, 2, 1, 2, 2, 1, 2, 5]
def baseStart_3834781 : Nat := 118140960795 + 3834781 * 2 ^ 59
def prefixEnd_3834781 : Nat := 4983230072969 + 3 ^ 40 * 3834781 * 2
def baseEnd_3834781 : Nat := 1969085857729266135401669

theorem tailTrace_3834781 : CollatzResearch.WordTrace tailWord_3834781 prefixEnd_3834781 1969085857729266135401669 := by
  unfold tailWord_3834781
  simp only [CollatzResearch.WordTrace]
  refine ⟨139865953520250840298392197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93243969013500560198928131 139865953520250840298392197)
  ·
    refine ⟨26224866285047032555948537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 139865953520250840298392197 26224866285047032555948537)
    ·
      refine ⟨19668649713785274416961403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26224866285047032555948537 19668649713785274416961403)
      ·
        refine ⟨29502974570677911625442105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19668649713785274416961403 29502974570677911625442105)
        ·
          refine ⟨22127230928008433719081579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29502974570677911625442105 22127230928008433719081579)
          ·
            refine ⟨33190846392012650578622369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22127230928008433719081579 33190846392012650578622369)
            ·
              refine ⟨24893134794009487933966777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33190846392012650578622369 24893134794009487933966777)
              ·
                refine ⟨18669851095507115950475083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24893134794009487933966777 18669851095507115950475083)
                ·
                  refine ⟨28004776643260673925712625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18669851095507115950475083 28004776643260673925712625)
                  ·
                    refine ⟨21003582482445505444284469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28004776643260673925712625 21003582482445505444284469)
                    ·
                      refine ⟨1969085857729266135401669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21003582482445505444284469 1969085857729266135401669)
                      ·
                        rfl

theorem cell23_3834781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 2, 2, 1, 2, 5].length) (baseStart_3834781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3834781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3834781 prefixEnd_3834781 := by exact prefixLift 3834781
  have htrace : WordTrace (prefixWord ++ tailWord_3834781) baseStart_3834781 baseEnd_3834781 := by
    simpa [prefixWord, tailWord_3834781, baseEnd_3834781] using wordTrace_append hprefix tailTrace_3834781
  have hstable : (prefixWord ++ tailWord_3834781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3834781).length < 2 ^ (prefixWord ++ tailWord_3834781).sum := by decide
  have hdescent : baseEnd_3834781 < baseStart_3834781 := by decide
  rcases family_descends (prefixWord ++ tailWord_3834781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3834845 : List Nat := [1, 4, 3, 1, 2, 1, 2, 2, 2, 2, 3]
def baseStart_3834845 : Nat := 118140960795 + 3834845 * 2 ^ 59
def prefixEnd_3834845 : Nat := 4983230072969 + 3 ^ 40 * 3834845 * 2
def baseEnd_3834845 : Nat := 1969118720491153885001375

theorem tailTrace_3834845 : CollatzResearch.WordTrace tailWord_3834845 prefixEnd_3834845 1969118720491153885001375 := by
  unfold tailWord_3834845
  simp only [CollatzResearch.WordTrace]
  refine ⟨139868287792018979228721989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93245525194679319485814659 139868287792018979228721989)
  ·
    refine ⟨26225303961003558605385373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 139868287792018979228721989 26225303961003558605385373)
    ·
      refine ⟨9834488985376334477019515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26225303961003558605385373 9834488985376334477019515)
      ·
        refine ⟨14751733478064501715529273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9834488985376334477019515 14751733478064501715529273)
        ·
          refine ⟨11063800108548376286646955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14751733478064501715529273 11063800108548376286646955)
          ·
            refine ⟨16595700162822564429970433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11063800108548376286646955 16595700162822564429970433)
            ·
              refine ⟨12446775122116923322477825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16595700162822564429970433 12446775122116923322477825)
              ·
                refine ⟨9335081341587692491858369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12446775122116923322477825 9335081341587692491858369)
                ·
                  refine ⟨7001311006190769368893777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9335081341587692491858369 7001311006190769368893777)
                  ·
                    refine ⟨5250983254643077026670333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7001311006190769368893777 5250983254643077026670333)
                    ·
                      refine ⟨1969118720491153885001375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5250983254643077026670333 1969118720491153885001375)
                      ·
                        rfl

theorem cell23_3834845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 2, 2, 2, 2, 3].length) (baseStart_3834845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3834845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3834845 prefixEnd_3834845 := by exact prefixLift 3834845
  have htrace : WordTrace (prefixWord ++ tailWord_3834845) baseStart_3834845 baseEnd_3834845 := by
    simpa [prefixWord, tailWord_3834845, baseEnd_3834845] using wordTrace_append hprefix tailTrace_3834845
  have hstable : (prefixWord ++ tailWord_3834845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3834845).length < 2 ^ (prefixWord ++ tailWord_3834845).sum := by decide
  have hdescent : baseEnd_3834845 < baseStart_3834845 := by decide
  rcases family_descends (prefixWord ++ tailWord_3834845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3834851 : List Nat := [1, 1, 1, 6, 1, 1, 2, 1, 1, 2, 6]
def baseStart_3834851 : Nat := 118140960795 + 3834851 * 2 ^ 59
def prefixEnd_3834851 : Nat := 4983230072969 + 3 ^ 40 * 3834851 * 2
def baseEnd_3834851 : Nat := 1969121801375080861526347

theorem tailTrace_3834851 : CollatzResearch.WordTrace tailWord_3834851 prefixEnd_3834851 1969121801375080861526347 := by
  unfold tailWord_3834851
  simp only [CollatzResearch.WordTrace]
  refine ⟨139868506629997242253440407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93245671086664828168960271 139868506629997242253440407)
  ·
    refine ⟨209802759944995863380160611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139868506629997242253440407 209802759944995863380160611)
    ·
      refine ⟨314704139917493795070240917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209802759944995863380160611 314704139917493795070240917)
      ·
        refine ⟨14751756558632521643917543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 314704139917493795070240917 14751756558632521643917543)
        ·
          refine ⟨22127634837948782465876315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14751756558632521643917543 22127634837948782465876315)
          ·
            refine ⟨33191452256923173698814473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22127634837948782465876315 33191452256923173698814473)
            ·
              refine ⟨24893589192692380274110855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33191452256923173698814473 24893589192692380274110855)
              ·
                refine ⟨37340383789038570411166283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24893589192692380274110855 37340383789038570411166283)
                ·
                  refine ⟨56010575683557855616749425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37340383789038570411166283 56010575683557855616749425)
                  ·
                    refine ⟨42007931762668391712562069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 56010575683557855616749425 42007931762668391712562069)
                    ·
                      refine ⟨1969121801375080861526347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 42007931762668391712562069 1969121801375080861526347)
                      ·
                        rfl

theorem cell23_3834851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 2, 1, 1, 2, 6].length) (baseStart_3834851 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3834851 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3834851 prefixEnd_3834851 := by exact prefixLift 3834851
  have htrace : WordTrace (prefixWord ++ tailWord_3834851) baseStart_3834851 baseEnd_3834851 := by
    simpa [prefixWord, tailWord_3834851, baseEnd_3834851] using wordTrace_append hprefix tailTrace_3834851
  have hstable : (prefixWord ++ tailWord_3834851).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3834851).length < 2 ^ (prefixWord ++ tailWord_3834851).sum := by decide
  have hdescent : baseEnd_3834851 < baseStart_3834851 := by decide
  rcases family_descends (prefixWord ++ tailWord_3834851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3834892 : List Nat := [2, 2, 1, 2, 3, 2, 1, 5, 1, 1, 3]
def baseStart_3834892 : Nat := 118140960795 + 3834892 * 2 ^ 59
def prefixEnd_3834892 : Nat := 4983230072969 + 3 ^ 40 * 3834892 * 2
def baseEnd_3834892 : Nat := 1969142854081915201113659

theorem tailTrace_3834892 : CollatzResearch.WordTrace tailWord_3834892 prefixEnd_3834892 1969142854081915201113659 := by
  unfold tailWord_3834892
  simp only [CollatzResearch.WordTrace]
  refine ⟨69935001011424353127841465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93246668015232470837121953 69935001011424353127841465)
  ·
    refine ⟨52451250758568264845881099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69935001011424353127841465 52451250758568264845881099)
    ·
      refine ⟨78676876137852397268821649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52451250758568264845881099 78676876137852397268821649)
      ·
        refine ⟨59007657103389297951616237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78676876137852397268821649 59007657103389297951616237)
        ·
          refine ⟨22127871413770986731856089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59007657103389297951616237 22127871413770986731856089)
          ·
            refine ⟨16595903560328240048892067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22127871413770986731856089 16595903560328240048892067)
            ·
              refine ⟨24893855340492360073338101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16595903560328240048892067 24893855340492360073338101)
              ·
                refine ⟨2333798938171158756875447, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 24893855340492360073338101 2333798938171158756875447)
                ·
                  refine ⟨3500698407256738135313171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2333798938171158756875447 3500698407256738135313171)
                  ·
                    refine ⟨5251047610885107202969757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3500698407256738135313171 5251047610885107202969757)
                    ·
                      refine ⟨1969142854081915201113659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5251047610885107202969757 1969142854081915201113659)
                      ·
                        rfl

theorem cell23_3834892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 1, 5, 1, 1, 3].length) (baseStart_3834892 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3834892 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3834892 prefixEnd_3834892 := by exact prefixLift 3834892
  have htrace : WordTrace (prefixWord ++ tailWord_3834892) baseStart_3834892 baseEnd_3834892 := by
    simpa [prefixWord, tailWord_3834892, baseEnd_3834892] using wordTrace_append hprefix tailTrace_3834892
  have hstable : (prefixWord ++ tailWord_3834892).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3834892).length < 2 ^ (prefixWord ++ tailWord_3834892).sum := by decide
  have hdescent : baseEnd_3834892 < baseStart_3834892 := by decide
  rcases family_descends (prefixWord ++ tailWord_3834892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3834932 : List Nat := [2, 5, 1, 2, 1, 1, 1, 4, 1, 1, 4]
def baseStart_3834932 : Nat := 118140960795 + 3834932 * 2 ^ 59
def prefixEnd_3834932 : Nat := 4983230072969 + 3 ^ 40 * 3834932 * 2
def baseEnd_3834932 : Nat := 1969163393308095044613475

theorem tailTrace_3834932 : CollatzResearch.WordTrace tailWord_3834932 prefixEnd_3834932 1969163393308095044613475 := by
  unfold tailWord_3834932
  simp only [CollatzResearch.WordTrace]
  refine ⟨69935730471351896543569525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93247640628469195391426033 69935730471351896543569525)
  ·
    refine ⟨6556474731689240300959643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 69935730471351896543569525 6556474731689240300959643)
    ·
      refine ⟨9834712097533860451439465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6556474731689240300959643 9834712097533860451439465)
      ·
        refine ⟨7376034073150395338579599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9834712097533860451439465 7376034073150395338579599)
        ·
          refine ⟨11064051109725593007869399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7376034073150395338579599 11064051109725593007869399)
          ·
            refine ⟨16596076664588389511804099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11064051109725593007869399 16596076664588389511804099)
            ·
              refine ⟨24894114996882584267706149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16596076664588389511804099 24894114996882584267706149)
              ·
                refine ⟨4667646561915484550194903, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24894114996882584267706149 4667646561915484550194903)
                ·
                  refine ⟨7001469842873226825292355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4667646561915484550194903 7001469842873226825292355)
                  ·
                    refine ⟨10502204764309840237938533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7001469842873226825292355 10502204764309840237938533)
                    ·
                      refine ⟨1969163393308095044613475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10502204764309840237938533 1969163393308095044613475)
                      ·
                        rfl

theorem cell23_3834932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 1, 4, 1, 1, 4].length) (baseStart_3834932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3834932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3834932 prefixEnd_3834932 := by exact prefixLift 3834932
  have htrace : WordTrace (prefixWord ++ tailWord_3834932) baseStart_3834932 baseEnd_3834932 := by
    simpa [prefixWord, tailWord_3834932, baseEnd_3834932] using wordTrace_append hprefix tailTrace_3834932
  have hstable : (prefixWord ++ tailWord_3834932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3834932).length < 2 ^ (prefixWord ++ tailWord_3834932).sum := by decide
  have hdescent : baseEnd_3834932 < baseStart_3834932 := by decide
  rcases family_descends (prefixWord ++ tailWord_3834932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3834938 : List Nat := [3, 1, 1, 1, 3, 1, 6, 7]
def baseStart_3834938 : Nat := 118140960795 + 3834938 * 2 ^ 59
def prefixEnd_3834938 : Nat := 4983230072969 + 3 ^ 40 * 3834938 * 2
def baseEnd_3834938 : Nat := 72932091636741556338461

theorem tailTrace_3834938 : CollatzResearch.WordTrace tailWord_3834938 prefixEnd_3834938 72932091636741556338461 := by
  unfold tailWord_3834938
  simp only [CollatzResearch.WordTrace]
  refine ⟨34967919945170514027964367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93247786520454704074571645 34967919945170514027964367)
  ·
    refine ⟨52451879917755771041946551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34967919945170514027964367 52451879917755771041946551)
    ·
      refine ⟨78677819876633656562919827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52451879917755771041946551 78677819876633656562919827)
      ·
        refine ⟨118016729814950484844379741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78677819876633656562919827 118016729814950484844379741)
        ·
          refine ⟨44256273680606431816642403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 118016729814950484844379741 44256273680606431816642403)
          ·
            refine ⟨66384410520909647724963605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44256273680606431816642403 66384410520909647724963605)
            ·
              refine ⟨3111769243167639737107669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 66384410520909647724963605 3111769243167639737107669)
              ·
                refine ⟨72932091636741556338461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3111769243167639737107669 72932091636741556338461)
                ·
                  rfl

theorem cell23_3834938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 6, 7].length) (baseStart_3834938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3834938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3834938 prefixEnd_3834938 := by exact prefixLift 3834938
  have htrace : WordTrace (prefixWord ++ tailWord_3834938) baseStart_3834938 baseEnd_3834938 := by
    simpa [prefixWord, tailWord_3834938, baseEnd_3834938] using wordTrace_append hprefix tailTrace_3834938
  have hstable : (prefixWord ++ tailWord_3834938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3834938).length < 2 ^ (prefixWord ++ tailWord_3834938).sum := by decide
  have hdescent : baseEnd_3834938 < baseStart_3834938 := by decide
  rcases family_descends (prefixWord ++ tailWord_3834938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3834949 : List Nat := [1, 3, 1, 1, 1, 3, 5, 3, 1, 2, 2]
def baseStart_3834949 : Nat := 118140960795 + 3834949 * 2 ^ 59
def prefixEnd_3834949 : Nat := 4983230072969 + 3 ^ 40 * 3834949 * 2
def baseEnd_3834949 : Nat := 1969172122479221478100897

theorem tailTrace_3834949 : CollatzResearch.WordTrace tailWord_3834949 prefixEnd_3834949 1969172122479221478100897 := by
  unfold tailWord_3834949
  simp only [CollatzResearch.WordTrace]
  refine ⟨139872080983642204990507901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93248053989094803327005267 139872080983642204990507901)
  ·
    refine ⟨52452030368865826871440463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 139872080983642204990507901 52452030368865826871440463)
    ·
      refine ⟨78678045553298740307160695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52452030368865826871440463 78678045553298740307160695)
      ·
        refine ⟨118017068329948110460741043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78678045553298740307160695 118017068329948110460741043)
        ·
          refine ⟨177025602494922165691111565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118017068329948110460741043 177025602494922165691111565)
          ·
            refine ⟨66384600935595812134166837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 177025602494922165691111565 66384600935595812134166837)
            ·
              refine ⟨6223556337712107387578141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 66384600935595812134166837 6223556337712107387578141)
              ·
                refine ⟨2333833626642040270341803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6223556337712107387578141 2333833626642040270341803)
                ·
                  refine ⟨3500750439963060405512705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2333833626642040270341803 3500750439963060405512705)
                  ·
                    refine ⟨2625562829972295304134529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3500750439963060405512705 2625562829972295304134529)
                    ·
                      refine ⟨1969172122479221478100897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2625562829972295304134529 1969172122479221478100897)
                      ·
                        rfl

theorem cell23_3834949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 5, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 5, 3, 1, 2, 2].length) (baseStart_3834949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3834949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3834949 prefixEnd_3834949 := by exact prefixLift 3834949
  have htrace : WordTrace (prefixWord ++ tailWord_3834949) baseStart_3834949 baseEnd_3834949 := by
    simpa [prefixWord, tailWord_3834949, baseEnd_3834949] using wordTrace_append hprefix tailTrace_3834949
  have hstable : (prefixWord ++ tailWord_3834949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3834949).length < 2 ^ (prefixWord ++ tailWord_3834949).sum := by decide
  have hdescent : baseEnd_3834949 < baseStart_3834949 := by decide
  rcases family_descends (prefixWord ++ tailWord_3834949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3834965 : List Nat := [1, 3, 2, 2, 1, 2, 1, 3, 4, 1, 3]
def baseStart_3834965 : Nat := 118140960795 + 3834965 * 2 ^ 59
def prefixEnd_3834965 : Nat := 4983230072969 + 3 ^ 40 * 3834965 * 2
def baseEnd_3834965 : Nat := 1969180338169693415500823

theorem tailTrace_3834965 : CollatzResearch.WordTrace tailWord_3834965 prefixEnd_3834965 1969180338169693415500823 := by
  unfold tailWord_3834965
  simp only [CollatzResearch.WordTrace]
  refine ⟨139872664551584239723090349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93248443034389493148726899 139872664551584239723090349)
  ·
    refine ⟨52452249206844089896158881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 139872664551584239723090349 52452249206844089896158881)
    ·
      refine ⟨39339186905133067422119161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52452249206844089896158881 39339186905133067422119161)
      ·
        refine ⟨29504390178849800566589371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39339186905133067422119161 29504390178849800566589371)
        ·
          refine ⟨44256585268274700849884057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29504390178849800566589371 44256585268274700849884057)
          ·
            refine ⟨33192438951206025637413043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44256585268274700849884057 33192438951206025637413043)
            ·
              refine ⟨49788658426809038456119565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33192438951206025637413043 49788658426809038456119565)
              ·
                refine ⟨18670746910053389421044837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49788658426809038456119565 18670746910053389421044837)
                ·
                  refine ⟨3500765045635010516445907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18670746910053389421044837 3500765045635010516445907)
                  ·
                    refine ⟨5251147568452515774668861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3500765045635010516445907 5251147568452515774668861)
                    ·
                      refine ⟨1969180338169693415500823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5251147568452515774668861 1969180338169693415500823)
                      ·
                        rfl

theorem cell23_3834965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 1, 3, 4, 1, 3].length) (baseStart_3834965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3834965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3834965 prefixEnd_3834965 := by exact prefixLift 3834965
  have htrace : WordTrace (prefixWord ++ tailWord_3834965) baseStart_3834965 baseEnd_3834965 := by
    simpa [prefixWord, tailWord_3834965, baseEnd_3834965] using wordTrace_append hprefix tailTrace_3834965
  have hstable : (prefixWord ++ tailWord_3834965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3834965).length < 2 ^ (prefixWord ++ tailWord_3834965).sum := by decide
  have hdescent : baseEnd_3834965 < baseStart_3834965 := by decide
  rcases family_descends (prefixWord ++ tailWord_3834965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3834975 : List Nat := [1, 1, 2, 3, 1, 1, 4, 2, 3, 3, 2]
def baseStart_3834975 : Nat := 118140960795 + 3834975 * 2 ^ 59
def prefixEnd_3834975 : Nat := 4983230072969 + 3 ^ 40 * 3834975 * 2
def baseEnd_3834975 : Nat := 1969185472976238376375777

theorem tailTrace_3834975 : CollatzResearch.WordTrace tailWord_3834975 prefixEnd_3834975 1969185472976238376375777 := by
  unfold tailWord_3834975
  simp only [CollatzResearch.WordTrace]
  refine ⟨139873029281548011430954379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93248686187698674287302919 139873029281548011430954379)
  ·
    refine ⟨209809543922322017146431569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139873029281548011430954379 209809543922322017146431569)
    ·
      refine ⟨157357157941741512859823677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 209809543922322017146431569 157357157941741512859823677)
      ·
        refine ⟨59008934228153067322433879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 157357157941741512859823677 59008934228153067322433879)
        ·
          refine ⟨88513401342229600983650819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59008934228153067322433879 88513401342229600983650819)
          ·
            refine ⟨132770102013344401475476229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88513401342229600983650819 132770102013344401475476229)
            ·
              refine ⟨24894394127502075276651793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 132770102013344401475476229 24894394127502075276651793)
              ·
                refine ⟨18670795595626556457488845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24894394127502075276651793 18670795595626556457488845)
                ·
                  refine ⟨7001548348359958671558317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18670795595626556457488845 7001548348359958671558317)
                  ·
                    refine ⟨2625580630634984501834369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7001548348359958671558317 2625580630634984501834369)
                    ·
                      refine ⟨1969185472976238376375777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2625580630634984501834369 1969185472976238376375777)
                      ·
                        rfl

theorem cell23_3834975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 4, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 4, 2, 3, 3, 2].length) (baseStart_3834975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3834975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3834975 prefixEnd_3834975 := by exact prefixLift 3834975
  have htrace : WordTrace (prefixWord ++ tailWord_3834975) baseStart_3834975 baseEnd_3834975 := by
    simpa [prefixWord, tailWord_3834975, baseEnd_3834975] using wordTrace_append hprefix tailTrace_3834975
  have hstable : (prefixWord ++ tailWord_3834975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3834975).length < 2 ^ (prefixWord ++ tailWord_3834975).sum := by decide
  have hdescent : baseEnd_3834975 < baseStart_3834975 := by decide
  rcases family_descends (prefixWord ++ tailWord_3834975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3835008 : List Nat := [2, 1, 1, 2, 1, 3, 4, 1, 2, 1, 5]
def baseStart_3835008 : Nat := 118140960795 + 3835008 * 2 ^ 59
def prefixEnd_3835008 : Nat := 4983230072969 + 3 ^ 40 * 3835008 * 2
def baseEnd_3835008 : Nat := 1969202417837836747263125

theorem tailTrace_3835008 : CollatzResearch.WordTrace tailWord_3835008 prefixEnd_3835008 1969202417837836747263125 := by
  unfold tailWord_3835008
  simp only [CollatzResearch.WordTrace]
  refine ⟨69937116445214229033452839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93249488593618972044603785 69937116445214229033452839)
  ·
    refine ⟨104905674667821343550179259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69937116445214229033452839 104905674667821343550179259)
    ·
      refine ⟨157358512001732015325268889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104905674667821343550179259 157358512001732015325268889)
      ·
        refine ⟨118018884001299011493951667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 157358512001732015325268889 118018884001299011493951667)
        ·
          refine ⟨177028326001948517240927501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118018884001299011493951667 177028326001948517240927501)
          ·
            refine ⟨66385622250730693965347813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 177028326001948517240927501 66385622250730693965347813)
            ·
              refine ⟨12447304172012005118502715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 66385622250730693965347813 12447304172012005118502715)
              ·
                refine ⟨18670956258018007677754073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12447304172012005118502715 18670956258018007677754073)
                ·
                  refine ⟨14003217193513505758315555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18670956258018007677754073 14003217193513505758315555)
                  ·
                    refine ⟨21004825790270258637473333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14003217193513505758315555 21004825790270258637473333)
                    ·
                      refine ⟨1969202417837836747263125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21004825790270258637473333 1969202417837836747263125)
                      ·
                        rfl

theorem cell23_3835008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 4, 1, 2, 1, 5].length) (baseStart_3835008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3835008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3835008 prefixEnd_3835008 := by exact prefixLift 3835008
  have htrace : WordTrace (prefixWord ++ tailWord_3835008) baseStart_3835008 baseEnd_3835008 := by
    simpa [prefixWord, tailWord_3835008, baseEnd_3835008] using wordTrace_append hprefix tailTrace_3835008
  have hstable : (prefixWord ++ tailWord_3835008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3835008).length < 2 ^ (prefixWord ++ tailWord_3835008).sum := by decide
  have hdescent : baseEnd_3835008 < baseStart_3835008 := by decide
  rcases family_descends (prefixWord ++ tailWord_3835008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3835039 : List Nat := [1, 1, 2, 6, 2, 1, 2, 1, 1, 4, 2]
def baseStart_3835039 : Nat := 118140960795 + 3835039 * 2 ^ 59
def prefixEnd_3835039 : Nat := 4983230072969 + 3 ^ 40 * 3835039 * 2
def baseEnd_3835039 : Nat := 1969218335738126125975483

theorem tailTrace_3835039 : CollatzResearch.WordTrace tailWord_3835039 prefixEnd_3835039 1969218335738126125975483 := by
  unfold tailWord_3835039
  simp only [CollatzResearch.WordTrace]
  refine ⟨139875363553316150361284171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93250242368877433574189447 139875363553316150361284171)
  ·
    refine ⟨209813045329974225541926257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139875363553316150361284171 209813045329974225541926257)
    ·
      refine ⟨157359783997480669156444693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 209813045329974225541926257 157359783997480669156444693)
      ·
        refine ⟨7376239874881906366708345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 157359783997480669156444693 7376239874881906366708345)
        ·
          refine ⟨5532179906161429775031259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7376239874881906366708345 5532179906161429775031259)
          ·
            refine ⟨8298269859242144662546889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5532179906161429775031259 8298269859242144662546889)
            ·
              refine ⟨6223702394431608496910167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8298269859242144662546889 6223702394431608496910167)
              ·
                refine ⟨9335553591647412745365251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6223702394431608496910167 9335553591647412745365251)
                ·
                  refine ⟨14003330387471119118047877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9335553591647412745365251 14003330387471119118047877)
                  ·
                    refine ⟨2625624447650834834633977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14003330387471119118047877 2625624447650834834633977)
                    ·
                      refine ⟨1969218335738126125975483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2625624447650834834633977 1969218335738126125975483)
                      ·
                        rfl

theorem cell23_3835039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 1, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 1, 2, 1, 1, 4, 2].length) (baseStart_3835039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3835039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3835039 prefixEnd_3835039 := by exact prefixLift 3835039
  have htrace : WordTrace (prefixWord ++ tailWord_3835039) baseStart_3835039 baseEnd_3835039 := by
    simpa [prefixWord, tailWord_3835039, baseEnd_3835039] using wordTrace_append hprefix tailTrace_3835039
  have hstable : (prefixWord ++ tailWord_3835039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3835039).length < 2 ^ (prefixWord ++ tailWord_3835039).sum := by decide
  have hdescent : baseEnd_3835039 < baseStart_3835039 := by decide
  rcases family_descends (prefixWord ++ tailWord_3835039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3835073 : List Nat := [1, 2, 6, 1, 1, 3, 1, 2, 2, 2, 2]
def baseStart_3835073 : Nat := 118140960795 + 3835073 * 2 ^ 59
def prefixEnd_3835073 : Nat := 4983230072969 + 3 ^ 40 * 3835073 * 2
def baseEnd_3835073 : Nat := 1969235794080378992950327

theorem tailTrace_3835073 : CollatzResearch.WordTrace tailWord_3835073 prefixEnd_3835073 1969235794080378992950327 := by
  unfold tailWord_3835073
  simp only [CollatzResearch.WordTrace]
  refine ⟨139876603635192974168021873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93251069090128649445347915 139876603635192974168021873)
  ·
    refine ⟨104907452726394730626016405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139876603635192974168021873 104907452726394730626016405)
    ·
      refine ⟨4917536846549752998094519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 104907452726394730626016405 4917536846549752998094519)
      ·
        refine ⟨7376305269824629497141779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4917536846549752998094519 7376305269824629497141779)
        ·
          refine ⟨11064457904736944245712669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7376305269824629497141779 11064457904736944245712669)
          ·
            refine ⟨4149171714276354092142251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11064457904736944245712669 4149171714276354092142251)
            ·
              refine ⟨6223757571414531138213377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4149171714276354092142251 6223757571414531138213377)
              ·
                refine ⟨4667818178560898353660033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6223757571414531138213377 4667818178560898353660033)
                ·
                  refine ⟨3500863633920673765245025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4667818178560898353660033 3500863633920673765245025)
                  ·
                    refine ⟨2625647725440505323933769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3500863633920673765245025 2625647725440505323933769)
                    ·
                      refine ⟨1969235794080378992950327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2625647725440505323933769 1969235794080378992950327)
                      ·
                        rfl

theorem cell23_3835073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 3, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 3, 1, 2, 2, 2, 2].length) (baseStart_3835073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3835073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3835073 prefixEnd_3835073 := by exact prefixLift 3835073
  have htrace : WordTrace (prefixWord ++ tailWord_3835073) baseStart_3835073 baseEnd_3835073 := by
    simpa [prefixWord, tailWord_3835073, baseEnd_3835073] using wordTrace_append hprefix tailTrace_3835073
  have hstable : (prefixWord ++ tailWord_3835073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3835073).length < 2 ^ (prefixWord ++ tailWord_3835073).sum := by decide
  have hdescent : baseEnd_3835073 < baseStart_3835073 := by decide
  rcases family_descends (prefixWord ++ tailWord_3835073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3835115 : List Nat := [1, 1, 1, 1, 2, 6, 2, 1, 1, 4, 3]
def baseStart_3835115 : Nat := 118140960795 + 3835115 * 2 ^ 59
def prefixEnd_3835115 : Nat := 4983230072969 + 3 ^ 40 * 3835115 * 2
def baseEnd_3835115 : Nat := 1969257360267867828625133

theorem tailTrace_3835115 : CollatzResearch.WordTrace tailWord_3835115 prefixEnd_3835115 1969257360267867828625133 := by
  unfold tailWord_3835115
  simp only [CollatzResearch.WordTrace]
  refine ⟨139878135501040815341050799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93252090334027210227367199 139878135501040815341050799)
  ·
    refine ⟨209817203251561223011576199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139878135501040815341050799 209817203251561223011576199)
    ·
      refine ⟨314725804877341834517364299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209817203251561223011576199 314725804877341834517364299)
      ·
        refine ⟨472088707316012751776046449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 314725804877341834517364299 472088707316012751776046449)
        ·
          refine ⟨354066530487009563832034837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 472088707316012751776046449 354066530487009563832034837)
          ·
            refine ⟨16596868616578573304626633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 354066530487009563832034837 16596868616578573304626633)
            ·
              refine ⟨12447651462433929978469975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16596868616578573304626633 12447651462433929978469975)
              ·
                refine ⟨18671477193650894967704963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12447651462433929978469975 18671477193650894967704963)
                ·
                  refine ⟨28007215790476342451557445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18671477193650894967704963 28007215790476342451557445)
                  ·
                    refine ⟨5251352960714314209667021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28007215790476342451557445 5251352960714314209667021)
                    ·
                      refine ⟨1969257360267867828625133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5251352960714314209667021 1969257360267867828625133)
                      ·
                        rfl

theorem cell23_3835115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 2, 1, 1, 4, 3].length) (baseStart_3835115 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3835115 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3835115 prefixEnd_3835115 := by exact prefixLift 3835115
  have htrace : WordTrace (prefixWord ++ tailWord_3835115) baseStart_3835115 baseEnd_3835115 := by
    simpa [prefixWord, tailWord_3835115, baseEnd_3835115] using wordTrace_append hprefix tailTrace_3835115
  have hstable : (prefixWord ++ tailWord_3835115).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3835115).length < 2 ^ (prefixWord ++ tailWord_3835115).sum := by decide
  have hdescent : baseEnd_3835115 < baseStart_3835115 := by decide
  rcases family_descends (prefixWord ++ tailWord_3835115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3835189 : List Nat := [1, 3, 3, 1, 2, 2, 2, 2, 2, 3, 2]
def baseStart_3835189 : Nat := 118140960795 + 3835189 * 2 ^ 59
def prefixEnd_3835189 : Nat := 4983230072969 + 3 ^ 40 * 3835189 * 2
def baseEnd_3835189 : Nat := 1969295357836300539099793

theorem tailTrace_3835189 : CollatzResearch.WordTrace tailWord_3835189 prefixEnd_3835189 1969295357836300539099793 := by
  unfold tailWord_3835189
  simp only [CollatzResearch.WordTrace]
  refine ⟨139880834502772725979244621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93253889668515150652829747 139880834502772725979244621)
  ·
    refine ⟨52455312938539772242216733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 139880834502772725979244621 52455312938539772242216733)
    ·
      refine ⟨19670742351952414590831275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52455312938539772242216733 19670742351952414590831275)
      ·
        refine ⟨29506113527928621886246913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19670742351952414590831275 29506113527928621886246913)
        ·
          refine ⟨22129585145946466414685185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29506113527928621886246913 22129585145946466414685185)
          ·
            refine ⟨16597188859459849811013889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22129585145946466414685185 16597188859459849811013889)
            ·
              refine ⟨12447891644594887358260417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16597188859459849811013889 12447891644594887358260417)
              ·
                refine ⟨9335918733446165518695313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12447891644594887358260417 9335918733446165518695313)
                ·
                  refine ⟨7001939050084624139021485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9335918733446165518695313 7001939050084624139021485)
                  ·
                    refine ⟨2625727143781734052133057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7001939050084624139021485 2625727143781734052133057)
                    ·
                      refine ⟨1969295357836300539099793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2625727143781734052133057 1969295357836300539099793)
                      ·
                        rfl

theorem cell23_3835189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 2, 2, 2, 3, 2].length) (baseStart_3835189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3835189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3835189 prefixEnd_3835189 := by exact prefixLift 3835189
  have htrace : WordTrace (prefixWord ++ tailWord_3835189) baseStart_3835189 baseEnd_3835189 := by
    simpa [prefixWord, tailWord_3835189, baseEnd_3835189] using wordTrace_append hprefix tailTrace_3835189
  have hstable : (prefixWord ++ tailWord_3835189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3835189).length < 2 ^ (prefixWord ++ tailWord_3835189).sum := by decide
  have hdescent : baseEnd_3835189 < baseStart_3835189 := by decide
  rcases family_descends (prefixWord ++ tailWord_3835189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3835195 : List Nat := [1, 1, 1, 1, 1, 2, 1, 1, 10, 4]
def baseStart_3835195 : Nat := 118140960795 + 3835195 * 2 ^ 59
def prefixEnd_3835195 : Nat := 4983230072969 + 3 ^ 40 * 3835195 * 2
def baseEnd_3835195 : Nat := 656432812906742505208255

theorem tailTrace_3835195 : CollatzResearch.WordTrace tailWord_3835195 prefixEnd_3835195 656432812906742505208255 := by
  unfold tailWord_3835195
  simp only [CollatzResearch.WordTrace]
  refine ⟨139881053340750989003963039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93254035560500659335975359 139881053340750989003963039)
  ·
    refine ⟨209821580011126483505944559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139881053340750989003963039 209821580011126483505944559)
    ·
      refine ⟨314732370016689725258916839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209821580011126483505944559 314732370016689725258916839)
      ·
        refine ⟨472098555025034587888375259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 314732370016689725258916839 472098555025034587888375259)
        ·
          refine ⟨708147832537551881832562889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 472098555025034587888375259 708147832537551881832562889)
          ·
            refine ⟨531110874403163911374422167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 708147832537551881832562889 531110874403163911374422167)
            ·
              refine ⟨796666311604745867061633251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 531110874403163911374422167 796666311604745867061633251)
              ·
                refine ⟨1194999467407118800592449877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 796666311604745867061633251 1194999467407118800592449877)
                ·
                  refine ⟨3500975002169293361110693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 1194999467407118800592449877 3500975002169293361110693)
                  ·
                    refine ⟨656432812906742505208255, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3500975002169293361110693 656432812906742505208255)
                    ·
                      rfl

theorem cell23_3835195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 10, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 10, 4].length) (baseStart_3835195 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3835195 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3835195 prefixEnd_3835195 := by exact prefixLift 3835195
  have htrace : WordTrace (prefixWord ++ tailWord_3835195) baseStart_3835195 baseEnd_3835195 := by
    simpa [prefixWord, tailWord_3835195, baseEnd_3835195] using wordTrace_append hprefix tailTrace_3835195
  have hstable : (prefixWord ++ tailWord_3835195).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3835195).length < 2 ^ (prefixWord ++ tailWord_3835195).sum := by decide
  have hdescent : baseEnd_3835195 < baseStart_3835195 := by decide
  rcases family_descends (prefixWord ++ tailWord_3835195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3835196 : List Nat := [2, 2, 2, 2, 1, 4, 1, 4, 1, 1, 3]
def baseStart_3835196 : Nat := 118140960795 + 3835196 * 2 ^ 59
def prefixEnd_3835196 : Nat := 4983230072969 + 3 ^ 40 * 3835196 * 2
def baseEnd_3835196 : Nat := 1969298952200882011712261

theorem tailTrace_3835196 : CollatzResearch.WordTrace tailWord_3835196 prefixEnd_3835196 1969298952200882011712261 := by
  unfold tailWord_3835196
  simp only [CollatzResearch.WordTrace]
  refine ⟨69940544906873683087374721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93254059875831577449832961 69940544906873683087374721)
  ·
    refine ⟨52455408680155262315531041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69940544906873683087374721 52455408680155262315531041)
    ·
      refine ⟨39341556510116446736648281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52455408680155262315531041 39341556510116446736648281)
      ·
        refine ⟨29506167382587335052486211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39341556510116446736648281 29506167382587335052486211)
        ·
          refine ⟨44259251073881002578729317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29506167382587335052486211 44259251073881002578729317)
          ·
            refine ⟨8298609576352687983511747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 44259251073881002578729317 8298609576352687983511747)
            ·
              refine ⟨12447914364529031975267621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8298609576352687983511747 12447914364529031975267621)
              ·
                refine ⟨2333983943349193495362679, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12447914364529031975267621 2333983943349193495362679)
                ·
                  refine ⟨3500975915023790243044019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2333983943349193495362679 3500975915023790243044019)
                  ·
                    refine ⟨5251463872535685364566029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3500975915023790243044019 5251463872535685364566029)
                    ·
                      refine ⟨1969298952200882011712261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5251463872535685364566029 1969298952200882011712261)
                      ·
                        rfl

theorem cell23_3835196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 4, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 4, 1, 4, 1, 1, 3].length) (baseStart_3835196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3835196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3835196 prefixEnd_3835196 := by exact prefixLift 3835196
  have htrace : WordTrace (prefixWord ++ tailWord_3835196) baseStart_3835196 baseEnd_3835196 := by
    simpa [prefixWord, tailWord_3835196, baseEnd_3835196] using wordTrace_append hprefix tailTrace_3835196
  have hstable : (prefixWord ++ tailWord_3835196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3835196).length < 2 ^ (prefixWord ++ tailWord_3835196).sum := by decide
  have hdescent : baseEnd_3835196 < baseStart_3835196 := by decide
  rcases family_descends (prefixWord ++ tailWord_3835196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3835205 : List Nat := [1, 3, 1, 1, 1, 2, 1, 6, 1, 1, 5]
def baseStart_3835205 : Nat := 118140960795 + 3835205 * 2 ^ 59
def prefixEnd_3835205 : Nat := 4983230072969 + 3 ^ 40 * 3835205 * 2
def baseEnd_3835205 : Nat := 1969303573526772476499719

theorem tailTrace_3835205 : CollatzResearch.WordTrace tailWord_3835205 prefixEnd_3835205 1969303573526772476499719 := by
  unfold tailWord_3835205
  simp only [CollatzResearch.WordTrace]
  refine ⟨139881418070714760711827069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93254278713809840474551379 139881418070714760711827069)
  ·
    refine ⟨52455531776518035266935151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 139881418070714760711827069 52455531776518035266935151)
    ·
      refine ⟨78683297664777052900402727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52455531776518035266935151 78683297664777052900402727)
      ·
        refine ⟨118024946497165579350604091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78683297664777052900402727 118024946497165579350604091)
        ·
          refine ⟨177037419745748369025906137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118024946497165579350604091 177037419745748369025906137)
          ·
            refine ⟨132778064809311276769429603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 177037419745748369025906137 132778064809311276769429603)
            ·
              refine ⟨199167097213966915154144405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 132778064809311276769429603 199167097213966915154144405)
              ·
                refine ⟨9335957681904699147850519, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 199167097213966915154144405 9335957681904699147850519)
                ·
                  refine ⟨14003936522857048721775779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9335957681904699147850519 14003936522857048721775779)
                  ·
                    refine ⟨21005904784285573082663669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14003936522857048721775779 21005904784285573082663669)
                    ·
                      refine ⟨1969303573526772476499719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21005904784285573082663669 1969303573526772476499719)
                      ·
                        rfl

theorem cell23_3835205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 6, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 6, 1, 1, 5].length) (baseStart_3835205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3835205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3835205 prefixEnd_3835205 := by exact prefixLift 3835205
  have htrace : WordTrace (prefixWord ++ tailWord_3835205) baseStart_3835205 baseEnd_3835205 := by
    simpa [prefixWord, tailWord_3835205, baseEnd_3835205] using wordTrace_append hprefix tailTrace_3835205
  have hstable : (prefixWord ++ tailWord_3835205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3835205).length < 2 ^ (prefixWord ++ tailWord_3835205).sum := by decide
  have hdescent : baseEnd_3835205 < baseStart_3835205 := by decide
  rcases family_descends (prefixWord ++ tailWord_3835205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3835212 : List Nat := [2, 2, 1, 3, 2, 3, 2, 1, 1, 6]
def baseStart_3835212 : Nat := 118140960795 + 3835212 * 2 ^ 59
def prefixEnd_3835212 : Nat := 4983230072969 + 3 ^ 40 * 3835212 * 2
def baseEnd_3835212 : Nat := 656435722630451316370729

theorem tailTrace_3835212 : CollatzResearch.WordTrace tailWord_3835212 prefixEnd_3835212 656435722630451316370729 := by
  unfold tailWord_3835212
  simp only [CollatzResearch.WordTrace]
  refine ⟨69940836690844700453665945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93254448921126267271554593 69940836690844700453665945)
  ·
    refine ⟨52455627518133525340249459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69940836690844700453665945 52455627518133525340249459)
    ·
      refine ⟨78683441277200288010374189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52455627518133525340249459 78683441277200288010374189)
      ·
        refine ⟨29506290478950108003890321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 78683441277200288010374189 29506290478950108003890321)
        ·
          refine ⟨22129717859212581002917741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29506290478950108003890321 22129717859212581002917741)
          ·
            refine ⟨8298644197204717876094153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22129717859212581002917741 8298644197204717876094153)
            ·
              refine ⟨6223983147903538407070615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8298644197204717876094153 6223983147903538407070615)
              ·
                refine ⟨9335974721855307610605923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6223983147903538407070615 9335974721855307610605923)
                ·
                  refine ⟨14003962082782961415908885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9335974721855307610605923 14003962082782961415908885)
                  ·
                    refine ⟨656435722630451316370729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14003962082782961415908885 656435722630451316370729)
                    ·
                      rfl

theorem cell23_3835212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 3, 2, 1, 1, 6].length) (baseStart_3835212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3835212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3835212 prefixEnd_3835212 := by exact prefixLift 3835212
  have htrace : WordTrace (prefixWord ++ tailWord_3835212) baseStart_3835212 baseEnd_3835212 := by
    simpa [prefixWord, tailWord_3835212, baseEnd_3835212] using wordTrace_append hprefix tailTrace_3835212
  have hstable : (prefixWord ++ tailWord_3835212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3835212).length < 2 ^ (prefixWord ++ tailWord_3835212).sum := by decide
  have hdescent : baseEnd_3835212 < baseStart_3835212 := by decide
  rcases family_descends (prefixWord ++ tailWord_3835212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3835213 : List Nat := [1, 6, 1, 3, 1, 1, 1, 2, 3, 1, 3]
def baseStart_3835213 : Nat := 118140960795 + 3835213 * 2 ^ 59
def prefixEnd_3835213 : Nat := 4983230072969 + 3 ^ 40 * 3835213 * 2
def baseEnd_3835213 : Nat := 1969307681372008445199683

theorem tailTrace_3835213 : CollatzResearch.WordTrace tailWord_3835213 prefixEnd_3835213 1969307681372008445199683 := by
  unfold tailWord_3835213
  simp only [CollatzResearch.WordTrace]
  refine ⟨139881709854685778078118293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93254473236457185385412195 139881709854685778078118293)
  ·
    refine ⟨6556955149438395847411795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 139881709854685778078118293 6556955149438395847411795)
    ·
      refine ⟨9835432724157593771117693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6556955149438395847411795 9835432724157593771117693)
      ·
        refine ⟨3688287271559097664169135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9835432724157593771117693 3688287271559097664169135)
        ·
          refine ⟨5532430907338646496253703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3688287271559097664169135 5532430907338646496253703)
          ·
            refine ⟨8298646361007969744380555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5532430907338646496253703 8298646361007969744380555)
            ·
              refine ⟨12447969541511954616570833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8298646361007969744380555 12447969541511954616570833)
              ·
                refine ⟨9335977156133965962428125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12447969541511954616570833 9335977156133965962428125)
                ·
                  refine ⟨3500991433550237235910547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9335977156133965962428125 3500991433550237235910547)
                  ·
                    refine ⟨5251487150325355853865821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3500991433550237235910547 5251487150325355853865821)
                    ·
                      refine ⟨1969307681372008445199683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5251487150325355853865821 1969307681372008445199683)
                      ·
                        rfl

theorem cell23_3835213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 1, 1, 2, 3, 1, 3].length) (baseStart_3835213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3835213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3835213 prefixEnd_3835213 := by exact prefixLift 3835213
  have htrace : WordTrace (prefixWord ++ tailWord_3835213) baseStart_3835213 baseEnd_3835213 := by
    simpa [prefixWord, tailWord_3835213, baseEnd_3835213] using wordTrace_append hprefix tailTrace_3835213
  have hstable : (prefixWord ++ tailWord_3835213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3835213).length < 2 ^ (prefixWord ++ tailWord_3835213).sum := by decide
  have hdescent : baseEnd_3835213 < baseStart_3835213 := by decide
  rcases family_descends (prefixWord ++ tailWord_3835213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3835219 : List Nat := [1, 1, 1, 2, 1, 1, 7, 2, 3, 2, 2]
def baseStart_3835219 : Nat := 118140960795 + 3835219 * 2 ^ 59
def prefixEnd_3835219 : Nat := 4983230072969 + 3 ^ 40 * 3835219 * 2
def baseEnd_3835219 : Nat := 1969310762255935421724655

theorem tailTrace_3835219 : CollatzResearch.WordTrace tailWord_3835219 prefixEnd_3835219 1969310762255935421724655 := by
  unfold tailWord_3835219
  simp only [CollatzResearch.WordTrace]
  refine ⟨139881928692664041102836711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93254619128442694068557807 139881928692664041102836711)
  ·
    refine ⟨209822893038996061654255067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139881928692664041102836711 209822893038996061654255067)
    ·
      refine ⟨314734339558494092481382601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209822893038996061654255067 314734339558494092481382601)
      ·
        refine ⟨236050754668870569361036951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 314734339558494092481382601 236050754668870569361036951)
        ·
          refine ⟨354076132003305854041555427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 236050754668870569361036951 354076132003305854041555427)
          ·
            refine ⟨531114198004958781062333141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 354076132003305854041555427 531114198004958781062333141)
            ·
              refine ⟨12447989015741221431148433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 531114198004958781062333141 12447989015741221431148433)
              ·
                refine ⟨9335991761805916073361325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12447989015741221431148433 9335991761805916073361325)
                ·
                  refine ⟨3500996910677218527510497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9335991761805916073361325 3500996910677218527510497)
                  ·
                    refine ⟨2625747683007913895632873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3500996910677218527510497 2625747683007913895632873)
                    ·
                      refine ⟨1969310762255935421724655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2625747683007913895632873 1969310762255935421724655)
                      ·
                        rfl

theorem cell23_3835219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 7, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 7, 2, 3, 2, 2].length) (baseStart_3835219 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3835219 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3835219 prefixEnd_3835219 := by exact prefixLift 3835219
  have htrace : WordTrace (prefixWord ++ tailWord_3835219) baseStart_3835219 baseEnd_3835219 := by
    simpa [prefixWord, tailWord_3835219, baseEnd_3835219] using wordTrace_append hprefix tailTrace_3835219
  have hstable : (prefixWord ++ tailWord_3835219).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3835219).length < 2 ^ (prefixWord ++ tailWord_3835219).sum := by decide
  have hdescent : baseEnd_3835219 < baseStart_3835219 := by decide
  rcases family_descends (prefixWord ++ tailWord_3835219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3835232 : List Nat := [2, 1, 1, 3, 4, 1, 2, 2, 1, 2, 4]
def baseStart_3835232 : Nat := 118140960795 + 3835232 * 2 ^ 59
def prefixEnd_3835232 : Nat := 4983230072969 + 3 ^ 40 * 3835232 * 2
def baseEnd_3835232 : Nat := 1969317437504443870862095

theorem tailTrace_3835232 : CollatzResearch.WordTrace tailWord_3835232 prefixEnd_3835232 1969317437504443870862095 := by
  unfold tailWord_3835232
  simp only [CollatzResearch.WordTrace]
  refine ⟨69941201420808472161529975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93254935227744629548706633 69941201420808472161529975)
  ·
    refine ⟨104911802131212708242294963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69941201420808472161529975 104911802131212708242294963)
    ·
      refine ⟨157367703196819062363442445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104911802131212708242294963 157367703196819062363442445)
      ·
        refine ⟨59012888698807148386290917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 157367703196819062363442445 59012888698807148386290917)
        ·
          refine ⟨11064916631026340322429547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 59012888698807148386290917 11064916631026340322429547)
          ·
            refine ⟨16597374946539510483644321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11064916631026340322429547 16597374946539510483644321)
            ·
              refine ⟨12448031209904632862733241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16597374946539510483644321 12448031209904632862733241)
              ·
                refine ⟨9336023407428474647049931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12448031209904632862733241 9336023407428474647049931)
                ·
                  refine ⟨14004035111142711970574897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9336023407428474647049931 14004035111142711970574897)
                  ·
                    refine ⟨10503026333357033977931173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14004035111142711970574897 10503026333357033977931173)
                    ·
                      refine ⟨1969317437504443870862095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10503026333357033977931173 1969317437504443870862095)
                      ·
                        rfl

theorem cell23_3835232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 2, 2, 1, 2, 4].length) (baseStart_3835232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3835232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3835232 prefixEnd_3835232 := by exact prefixLift 3835232
  have htrace : WordTrace (prefixWord ++ tailWord_3835232) baseStart_3835232 baseEnd_3835232 := by
    simpa [prefixWord, tailWord_3835232, baseEnd_3835232] using wordTrace_append hprefix tailTrace_3835232
  have hstable : (prefixWord ++ tailWord_3835232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3835232).length < 2 ^ (prefixWord ++ tailWord_3835232).sum := by decide
  have hdescent : baseEnd_3835232 < baseStart_3835232 := by decide
  rcases family_descends (prefixWord ++ tailWord_3835232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3835236 : List Nat := [2, 3, 1, 1, 3, 4, 2, 1, 1, 1, 4]
def baseStart_3835236 : Nat := 118140960795 + 3835236 * 2 ^ 59
def prefixEnd_3835236 : Nat := 4983230072969 + 3 ^ 40 * 3835236 * 2
def baseEnd_3835236 : Nat := 1969319491427061855212077

theorem tailTrace_3835236 : CollatzResearch.WordTrace tailWord_3835236 prefixEnd_3835236 1969319491427061855212077 := by
  unfold tailWord_3835236
  simp only [CollatzResearch.WordTrace]
  refine ⟨69941274366801226503102781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93255032489068302004137041 69941274366801226503102781)
  ·
    refine ⟨26227977887550459938663543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69941274366801226503102781 26227977887550459938663543)
    ·
      refine ⟨39341966831325689907995315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26227977887550459938663543 39341966831325689907995315)
      ·
        refine ⟨59012950246988534861992973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39341966831325689907995315 59012950246988534861992973)
        ·
          refine ⟨22129856342620700573247365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59012950246988534861992973 22129856342620700573247365)
          ·
            refine ⟨4149348064241381357483881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22129856342620700573247365 4149348064241381357483881)
            ·
              refine ⟨3112011048181036018112911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4149348064241381357483881 3112011048181036018112911)
              ·
                refine ⟨4668016572271554027169367, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3112011048181036018112911 4668016572271554027169367)
                ·
                  refine ⟨7002024858407331040754051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4668016572271554027169367 7002024858407331040754051)
                  ·
                    refine ⟨10503037287610996561131077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7002024858407331040754051 10503037287610996561131077)
                    ·
                      refine ⟨1969319491427061855212077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10503037287610996561131077 1969319491427061855212077)
                      ·
                        rfl

theorem cell23_3835236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 4, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 4, 2, 1, 1, 1, 4].length) (baseStart_3835236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3835236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3835236 prefixEnd_3835236 := by exact prefixLift 3835236
  have htrace : WordTrace (prefixWord ++ tailWord_3835236) baseStart_3835236 baseEnd_3835236 := by
    simpa [prefixWord, tailWord_3835236, baseEnd_3835236] using wordTrace_append hprefix tailTrace_3835236
  have hstable : (prefixWord ++ tailWord_3835236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3835236).length < 2 ^ (prefixWord ++ tailWord_3835236).sum := by decide
  have hdescent : baseEnd_3835236 < baseStart_3835236 := by decide
  rcases family_descends (prefixWord ++ tailWord_3835236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3835242 : List Nat := [3, 1, 3, 3, 2, 1, 10]
def baseStart_3835242 : Nat := 118140960795 + 3835242 * 2 ^ 59
def prefixEnd_3835242 : Nat := 4983230072969 + 3 ^ 40 * 3835242 * 2
def baseEnd_3835242 : Nat := 24312624349518380638729

theorem tailTrace_3835242 : CollatzResearch.WordTrace tailWord_3835242 prefixEnd_3835242 24312624349518380638729 := by
  unfold tailWord_3835242
  simp only [CollatzResearch.WordTrace]
  refine ⟨34970691892895179007730995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93255178381053810687282653 34970691892895179007730995)
  ·
    refine ⟨52456037839342768511596493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34970691892895179007730995 52456037839342768511596493)
    ·
      refine ⟨19671014189753538191848685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52456037839342768511596493 19671014189753538191848685)
      ·
        refine ⟨7376630321157576821943257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19671014189753538191848685 7376630321157576821943257)
        ·
          refine ⟨5532472740868182616457443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7376630321157576821943257 5532472740868182616457443)
          ·
            refine ⟨8298709111302273924686165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5532472740868182616457443 8298709111302273924686165)
            ·
              refine ⟨24312624349518380638729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 8298709111302273924686165 24312624349518380638729)
              ·
                rfl

theorem cell23_3835242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 1, 10].length) (baseStart_3835242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3835242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3835242 prefixEnd_3835242 := by exact prefixLift 3835242
  have htrace : WordTrace (prefixWord ++ tailWord_3835242) baseStart_3835242 baseEnd_3835242 := by
    simpa [prefixWord, tailWord_3835242, baseEnd_3835242] using wordTrace_append hprefix tailTrace_3835242
  have hstable : (prefixWord ++ tailWord_3835242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3835242).length < 2 ^ (prefixWord ++ tailWord_3835242).sum := by decide
  have hdescent : baseEnd_3835242 < baseStart_3835242 := by decide
  rcases family_descends (prefixWord ++ tailWord_3835242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3835246 : List Nat := [4, 1, 2, 4, 1, 1, 1, 1, 4, 4]
def baseStart_3835246 : Nat := 118140960795 + 3835246 * 2 ^ 59
def prefixEnd_3835246 : Nat := 4983230072969 + 3 ^ 40 * 3835246 * 2
def baseEnd_3835246 : Nat := 656441542077868938695677

theorem tailTrace_3835246 : CollatzResearch.WordTrace tailWord_3835246 prefixEnd_3835246 656441542077868938695677 := by
  unfold tailWord_3835246
  simp only [CollatzResearch.WordTrace]
  refine ⟨17485364182945778089258699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 93255275642377483142713061 17485364182945778089258699)
  ·
    refine ⟨26228046274418667133888049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17485364182945778089258699 26228046274418667133888049)
    ·
      refine ⟨19671034705814000350416037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26228046274418667133888049 19671034705814000350416037)
      ·
        refine ⟨3688319007340125065703007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19671034705814000350416037 3688319007340125065703007)
        ·
          refine ⟨5532478511010187598554511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3688319007340125065703007 5532478511010187598554511)
          ·
            refine ⟨8298717766515281397831767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5532478511010187598554511 8298717766515281397831767)
            ·
              refine ⟨12448076649772922096747651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8298717766515281397831767 12448076649772922096747651)
              ·
                refine ⟨18672114974659383145121477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12448076649772922096747651 18672114974659383145121477)
                ·
                  refine ⟨3501021557748634339710277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18672114974659383145121477 3501021557748634339710277)
                  ·
                    refine ⟨656441542077868938695677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3501021557748634339710277 656441542077868938695677)
                    ·
                      rfl

theorem cell23_3835246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 1, 1, 1, 4, 4].length) (baseStart_3835246 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3835246 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3835246 prefixEnd_3835246 := by exact prefixLift 3835246
  have htrace : WordTrace (prefixWord ++ tailWord_3835246) baseStart_3835246 baseEnd_3835246 := by
    simpa [prefixWord, tailWord_3835246, baseEnd_3835246] using wordTrace_append hprefix tailTrace_3835246
  have hstable : (prefixWord ++ tailWord_3835246).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3835246).length < 2 ^ (prefixWord ++ tailWord_3835246).sum := by decide
  have hdescent : baseEnd_3835246 < baseStart_3835246 := by decide
  rcases family_descends (prefixWord ++ tailWord_3835246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3835253 : List Nat := [1, 3, 4, 1, 3, 1, 2, 1, 3, 2, 2]
def baseStart_3835253 : Nat := 118140960795 + 3835253 * 2 ^ 59
def prefixEnd_3835253 : Nat := 4983230072969 + 3 ^ 40 * 3835253 * 2
def baseEnd_3835253 : Nat := 1969328220598188288699499

theorem tailTrace_3835253 : CollatzResearch.WordTrace tailWord_3835253 prefixEnd_3835253 1969328220598188288699499 := by
  unfold tailWord_3835253
  simp only [CollatzResearch.WordTrace]
  refine ⟨139883168774540864909574413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93255445849693909939716275 139883168774540864909574413)
  ·
    refine ⟨52456188290452824341090405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 139883168774540864909574413 52456188290452824341090405)
    ·
      refine ⟨9835535304459904563954451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 52456188290452824341090405 9835535304459904563954451)
      ·
        refine ⟨14753302956689856845931677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9835535304459904563954451 14753302956689856845931677)
        ·
          refine ⟨5532488608758696317224379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14753302956689856845931677 5532488608758696317224379)
          ·
            refine ⟨8298732913138044475836569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5532488608758696317224379 8298732913138044475836569)
            ·
              refine ⟨6224049684853533356877427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8298732913138044475836569 6224049684853533356877427)
              ·
                refine ⟨9336074527280300035316141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6224049684853533356877427 9336074527280300035316141)
                ·
                  refine ⟨3501027947730112513243553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9336074527280300035316141 3501027947730112513243553)
                  ·
                    refine ⟨2625770960797584384932665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3501027947730112513243553 2625770960797584384932665)
                    ·
                      refine ⟨1969328220598188288699499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2625770960797584384932665 1969328220598188288699499)
                      ·
                        rfl

theorem cell23_3835253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 1, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 1, 2, 1, 3, 2, 2].length) (baseStart_3835253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3835253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3835253 prefixEnd_3835253 := by exact prefixLift 3835253
  have htrace : WordTrace (prefixWord ++ tailWord_3835253) baseStart_3835253 baseEnd_3835253 := by
    simpa [prefixWord, tailWord_3835253, baseEnd_3835253] using wordTrace_append hprefix tailTrace_3835253
  have hstable : (prefixWord ++ tailWord_3835253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3835253).length < 2 ^ (prefixWord ++ tailWord_3835253).sum := by decide
  have hdescent : baseEnd_3835253 < baseStart_3835253 := by decide
  rcases family_descends (prefixWord ++ tailWord_3835253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3835266 : List Nat := [3, 4, 2, 1, 1, 1, 3, 1, 1, 2, 4]
def baseStart_3835266 : Nat := 118140960795 + 3835266 * 2 ^ 59
def prefixEnd_3835266 : Nat := 4983230072969 + 3 ^ 40 * 3835266 * 2
def baseEnd_3835266 : Nat := 1969334895846696737836939

theorem tailTrace_3835266 : CollatzResearch.WordTrace tailWord_3835266 prefixEnd_3835266 1969334895846696737836939 := by
  unfold tailWord_3835266
  simp only [CollatzResearch.WordTrace]
  refine ⟨34970910730873442032449413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93255761948995845419865101 34970910730873442032449413)
  ·
    refine ⟨6557045762038770381084265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 34970910730873442032449413 6557045762038770381084265)
    ·
      refine ⟨4917784321529077785813199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6557045762038770381084265 4917784321529077785813199)
      ·
        refine ⟨7376676482293616678719799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4917784321529077785813199 7376676482293616678719799)
        ·
          refine ⟨11065014723440425018079699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7376676482293616678719799 11065014723440425018079699)
          ·
            refine ⟨16597522085160637527119549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11065014723440425018079699 16597522085160637527119549)
            ·
              refine ⟨6224070781935239072669831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16597522085160637527119549 6224070781935239072669831)
              ·
                refine ⟨9336106172902858609004747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6224070781935239072669831 9336106172902858609004747)
                ·
                  refine ⟨14004159259354287913507121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9336106172902858609004747 14004159259354287913507121)
                  ·
                    refine ⟨10503119444515715935130341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14004159259354287913507121 10503119444515715935130341)
                    ·
                      refine ⟨1969334895846696737836939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10503119444515715935130341 1969334895846696737836939)
                      ·
                        rfl

theorem cell23_3835266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 3, 1, 1, 2, 4].length) (baseStart_3835266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3835266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3835266 prefixEnd_3835266 := by exact prefixLift 3835266
  have htrace : WordTrace (prefixWord ++ tailWord_3835266) baseStart_3835266 baseEnd_3835266 := by
    simpa [prefixWord, tailWord_3835266, baseEnd_3835266] using wordTrace_append hprefix tailTrace_3835266
  have hstable : (prefixWord ++ tailWord_3835266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3835266).length < 2 ^ (prefixWord ++ tailWord_3835266).sum := by decide
  have hdescent : baseEnd_3835266 < baseStart_3835266 := by decide
  rcases family_descends (prefixWord ++ tailWord_3835266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3835269 : List Nat := [1, 3, 1, 1, 3, 1, 2, 5, 2, 1, 3]
def baseStart_3835269 : Nat := 118140960795 + 3835269 * 2 ^ 59
def prefixEnd_3835269 : Nat := 4983230072969 + 3 ^ 40 * 3835269 * 2
def baseEnd_3835269 : Nat := 1969336436288660226099425

theorem tailTrace_3835269 : CollatzResearch.WordTrace tailWord_3835269 prefixEnd_3835269 1969336436288660226099425 := by
  unfold tailWord_3835269
  simp only [CollatzResearch.WordTrace]
  refine ⟨139883752342482899642156861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93255834894988599761437907 139883752342482899642156861)
  ·
    refine ⟨52456407128431087365808823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 139883752342482899642156861 52456407128431087365808823)
    ·
      refine ⟨78684610692646631048713235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52456407128431087365808823 78684610692646631048713235)
      ·
        refine ⟨118026916038969946573069853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78684610692646631048713235 118026916038969946573069853)
        ·
          refine ⟨44260093514613729964901195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 118026916038969946573069853 44260093514613729964901195)
          ·
            refine ⟨66390140271920594947351793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44260093514613729964901195 66390140271920594947351793)
            ·
              refine ⟨49792605203940446210513845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66390140271920594947351793 49792605203940446210513845)
              ·
                refine ⟨4668056737869416832235673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 49792605203940446210513845 4668056737869416832235673)
                ·
                  refine ⟨3501042553402062624176755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4668056737869416832235673 3501042553402062624176755)
                  ·
                    refine ⟨5251563830103093936265133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3501042553402062624176755 5251563830103093936265133)
                    ·
                      refine ⟨1969336436288660226099425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5251563830103093936265133 1969336436288660226099425)
                      ·
                        rfl

theorem cell23_3835269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 2, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 2, 5, 2, 1, 3].length) (baseStart_3835269 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3835269 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3835269 prefixEnd_3835269 := by exact prefixLift 3835269
  have htrace : WordTrace (prefixWord ++ tailWord_3835269) baseStart_3835269 baseEnd_3835269 := by
    simpa [prefixWord, tailWord_3835269, baseEnd_3835269] using wordTrace_append hprefix tailTrace_3835269
  have hstable : (prefixWord ++ tailWord_3835269).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3835269).length < 2 ^ (prefixWord ++ tailWord_3835269).sum := by decide
  have hdescent : baseEnd_3835269 < baseStart_3835269 := by decide
  rcases family_descends (prefixWord ++ tailWord_3835269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3835285 : List Nat := [1, 3, 2, 1, 1, 2, 2, 2, 1, 8]
def baseStart_3835285 : Nat := 118140960795 + 3835285 * 2 ^ 59
def prefixEnd_3835285 : Nat := 4983230072969 + 3 ^ 40 * 3835285 * 2
def baseEnd_3835285 : Nat := 656448217326377387833117

theorem tailTrace_3835285 : CollatzResearch.WordTrace tailWord_3835285 prefixEnd_3835285 656448217326377387833117 := by
  unfold tailWord_3835285
  simp only [CollatzResearch.WordTrace]
  refine ⟨139884335910424934374739309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93256223940283289583159539 139884335910424934374739309)
  ·
    refine ⟨52456625966409350390527241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 139884335910424934374739309 52456625966409350390527241)
    ·
      refine ⟨39342469474807012792895431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52456625966409350390527241 39342469474807012792895431)
      ·
        refine ⟨59013704212210519189343147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39342469474807012792895431 59013704212210519189343147)
        ·
          refine ⟨88520556318315778784014721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59013704212210519189343147 88520556318315778784014721)
          ·
            refine ⟨66390417238736834088011041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 88520556318315778784014721 66390417238736834088011041)
            ·
              refine ⟨49792812929052625566008281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66390417238736834088011041 49792812929052625566008281)
              ·
                refine ⟨37344609696789469174506211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49792812929052625566008281 37344609696789469174506211)
                ·
                  refine ⟨56016914545184203761759317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37344609696789469174506211 56016914545184203761759317)
                  ·
                    refine ⟨656448217326377387833117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 56016914545184203761759317 656448217326377387833117)
                    ·
                      rfl

theorem cell23_3835285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 2, 2, 1, 8].length) (baseStart_3835285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3835285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3835285 prefixEnd_3835285 := by exact prefixLift 3835285
  have htrace : WordTrace (prefixWord ++ tailWord_3835285) baseStart_3835285 baseEnd_3835285 := by
    simpa [prefixWord, tailWord_3835285, baseEnd_3835285] using wordTrace_append hprefix tailTrace_3835285
  have hstable : (prefixWord ++ tailWord_3835285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3835285).length < 2 ^ (prefixWord ++ tailWord_3835285).sum := by decide
  have hdescent : baseEnd_3835285 < baseStart_3835285 := by decide
  rcases family_descends (prefixWord ++ tailWord_3835285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3835349 : List Nat := [1, 3, 2, 3, 1, 1, 2, 5, 5]
def baseStart_3835349 : Nat := 118140960795 + 3835349 * 2 ^ 59
def prefixEnd_3835349 : Nat := 4983230072969 + 3 ^ 40 * 3835349 * 2
def baseEnd_3835349 : Nat := 218819723860113323677673

theorem tailTrace_3835349 : CollatzResearch.WordTrace tailWord_3835349 prefixEnd_3835349 218819723860113323677673 := by
  unfold tailWord_3835349
  simp only [CollatzResearch.WordTrace]
  refine ⟨139886670182193073305069101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93257780121462048870046067 139886670182193073305069101)
  ·
    refine ⟨52457501318322402489400913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 139886670182193073305069101 52457501318322402489400913)
    ·
      refine ⟨39343125988741801867050685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52457501318322402489400913 39343125988741801867050685)
      ·
        refine ⟨14753672245778175700144007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39343125988741801867050685 14753672245778175700144007)
        ·
          refine ⟨22130508368667263550216011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14753672245778175700144007 22130508368667263550216011)
          ·
            refine ⟨33195762553000895325324017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22130508368667263550216011 33195762553000895325324017)
            ·
              refine ⟨24896821914750671493993013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33195762553000895325324017 24896821914750671493993013)
              ·
                refine ⟨2334077054507875452561845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 24896821914750671493993013 2334077054507875452561845)
                ·
                  refine ⟨218819723860113323677673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2334077054507875452561845 218819723860113323677673)
                  ·
                    rfl

theorem cell23_3835349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 2, 5, 5].length) (baseStart_3835349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3835349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3835349 prefixEnd_3835349 := by exact prefixLift 3835349
  have htrace : WordTrace (prefixWord ++ tailWord_3835349) baseStart_3835349 baseEnd_3835349 := by
    simpa [prefixWord, tailWord_3835349, baseEnd_3835349] using wordTrace_append hprefix tailTrace_3835349
  have hstable : (prefixWord ++ tailWord_3835349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3835349).length < 2 ^ (prefixWord ++ tailWord_3835349).sum := by decide
  have hdescent : baseEnd_3835349 < baseStart_3835349 := by decide
  rcases family_descends (prefixWord ++ tailWord_3835349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3835399 : List Nat := [1, 1, 4, 3, 2, 2, 1, 1, 1, 3, 4]
def baseStart_3835399 : Nat := 118140960795 + 3835399 * 2 ^ 59
def prefixEnd_3835399 : Nat := 4983230072969 + 3 ^ 40 * 3835399 * 2
def baseEnd_3835399 : Nat := 1969403188773744717473827

theorem tailTrace_3835399 : CollatzResearch.WordTrace tailWord_3835399 prefixEnd_3835399 1969403188773744717473827 := by
  unfold tailWord_3835399
  simp only [CollatzResearch.WordTrace]
  refine ⟨139888493832011931844389251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93258995888007954562926167 139888493832011931844389251)
  ·
    refine ⟨209832740748017897766583877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139888493832011931844389251 209832740748017897766583877)
    ·
      refine ⟨39343638890253355831234477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 209832740748017897766583877 39343638890253355831234477)
      ·
        refine ⟨14753864583845008436712929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39343638890253355831234477 14753864583845008436712929)
        ·
          refine ⟨11065398437883756327534697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14753864583845008436712929 11065398437883756327534697)
          ·
            refine ⟨8299048828412817245651023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11065398437883756327534697 8299048828412817245651023)
            ·
              refine ⟨12448573242619225868476535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8299048828412817245651023 12448573242619225868476535)
              ·
                refine ⟨18672859863928838802714803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12448573242619225868476535 18672859863928838802714803)
                ·
                  refine ⟨28009289795893258204072205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18672859863928838802714803 28009289795893258204072205)
                  ·
                    refine ⟨10503483673459971826527077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28009289795893258204072205 10503483673459971826527077)
                    ·
                      refine ⟨1969403188773744717473827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10503483673459971826527077 1969403188773744717473827)
                      ·
                        rfl

theorem cell23_3835399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 2, 1, 1, 1, 3, 4].length) (baseStart_3835399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3835399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3835399 prefixEnd_3835399 := by exact prefixLift 3835399
  have htrace : WordTrace (prefixWord ++ tailWord_3835399) baseStart_3835399 baseEnd_3835399 := by
    simpa [prefixWord, tailWord_3835399, baseEnd_3835399] using wordTrace_append hprefix tailTrace_3835399
  have hstable : (prefixWord ++ tailWord_3835399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3835399).length < 2 ^ (prefixWord ++ tailWord_3835399).sum := by decide
  have hdescent : baseEnd_3835399 < baseStart_3835399 := by decide
  rcases family_descends (prefixWord ++ tailWord_3835399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3835442 : List Nat := [3, 2, 1, 1, 2, 1, 1, 1, 3, 2, 6]
def baseStart_3835442 : Nat := 118140960795 + 3835442 * 2 ^ 59
def prefixEnd_3835442 : Nat := 4983230072969 + 3 ^ 40 * 3835442 * 2
def baseEnd_3835442 : Nat := 1969425268441888049236129

theorem tailTrace_3835442 : CollatzResearch.WordTrace tailWord_3835442 prefixEnd_3835442 1969425268441888049236129 := by
  unfold tailWord_3835442
  simp only [CollatzResearch.WordTrace]
  refine ⟨34972515542714037547051145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93260041447237433458803053 34972515542714037547051145)
  ·
    refine ⟨26229386657035528160288359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34972515542714037547051145 26229386657035528160288359)
    ·
      refine ⟨39344079985553292240432539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26229386657035528160288359 39344079985553292240432539)
      ·
        refine ⟨59016119978329938360648809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39344079985553292240432539 59016119978329938360648809)
        ·
          refine ⟨44262089983747453770486607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59016119978329938360648809 44262089983747453770486607)
          ·
            refine ⟨66393134975621180655729911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44262089983747453770486607 66393134975621180655729911)
            ·
              refine ⟨99589702463431770983594867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66393134975621180655729911 99589702463431770983594867)
              ·
                refine ⟨149384553695147656475392301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 99589702463431770983594867 149384553695147656475392301)
                ·
                  refine ⟨56019207635680371178272113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 149384553695147656475392301 56019207635680371178272113)
                  ·
                    refine ⟨42014405726760278383704085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 56019207635680371178272113 42014405726760278383704085)
                    ·
                      refine ⟨1969425268441888049236129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 42014405726760278383704085 1969425268441888049236129)
                      ·
                        rfl

theorem cell23_3835442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 1, 3, 2, 6].length) (baseStart_3835442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3835442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3835442 prefixEnd_3835442 := by exact prefixLift 3835442
  have htrace : WordTrace (prefixWord ++ tailWord_3835442) baseStart_3835442 baseEnd_3835442 := by
    simpa [prefixWord, tailWord_3835442, baseEnd_3835442] using wordTrace_append hprefix tailTrace_3835442
  have hstable : (prefixWord ++ tailWord_3835442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3835442).length < 2 ^ (prefixWord ++ tailWord_3835442).sum := by decide
  have hdescent : baseEnd_3835442 < baseStart_3835442 := by decide
  rcases family_descends (prefixWord ++ tailWord_3835442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3835489 : List Nat := [1, 2, 3, 1, 1, 3, 2, 2, 3, 1, 4]
def baseStart_3835489 : Nat := 118140960795 + 3835489 * 2 ^ 59
def prefixEnd_3835489 : Nat := 4983230072969 + 3 ^ 40 * 3835489 * 2
def baseEnd_3835489 : Nat := 1969449402032649365348413

theorem tailTrace_3835489 : CollatzResearch.WordTrace tailWord_3835489 prefixEnd_3835489 1969449402032649365348413 := by
  unfold tailWord_3835489
  simp only [CollatzResearch.WordTrace]
  refine ⟨139891776401685877215165521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93261184267790584810110347 139891776401685877215165521)
  ·
    refine ⟨104918832301264407911374141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139891776401685877215165521 104918832301264407911374141)
    ·
      refine ⟨39344562112974152966765303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 104918832301264407911374141 39344562112974152966765303)
      ·
        refine ⟨59016843169461229450147955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39344562112974152966765303 59016843169461229450147955)
        ·
          refine ⟨88525264754191844175221933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59016843169461229450147955 88525264754191844175221933)
          ·
            refine ⟨33196974282821941565708225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 88525264754191844175221933 33196974282821941565708225)
            ·
              refine ⟨24897730712116456174281169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33196974282821941565708225 24897730712116456174281169)
              ·
                refine ⟨18673298034087342130710877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24897730712116456174281169 18673298034087342130710877)
                ·
                  refine ⟨7002486762782753299016579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18673298034087342130710877 7002486762782753299016579)
                  ·
                    refine ⟨10503730144174129948524869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7002486762782753299016579 10503730144174129948524869)
                    ·
                      refine ⟨1969449402032649365348413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10503730144174129948524869 1969449402032649365348413)
                      ·
                        rfl

theorem cell23_3835489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 2, 2, 3, 1, 4].length) (baseStart_3835489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3835489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3835489 prefixEnd_3835489 := by exact prefixLift 3835489
  have htrace : WordTrace (prefixWord ++ tailWord_3835489) baseStart_3835489 baseEnd_3835489 := by
    simpa [prefixWord, tailWord_3835489, baseEnd_3835489] using wordTrace_append hprefix tailTrace_3835489
  have hstable : (prefixWord ++ tailWord_3835489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3835489).length < 2 ^ (prefixWord ++ tailWord_3835489).sum := by decide
  have hdescent : baseEnd_3835489 < baseStart_3835489 := by decide
  rcases family_descends (prefixWord ++ tailWord_3835489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3835506 : List Nat := [3, 2, 1, 2, 3, 2, 1, 1, 3, 1, 4]
def baseStart_3835506 : Nat := 118140960795 + 3835506 * 2 ^ 59
def prefixEnd_3835506 : Nat := 4983230072969 + 3 ^ 40 * 3835506 * 2
def baseEnd_3835506 : Nat := 1969458131203775798835835

theorem tailTrace_3835506 : CollatzResearch.WordTrace tailWord_3835506 prefixEnd_3835506 1969458131203775798835835 := by
  unfold tailWord_3835506
  simp only [CollatzResearch.WordTrace]
  refine ⟨34973099110656072279633593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93261597628416192745689581 34973099110656072279633593)
  ·
    refine ⟨26229824332992054209725195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34973099110656072279633593 26229824332992054209725195)
    ·
      refine ⟨39344736499488081314587793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26229824332992054209725195 39344736499488081314587793)
      ·
        refine ⟨29508552374616060985940845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39344736499488081314587793 29508552374616060985940845)
        ·
          refine ⟨11065707140481022869727817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29508552374616060985940845 11065707140481022869727817)
          ·
            refine ⟨8299280355360767152295863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11065707140481022869727817 8299280355360767152295863)
            ·
              refine ⟨12448920533041150728443795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8299280355360767152295863 12448920533041150728443795)
              ·
                refine ⟨18673380799561726092665693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12448920533041150728443795 18673380799561726092665693)
                ·
                  refine ⟨7002517799835647284749635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18673380799561726092665693 7002517799835647284749635)
                  ·
                    refine ⟨10503776699753470927124453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7002517799835647284749635 10503776699753470927124453)
                    ·
                      refine ⟨1969458131203775798835835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10503776699753470927124453 1969458131203775798835835)
                      ·
                        rfl

theorem cell23_3835506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 2, 1, 1, 3, 1, 4].length) (baseStart_3835506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3835506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3835506 prefixEnd_3835506 := by exact prefixLift 3835506
  have htrace : WordTrace (prefixWord ++ tailWord_3835506) baseStart_3835506 baseEnd_3835506 := by
    simpa [prefixWord, tailWord_3835506, baseEnd_3835506] using wordTrace_append hprefix tailTrace_3835506
  have hstable : (prefixWord ++ tailWord_3835506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3835506).length < 2 ^ (prefixWord ++ tailWord_3835506).sum := by decide
  have hdescent : baseEnd_3835506 < baseStart_3835506 := by decide
  rcases family_descends (prefixWord ++ tailWord_3835506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3835510 : List Nat := [5, 1, 1, 2, 2, 2, 2, 1, 2, 3, 2]
def baseStart_3835510 : Nat := 118140960795 + 3835510 * 2 ^ 59
def prefixEnd_3835510 : Nat := 4983230072969 + 3 ^ 40 * 3835510 * 2
def baseEnd_3835510 : Nat := 1969460185126393783185817

theorem tailTrace_3835510 : CollatzResearch.WordTrace tailWord_3835510 prefixEnd_3835510 1969460185126393783185817 := by
  unfold tailWord_3835510
  simp only [CollatzResearch.WordTrace]
  refine ⟨8743283895913112362604999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 93261694889739865201119989 8743283895913112362604999)
  ·
    refine ⟨13114925843869668543907499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8743283895913112362604999 13114925843869668543907499)
    ·
      refine ⟨19672388765804502815861249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13114925843869668543907499 19672388765804502815861249)
      ·
        refine ⟨14754291574353377111895937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19672388765804502815861249 14754291574353377111895937)
        ·
          refine ⟨11065718680765032833921953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14754291574353377111895937 11065718680765032833921953)
          ·
            refine ⟨8299289010573774625441465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11065718680765032833921953 8299289010573774625441465)
            ·
              refine ⟨6224466757930330969081099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8299289010573774625441465 6224466757930330969081099)
              ·
                refine ⟨9336700136895496453621649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6224466757930330969081099 9336700136895496453621649)
                ·
                  refine ⟨7002525102671622340216237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9336700136895496453621649 7002525102671622340216237)
                  ·
                    refine ⟨2625946913501858377581089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7002525102671622340216237 2625946913501858377581089)
                    ·
                      refine ⟨1969460185126393783185817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2625946913501858377581089 1969460185126393783185817)
                      ·
                        rfl

theorem cell23_3835510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 2, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 2, 2, 1, 2, 3, 2].length) (baseStart_3835510 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3835510 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3835510 prefixEnd_3835510 := by exact prefixLift 3835510
  have htrace : WordTrace (prefixWord ++ tailWord_3835510) baseStart_3835510 baseEnd_3835510 := by
    simpa [prefixWord, tailWord_3835510, baseEnd_3835510] using wordTrace_append hprefix tailTrace_3835510
  have hstable : (prefixWord ++ tailWord_3835510).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3835510).length < 2 ^ (prefixWord ++ tailWord_3835510).sum := by decide
  have hdescent : baseEnd_3835510 < baseStart_3835510 := by decide
  rcases family_descends (prefixWord ++ tailWord_3835510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3835556 : List Nat := [2, 3, 1, 2, 2, 2, 1, 3, 1, 3, 3]
def baseStart_3835556 : Nat := 118140960795 + 3835556 * 2 ^ 59
def prefixEnd_3835556 : Nat := 4983230072969 + 3 ^ 40 * 3835556 * 2
def baseEnd_3835556 : Nat := 1969483805236500603210605

theorem tailTrace_3835556 : CollatzResearch.WordTrace tailWord_3835556 prefixEnd_3835556 1969483805236500603210605 := by
  unfold tailWord_3835556
  simp only [CollatzResearch.WordTrace]
  refine ⟨69947110046221573828927261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93262813394962098438569681 69947110046221573828927261)
  ·
    refine ⟨26230166267333090185847723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69947110046221573828927261 26230166267333090185847723)
    ·
      refine ⟨39345249400999635278771585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26230166267333090185847723 39345249400999635278771585)
      ·
        refine ⟨29508937050749726459078689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39345249400999635278771585 29508937050749726459078689)
        ·
          refine ⟨22131702788062294844309017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29508937050749726459078689 22131702788062294844309017)
          ·
            refine ⟨16598777091046721133231763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22131702788062294844309017 16598777091046721133231763)
            ·
              refine ⟨24898165636570081699847645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16598777091046721133231763 24898165636570081699847645)
              ·
                refine ⟨9336812113713780637442867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24898165636570081699847645 9336812113713780637442867)
                ·
                  refine ⟨14005218170570670956164301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9336812113713780637442867 14005218170570670956164301)
                  ·
                    refine ⟨5251956813964001608561613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14005218170570670956164301 5251956813964001608561613)
                    ·
                      refine ⟨1969483805236500603210605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5251956813964001608561613 1969483805236500603210605)
                      ·
                        rfl

theorem cell23_3835556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 1, 3, 1, 3, 3].length) (baseStart_3835556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3835556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3835556 prefixEnd_3835556 := by exact prefixLift 3835556
  have htrace : WordTrace (prefixWord ++ tailWord_3835556) baseStart_3835556 baseEnd_3835556 := by
    simpa [prefixWord, tailWord_3835556, baseEnd_3835556] using wordTrace_append hprefix tailTrace_3835556
  have hstable : (prefixWord ++ tailWord_3835556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3835556).length < 2 ^ (prefixWord ++ tailWord_3835556).sum := by decide
  have hdescent : baseEnd_3835556 < baseStart_3835556 := by decide
  rcases family_descends (prefixWord ++ tailWord_3835556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3835574 : List Nat := [5, 1, 3, 1, 1, 1, 1, 5, 1, 2, 2]
def baseStart_3835574 : Nat := 118140960795 + 3835574 * 2 ^ 59
def prefixEnd_3835574 : Nat := 4983230072969 + 3 ^ 40 * 3835574 * 2
def baseEnd_3835574 : Nat := 1969493047888281532785523

theorem tailTrace_3835574 : CollatzResearch.WordTrace tailWord_3835574 prefixEnd_3835574 1969493047888281532785523 := by
  unfold tailWord_3835574
  simp only [CollatzResearch.WordTrace]
  refine ⟨8743429787898621045750611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 93263251070918624488006517 8743429787898621045750611)
  ·
    refine ⟨13115144681847931568625917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8743429787898621045750611 13115144681847931568625917)
    ·
      refine ⟨4918179255692974338234719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13115144681847931568625917 4918179255692974338234719)
      ·
        refine ⟨7377268883539461507352079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4918179255692974338234719 7377268883539461507352079)
        ·
          refine ⟨11065903325309192261028119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7377268883539461507352079 11065903325309192261028119)
          ·
            refine ⟨16598854987963788391542179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11065903325309192261028119 16598854987963788391542179)
            ·
              refine ⟨24898282481945682587313269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16598854987963788391542179 24898282481945682587313269)
              ·
                refine ⟨2334213982682407742560619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 24898282481945682587313269 2334213982682407742560619)
                ·
                  refine ⟨3501320974023611613840929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2334213982682407742560619 3501320974023611613840929)
                  ·
                    refine ⟨2625990730517708710380697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3501320974023611613840929 2625990730517708710380697)
                    ·
                      refine ⟨1969493047888281532785523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2625990730517708710380697 1969493047888281532785523)
                      ·
                        rfl

theorem cell23_3835574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 1, 5, 1, 2, 2].length) (baseStart_3835574 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3835574 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3835574 prefixEnd_3835574 := by exact prefixLift 3835574
  have htrace : WordTrace (prefixWord ++ tailWord_3835574) baseStart_3835574 baseEnd_3835574 := by
    simpa [prefixWord, tailWord_3835574, baseEnd_3835574] using wordTrace_append hprefix tailTrace_3835574
  have hstable : (prefixWord ++ tailWord_3835574).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3835574).length < 2 ^ (prefixWord ++ tailWord_3835574).sum := by decide
  have hdescent : baseEnd_3835574 < baseStart_3835574 := by decide
  rcases family_descends (prefixWord ++ tailWord_3835574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3835583 : List Nat := [1, 1, 2, 2, 2, 3, 3, 3, 1, 3, 2]
def baseStart_3835583 : Nat := 118140960795 + 3835583 * 2 ^ 59
def prefixEnd_3835583 : Nat := 4983230072969 + 3 ^ 40 * 3835583 * 2
def baseEnd_3835583 : Nat := 1969497669214171997572981

theorem tailTrace_3835583 : CollatzResearch.WordTrace tailWord_3835583 prefixEnd_3835583 1969497669214171997572981 := by
  unfold tailWord_3835583
  simp only [CollatzResearch.WordTrace]
  refine ⟨139895204863345331269087403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93263469908896887512724935 139895204863345331269087403)
  ·
    refine ⟨209842807295017996903631105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139895204863345331269087403 209842807295017996903631105)
    ·
      refine ⟨157382105471263497677723329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 209842807295017996903631105 157382105471263497677723329)
      ·
        refine ⟨118036579103447623258292497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 157382105471263497677723329 118036579103447623258292497)
        ·
          refine ⟨88527434327585717443719373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 118036579103447623258292497 88527434327585717443719373)
          ·
            refine ⟨33197787872844644041394765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 88527434327585717443719373 33197787872844644041394765)
            ·
              refine ⟨12449170452316741515523037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33197787872844644041394765 12449170452316741515523037)
              ·
                refine ⟨4668438919618778068321139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12449170452316741515523037 4668438919618778068321139)
                ·
                  refine ⟨7002658379428167102481709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4668438919618778068321139 7002658379428167102481709)
                  ·
                    refine ⟨2625996892285562663430641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7002658379428167102481709 2625996892285562663430641)
                    ·
                      refine ⟨1969497669214171997572981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2625996892285562663430641 1969497669214171997572981)
                      ·
                        rfl

theorem cell23_3835583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 3, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 3, 3, 1, 3, 2].length) (baseStart_3835583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3835583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3835583 prefixEnd_3835583 := by exact prefixLift 3835583
  have htrace : WordTrace (prefixWord ++ tailWord_3835583) baseStart_3835583 baseEnd_3835583 := by
    simpa [prefixWord, tailWord_3835583, baseEnd_3835583] using wordTrace_append hprefix tailTrace_3835583
  have hstable : (prefixWord ++ tailWord_3835583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3835583).length < 2 ^ (prefixWord ++ tailWord_3835583).sum := by decide
  have hdescent : baseEnd_3835583 < baseStart_3835583 := by decide
  rcases family_descends (prefixWord ++ tailWord_3835583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3835599 : List Nat := [1, 1, 2, 1, 1, 3, 1, 3, 1, 6, 3]
def baseStart_3835599 : Nat := 118140960795 + 3835599 * 2 ^ 59
def prefixEnd_3835599 : Nat := 4983230072969 + 3 ^ 40 * 3835599 * 2
def baseEnd_3835599 : Nat := 1969505884904643934972907

theorem tailTrace_3835599 : CollatzResearch.WordTrace tailWord_3835599 prefixEnd_3835599 1969505884904643934972907 := by
  unfold tailWord_3835599
  simp only [CollatzResearch.WordTrace]
  refine ⟨139895788431287366001669851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93263858954191577334446567 139895788431287366001669851)
  ·
    refine ⟨209843682646931049002504777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139895788431287366001669851 209843682646931049002504777)
    ·
      refine ⟨157382761985198286751878583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 209843682646931049002504777 157382761985198286751878583)
      ·
        refine ⟨236074142977797430127817875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157382761985198286751878583 236074142977797430127817875)
        ·
          refine ⟨354111214466696145191726813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 236074142977797430127817875 354111214466696145191726813)
          ·
            refine ⟨132791705425011054446897555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 354111214466696145191726813 132791705425011054446897555)
            ·
              refine ⟨199187558137516581670346333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 132791705425011054446897555 199187558137516581670346333)
              ·
                refine ⟨74695334301568718126379875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 199187558137516581670346333 74695334301568718126379875)
                ·
                  refine ⟨112043001452353077189569813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 74695334301568718126379875 112043001452353077189569813)
                  ·
                    refine ⟨5252015693079050493261085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 112043001452353077189569813 5252015693079050493261085)
                    ·
                      refine ⟨1969505884904643934972907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5252015693079050493261085 1969505884904643934972907)
                      ·
                        rfl

theorem cell23_3835599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 3, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 3, 1, 6, 3].length) (baseStart_3835599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3835599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3835599 prefixEnd_3835599 := by exact prefixLift 3835599
  have htrace : WordTrace (prefixWord ++ tailWord_3835599) baseStart_3835599 baseEnd_3835599 := by
    simpa [prefixWord, tailWord_3835599, baseEnd_3835599] using wordTrace_append hprefix tailTrace_3835599
  have hstable : (prefixWord ++ tailWord_3835599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3835599).length < 2 ^ (prefixWord ++ tailWord_3835599).sum := by decide
  have hdescent : baseEnd_3835599 < baseStart_3835599 := by decide
  rcases family_descends (prefixWord ++ tailWord_3835599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3835659 : List Nat := [1, 1, 1, 1, 5, 1, 3, 1, 1, 1, 7]
def baseStart_3835659 : Nat := 118140960795 + 3835659 * 2 ^ 59
def prefixEnd_3835659 : Nat := 4983230072969 + 3 ^ 40 * 3835659 * 2
def baseEnd_3835659 : Nat := 1969536693743913700222631

theorem tailTrace_3835659 : CollatzResearch.WordTrace tailWord_3835659 prefixEnd_3835659 1969536693743913700222631 := by
  unfold tailWord_3835659
  simp only [CollatzResearch.WordTrace]
  refine ⟨139897976811069996248854031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93265317874046664165902687 139897976811069996248854031)
  ·
    refine ⟨209846965216604994373281047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139897976811069996248854031 209846965216604994373281047)
    ·
      refine ⟨314770447824907491559921571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209846965216604994373281047 314770447824907491559921571)
      ·
        refine ⟨472155671737361237339882357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 314770447824907491559921571 472155671737361237339882357)
        ·
          refine ⟨44264594225377616000613971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 472155671737361237339882357 44264594225377616000613971)
          ·
            refine ⟨66396891338066424000920957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44264594225377616000613971 66396891338066424000920957)
            ·
              refine ⟨24898834251774909000345359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 66396891338066424000920957 24898834251774909000345359)
              ·
                refine ⟨37348251377662363500518039, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24898834251774909000345359 37348251377662363500518039)
                ·
                  refine ⟨56022377066493545250777059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37348251377662363500518039 56022377066493545250777059)
                  ·
                    refine ⟨84033565599740317876165589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 56022377066493545250777059 84033565599740317876165589)
                    ·
                      refine ⟨1969536693743913700222631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 84033565599740317876165589 1969536693743913700222631)
                      ·
                        rfl

theorem cell23_3835659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 3, 1, 1, 1, 7].length) (baseStart_3835659 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3835659 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3835659 prefixEnd_3835659 := by exact prefixLift 3835659
  have htrace : WordTrace (prefixWord ++ tailWord_3835659) baseStart_3835659 baseEnd_3835659 := by
    simpa [prefixWord, tailWord_3835659, baseEnd_3835659] using wordTrace_append hprefix tailTrace_3835659
  have hstable : (prefixWord ++ tailWord_3835659).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3835659).length < 2 ^ (prefixWord ++ tailWord_3835659).sum := by decide
  have hdescent : baseEnd_3835659 < baseStart_3835659 := by decide
  rcases family_descends (prefixWord ++ tailWord_3835659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3835668 : List Nat := [2, 4, 4, 1, 2, 1, 1, 2, 1, 3, 2]
def baseStart_3835668 : Nat := 118140960795 + 3835668 * 2 ^ 59
def prefixEnd_3835668 : Nat := 4983230072969 + 3 ^ 40 * 3835668 * 2
def baseEnd_3835668 : Nat := 1969541315069804165010091

theorem tailTrace_3835668 : CollatzResearch.WordTrace tailWord_3835668 prefixEnd_3835668 1969541315069804165010091 := by
  unfold tailWord_3835668
  simp only [CollatzResearch.WordTrace]
  refine ⟨69949152534018695392965829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93265536712024927190621105 69949152534018695392965829)
  ·
    refine ⟨13115466100128505386181093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 69949152534018695392965829 13115466100128505386181093)
    ·
      refine ⟨2459149893774094759908955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13115466100128505386181093 2459149893774094759908955)
      ·
        refine ⟨3688724840661142139863433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2459149893774094759908955 3688724840661142139863433)
        ·
          refine ⟨2766543630495856604897575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3688724840661142139863433 2766543630495856604897575)
          ·
            refine ⟨4149815445743784907346363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2766543630495856604897575 4149815445743784907346363)
            ·
              refine ⟨6224723168615677361019545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4149815445743784907346363 6224723168615677361019545)
              ·
                refine ⟨4668542376461758020764659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6224723168615677361019545 4668542376461758020764659)
                ·
                  refine ⟨7002813564692637031146989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4668542376461758020764659 7002813564692637031146989)
                  ·
                    refine ⟨2626055086759738886680121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7002813564692637031146989 2626055086759738886680121)
                    ·
                      refine ⟨1969541315069804165010091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2626055086759738886680121 1969541315069804165010091)
                      ·
                        rfl

theorem cell23_3835668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 2, 1, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 2, 1, 1, 2, 1, 3, 2].length) (baseStart_3835668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3835668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3835668 prefixEnd_3835668 := by exact prefixLift 3835668
  have htrace : WordTrace (prefixWord ++ tailWord_3835668) baseStart_3835668 baseEnd_3835668 := by
    simpa [prefixWord, tailWord_3835668, baseEnd_3835668] using wordTrace_append hprefix tailTrace_3835668
  have hstable : (prefixWord ++ tailWord_3835668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3835668).length < 2 ^ (prefixWord ++ tailWord_3835668).sum := by decide
  have hdescent : baseEnd_3835668 < baseStart_3835668 := by decide
  rcases family_descends (prefixWord ++ tailWord_3835668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3835689 : List Nat := [1, 2, 1, 1, 1, 1, 1, 3, 4, 3, 5]
def baseStart_3835689 : Nat := 118140960795 + 3835689 * 2 ^ 59
def prefixEnd_3835689 : Nat := 4983230072969 + 3 ^ 40 * 3835689 * 2
def baseEnd_3835689 : Nat := 1969552098163548582847493

theorem tailTrace_3835689 : CollatzResearch.WordTrace tailWord_3835689 prefixEnd_3835689 1969552098163548582847493 := by
  unfold tailWord_3835689
  simp only [CollatzResearch.WordTrace]
  refine ⟨139899071000961311372446121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93266047333974207581630747 139899071000961311372446121)
  ·
    refine ⟨104924303250720983529334591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139899071000961311372446121 104924303250720983529334591)
    ·
      refine ⟨157386454876081475294001887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104924303250720983529334591 157386454876081475294001887)
      ·
        refine ⟨236079682314122212941002831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157386454876081475294001887 236079682314122212941002831)
        ·
          refine ⟨354119523471183319411504247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 236079682314122212941002831 354119523471183319411504247)
          ·
            refine ⟨531179285206774979117256371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 354119523471183319411504247 531179285206774979117256371)
            ·
              refine ⟨796768927810162468675884557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 531179285206774979117256371 796768927810162468675884557)
              ·
                refine ⟨298788347928810925753456709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 796768927810162468675884557 298788347928810925753456709)
                ·
                  refine ⟨56022815236652048578773133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 298788347928810925753456709 56022815236652048578773133)
                  ·
                    refine ⟨21008555713744518217039925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 56022815236652048578773133 21008555713744518217039925)
                    ·
                      refine ⟨1969552098163548582847493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21008555713744518217039925 1969552098163548582847493)
                      ·
                        rfl

theorem cell23_3835689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 3, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 3, 4, 3, 5].length) (baseStart_3835689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3835689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3835689 prefixEnd_3835689 := by exact prefixLift 3835689
  have htrace : WordTrace (prefixWord ++ tailWord_3835689) baseStart_3835689 baseEnd_3835689 := by
    simpa [prefixWord, tailWord_3835689, baseEnd_3835689] using wordTrace_append hprefix tailTrace_3835689
  have hstable : (prefixWord ++ tailWord_3835689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3835689).length < 2 ^ (prefixWord ++ tailWord_3835689).sum := by decide
  have hdescent : baseEnd_3835689 < baseStart_3835689 := by decide
  rcases family_descends (prefixWord ++ tailWord_3835689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3835740 : List Nat := [2, 2, 4, 2, 2, 1, 1, 1, 1, 4, 3]
def baseStart_3835740 : Nat := 118140960795 + 3835740 * 2 ^ 59
def prefixEnd_3835740 : Nat := 4983230072969 + 3 ^ 40 * 3835740 * 2
def baseEnd_3835740 : Nat := 1969578285676927883309759

theorem tailTrace_3835740 : CollatzResearch.WordTrace tailWord_3835740 prefixEnd_3835740 1969578285676927883309759 := by
  unfold tailWord_3835740
  simp only [CollatzResearch.WordTrace]
  refine ⟨69950465561888273541276337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93267287415851031388368449 69950465561888273541276337)
  ·
    refine ⟨52462849171416205155957253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69950465561888273541276337 52462849171416205155957253)
    ·
      refine ⟨9836784219640538466741985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 52462849171416205155957253 9836784219640538466741985)
      ·
        refine ⟨7377588164730403850056489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9836784219640538466741985 7377588164730403850056489)
        ·
          refine ⟨5533191123547802887542367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7377588164730403850056489 5533191123547802887542367)
          ·
            refine ⟨8299786685321704331313551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5533191123547802887542367 8299786685321704331313551)
            ·
              refine ⟨12449680027982556496970327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8299786685321704331313551 12449680027982556496970327)
              ·
                refine ⟨18674520041973834745455491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12449680027982556496970327 18674520041973834745455491)
                ·
                  refine ⟨28011780062960752118183237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18674520041973834745455491 28011780062960752118183237)
                  ·
                    refine ⟨5252208761805141022159357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28011780062960752118183237 5252208761805141022159357)
                    ·
                      refine ⟨1969578285676927883309759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5252208761805141022159357 1969578285676927883309759)
                      ·
                        rfl

theorem cell23_3835740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 1, 1, 1, 1, 4, 3].length) (baseStart_3835740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3835740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3835740 prefixEnd_3835740 := by exact prefixLift 3835740
  have htrace : WordTrace (prefixWord ++ tailWord_3835740) baseStart_3835740 baseEnd_3835740 := by
    simpa [prefixWord, tailWord_3835740, baseEnd_3835740] using wordTrace_append hprefix tailTrace_3835740
  have hstable : (prefixWord ++ tailWord_3835740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3835740).length < 2 ^ (prefixWord ++ tailWord_3835740).sum := by decide
  have hdescent : baseEnd_3835740 < baseStart_3835740 := by decide
  rcases family_descends (prefixWord ++ tailWord_3835740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3835747 : List Nat := [1, 1, 1, 5, 4, 1, 2, 3, 1, 4]
def baseStart_3835747 : Nat := 118140960795 + 3835747 * 2 ^ 59
def prefixEnd_3835747 : Nat := 4983230072969 + 3 ^ 40 * 3835747 * 2
def baseEnd_3835747 : Nat := 656527293347169785307409

theorem tailTrace_3835747 : CollatzResearch.WordTrace tailWord_3835747 prefixEnd_3835747 656527293347169785307409 := by
  unfold tailWord_3835747
  simp only [CollatzResearch.WordTrace]
  refine ⟨139901186434751187278057495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93267457623167458185371663 139901186434751187278057495)
  ·
    refine ⟨209851779652126780917086243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139901186434751187278057495 209851779652126780917086243)
    ·
      refine ⟨314777669478190171375629365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209851779652126780917086243 314777669478190171375629365)
      ·
        refine ⟨29510406513580328566465253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 314777669478190171375629365 29510406513580328566465253)
        ·
          refine ⟨5533201221296311606212235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29510406513580328566465253 5533201221296311606212235)
          ·
            refine ⟨8299801831944467409318353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5533201221296311606212235 8299801831944467409318353)
            ·
              refine ⟨6224851373958350556988765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8299801831944467409318353 6224851373958350556988765)
              ·
                refine ⟨2334319265234381458870787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6224851373958350556988765 2334319265234381458870787)
                ·
                  refine ⟨3501478897851572188306181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2334319265234381458870787 3501478897851572188306181)
                  ·
                    refine ⟨656527293347169785307409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3501478897851572188306181 656527293347169785307409)
                    ·
                      rfl

theorem cell23_3835747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 1, 2, 3, 1, 4].length) (baseStart_3835747 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3835747 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3835747 prefixEnd_3835747 := by exact prefixLift 3835747
  have htrace : WordTrace (prefixWord ++ tailWord_3835747) baseStart_3835747 baseEnd_3835747 := by
    simpa [prefixWord, tailWord_3835747, baseEnd_3835747] using wordTrace_append hprefix tailTrace_3835747
  have hstable : (prefixWord ++ tailWord_3835747).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3835747).length < 2 ^ (prefixWord ++ tailWord_3835747).sum := by decide
  have hdescent : baseEnd_3835747 < baseStart_3835747 := by decide
  rcases family_descends (prefixWord ++ tailWord_3835747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3835763 : List Nat := [1, 1, 1, 2, 2, 1, 3, 3, 4, 3, 2]
def baseStart_3835763 : Nat := 118140960795 + 3835763 * 2 ^ 59
def prefixEnd_3835763 : Nat := 4983230072969 + 3 ^ 40 * 3835763 * 2
def baseEnd_3835763 : Nat := 1969590095731981293322153

theorem tailTrace_3835763 : CollatzResearch.WordTrace tailWord_3835763 prefixEnd_3835763 1969590095731981293322153 := by
  unfold tailWord_3835763
  simp only [CollatzResearch.WordTrace]
  refine ⟨139901770002693222010639943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93267846668462148007093295 139901770002693222010639943)
  ·
    refine ⟨209852655004039833015959915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139901770002693222010639943 209852655004039833015959915)
    ·
      refine ⟨314778982506059749523939873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209852655004039833015959915 314778982506059749523939873)
      ·
        refine ⟨236084236879544812142954905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 314778982506059749523939873 236084236879544812142954905)
        ·
          refine ⟨177063177659658609107216179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 236084236879544812142954905 177063177659658609107216179)
          ·
            refine ⟨265594766489487913660824269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 177063177659658609107216179 265594766489487913660824269)
            ·
              refine ⟨99598037433557967622809101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 265594766489487913660824269 99598037433557967622809101)
              ·
                refine ⟨37349264037584237858553413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 99598037433557967622809101 37349264037584237858553413)
                ·
                  refine ⟨7002987007047044598478765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37349264037584237858553413 7002987007047044598478765)
                  ·
                    refine ⟨2626120127642641724429537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7002987007047044598478765 2626120127642641724429537)
                    ·
                      refine ⟨1969590095731981293322153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2626120127642641724429537 1969590095731981293322153)
                      ·
                        rfl

theorem cell23_3835763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 3, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 3, 4, 3, 2].length) (baseStart_3835763 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3835763 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3835763 prefixEnd_3835763 := by exact prefixLift 3835763
  have htrace : WordTrace (prefixWord ++ tailWord_3835763) baseStart_3835763 baseEnd_3835763 := by
    simpa [prefixWord, tailWord_3835763, baseEnd_3835763] using wordTrace_append hprefix tailTrace_3835763
  have hstable : (prefixWord ++ tailWord_3835763).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3835763).length < 2 ^ (prefixWord ++ tailWord_3835763).sum := by decide
  have hdescent : baseEnd_3835763 < baseStart_3835763 := by decide
  rcases family_descends (prefixWord ++ tailWord_3835763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3835777 : List Nat := [1, 2, 4, 4, 1, 1, 3, 1, 6]
def baseStart_3835777 : Nat := 118140960795 + 3835777 * 2 ^ 59
def prefixEnd_3835777 : Nat := 4983230072969 + 3 ^ 40 * 3835777 * 2
def baseEnd_3835777 : Nat := 218844142717904915394121

theorem tailTrace_3835777 : CollatzResearch.WordTrace tailWord_3835777 prefixEnd_3835777 218844142717904915394121 := by
  unfold tailWord_3835777
  simp only [CollatzResearch.WordTrace]
  refine ⟨139902280624642502401649585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93268187083095001601099723 139902280624642502401649585)
  ·
    refine ⟨104926710468481876801237189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139902280624642502401649585 104926710468481876801237189)
    ·
      refine ⟨19673758212840351900231973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 104926710468481876801237189 19673758212840351900231973)
      ·
        refine ⟨3688829664907565981293495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19673758212840351900231973 3688829664907565981293495)
        ·
          refine ⟨5533244497361348971940243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3688829664907565981293495 5533244497361348971940243)
          ·
            refine ⟨8299866746042023457910365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5533244497361348971940243 8299866746042023457910365)
            ·
              refine ⟨3112450029765758796716387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8299866746042023457910365 3112450029765758796716387)
              ·
                refine ⟨4668675044648638195074581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3112450029765758796716387 4668675044648638195074581)
                ·
                  refine ⟨218844142717904915394121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4668675044648638195074581 218844142717904915394121)
                  ·
                    rfl

theorem cell23_3835777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 1, 3, 1, 6].length) (baseStart_3835777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3835777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3835777 prefixEnd_3835777 := by exact prefixLift 3835777
  have htrace : WordTrace (prefixWord ++ tailWord_3835777) baseStart_3835777 baseEnd_3835777 := by
    simpa [prefixWord, tailWord_3835777, baseEnd_3835777] using wordTrace_append hprefix tailTrace_3835777
  have hstable : (prefixWord ++ tailWord_3835777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3835777).length < 2 ^ (prefixWord ++ tailWord_3835777).sum := by decide
  have hdescent : baseEnd_3835777 < baseStart_3835777 := by decide
  rcases family_descends (prefixWord ++ tailWord_3835777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3835793 : List Nat := [1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 4]
def baseStart_3835793 : Nat := 118140960795 + 3835793 * 2 ^ 59
def prefixEnd_3835793 : Nat := 4983230072969 + 3 ^ 40 * 3835793 * 2
def baseEnd_3835793 : Nat := 1969605500151616175947015

theorem tailTrace_3835793 : CollatzResearch.WordTrace tailWord_3835793 prefixEnd_3835793 1969605500151616175947015 := by
  unfold tailWord_3835793
  simp only [CollatzResearch.WordTrace]
  refine ⟨139902864192584537134232033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93268576128389691422821355 139902864192584537134232033)
  ·
    refine ⟨104927148144438402850674025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139902864192584537134232033 104927148144438402850674025)
    ·
      refine ⟨78695361108328802138005519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104927148144438402850674025 78695361108328802138005519)
      ·
        refine ⟨118043041662493203207008279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78695361108328802138005519 118043041662493203207008279)
        ·
          refine ⟨177064562493739804810512419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118043041662493203207008279 177064562493739804810512419)
          ·
            refine ⟨265596843740609707215768629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 177064562493739804810512419 265596843740609707215768629)
            ·
              refine ⟨24899704100682160051478309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 265596843740609707215768629 24899704100682160051478309)
              ·
                refine ⟨4668694518877905009652183, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24899704100682160051478309 4668694518877905009652183)
                ·
                  refine ⟨7003041778316857514478275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4668694518877905009652183 7003041778316857514478275)
                  ·
                    refine ⟨10504562667475286271717413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7003041778316857514478275 10504562667475286271717413)
                    ·
                      refine ⟨1969605500151616175947015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10504562667475286271717413 1969605500151616175947015)
                      ·
                        rfl

theorem cell23_3835793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 4].length) (baseStart_3835793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3835793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3835793 prefixEnd_3835793 := by exact prefixLift 3835793
  have htrace : WordTrace (prefixWord ++ tailWord_3835793) baseStart_3835793 baseEnd_3835793 := by
    simpa [prefixWord, tailWord_3835793, baseEnd_3835793] using wordTrace_append hprefix tailTrace_3835793
  have hstable : (prefixWord ++ tailWord_3835793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3835793).length < 2 ^ (prefixWord ++ tailWord_3835793).sum := by decide
  have hdescent : baseEnd_3835793 < baseStart_3835793 := by decide
  rcases family_descends (prefixWord ++ tailWord_3835793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3835798 : List Nat := [5, 3, 1, 1, 2, 2, 1, 3, 1, 4]
def baseStart_3835798 : Nat := 118140960795 + 3835798 * 2 ^ 59
def prefixEnd_3835798 : Nat := 4983230072969 + 3 ^ 40 * 3835798 * 2
def baseEnd_3835798 : Nat := 656536022518296218794831

theorem tailTrace_3835798 : CollatzResearch.WordTrace tailWord_3835798 prefixEnd_3835798 656536022518296218794831 := by
  unfold tailWord_3835798
  simp only [CollatzResearch.WordTrace]
  refine ⟨8743940409847901436760253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 93268697705044281992109365 8743940409847901436760253)
  ·
    refine ⟨3278977653692963038785095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8743940409847901436760253 3278977653692963038785095)
    ·
      refine ⟨4918466480539444558177643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3278977653692963038785095 4918466480539444558177643)
      ·
        refine ⟨7377699720809166837266465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4918466480539444558177643 7377699720809166837266465)
        ·
          refine ⟨5533274790606875127949849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7377699720809166837266465 5533274790606875127949849)
          ·
            refine ⟨4149956092955156345962387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5533274790606875127949849 4149956092955156345962387)
            ·
              refine ⟨6224934139432734518943581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4149956092955156345962387 6224934139432734518943581)
              ·
                refine ⟨2334350302287275444603843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6224934139432734518943581 2334350302287275444603843)
                ·
                  refine ⟨3501525453430913166905765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2334350302287275444603843 3501525453430913166905765)
                  ·
                    refine ⟨656536022518296218794831, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3501525453430913166905765 656536022518296218794831)
                    ·
                      rfl

theorem cell23_3835798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 2, 1, 3, 1, 4].length) (baseStart_3835798 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3835798 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3835798 prefixEnd_3835798 := by exact prefixLift 3835798
  have htrace : WordTrace (prefixWord ++ tailWord_3835798) baseStart_3835798 baseEnd_3835798 := by
    simpa [prefixWord, tailWord_3835798, baseEnd_3835798] using wordTrace_append hprefix tailTrace_3835798
  have hstable : (prefixWord ++ tailWord_3835798).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3835798).length < 2 ^ (prefixWord ++ tailWord_3835798).sum := by decide
  have hdescent : baseEnd_3835798 < baseStart_3835798 := by decide
  rcases family_descends (prefixWord ++ tailWord_3835798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3835804 : List Nat := [2, 2, 3, 3, 1, 1, 3, 3, 1, 1, 3]
def baseStart_3835804 : Nat := 118140960795 + 3835804 * 2 ^ 59
def prefixEnd_3835804 : Nat := 4983230072969 + 3 ^ 40 * 3835804 * 2
def baseEnd_3835804 : Nat := 1969611148438815632909465

theorem tailTrace_3835804 : CollatzResearch.WordTrace tailWord_3835804 prefixEnd_3835804 1969611148438815632909465 := by
  unfold tailWord_3835804
  simp only [CollatzResearch.WordTrace]
  refine ⟨69951632697772343006441233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93268843597029790675254977 69951632697772343006441233)
  ·
    refine ⟨52463724523329257254830925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69951632697772343006441233 52463724523329257254830925)
    ·
      refine ⟨19673896696248471470561597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52463724523329257254830925 19673896696248471470561597)
      ·
        refine ⟨7377711261093176801460599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19673896696248471470561597 7377711261093176801460599)
        ·
          refine ⟨11066566891639765202190899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7377711261093176801460599 11066566891639765202190899)
          ·
            refine ⟨16599850337459647803286349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11066566891639765202190899 16599850337459647803286349)
            ·
              refine ⟨6224943876547367926232381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16599850337459647803286349 6224943876547367926232381)
              ·
                refine ⟨2334353953705262972337143, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6224943876547367926232381 2334353953705262972337143)
                ·
                  refine ⟨3501530930557894458505715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2334353953705262972337143 3501530930557894458505715)
                  ·
                    refine ⟨5252296395836841687758573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3501530930557894458505715 5252296395836841687758573)
                    ·
                      refine ⟨1969611148438815632909465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5252296395836841687758573 1969611148438815632909465)
                      ·
                        rfl

theorem cell23_3835804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 3, 3, 1, 1, 3].length) (baseStart_3835804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3835804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3835804 prefixEnd_3835804 := by exact prefixLift 3835804
  have htrace : WordTrace (prefixWord ++ tailWord_3835804) baseStart_3835804 baseEnd_3835804 := by
    simpa [prefixWord, tailWord_3835804, baseEnd_3835804] using wordTrace_append hprefix tailTrace_3835804
  have hstable : (prefixWord ++ tailWord_3835804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3835804).length < 2 ^ (prefixWord ++ tailWord_3835804).sum := by decide
  have hdescent : baseEnd_3835804 < baseStart_3835804 := by decide
  rcases family_descends (prefixWord ++ tailWord_3835804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3835837 : List Nat := [1, 4, 1, 2, 3, 1, 4, 1, 2, 4]
def baseStart_3835837 : Nat := 118140960795 + 3835837 * 2 ^ 59
def prefixEnd_3835837 : Nat := 4983230072969 + 3 ^ 40 * 3835837 * 2
def baseEnd_3835837 : Nat := 656542697766804667932271

theorem tailTrace_3835837 : CollatzResearch.WordTrace tailWord_3835837 prefixEnd_3835837 656542697766804667932271 := by
  unfold tailWord_3835837
  simp only [CollatzResearch.WordTrace]
  refine ⟨139904469004425132648833765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93269646002950088432555843 139904469004425132648833765)
  ·
    refine ⟨26232087938329712371656331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 139904469004425132648833765 26232087938329712371656331)
    ·
      refine ⟨39348131907494568557484497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26232087938329712371656331 39348131907494568557484497)
      ·
        refine ⟨29511098930620926418113373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39348131907494568557484497 29511098930620926418113373)
        ·
          refine ⟨11066662098982847406792515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29511098930620926418113373 11066662098982847406792515)
          ·
            refine ⟨16599993148474271110188773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11066662098982847406792515 16599993148474271110188773)
            ·
              refine ⟨3112498715338925833160395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16599993148474271110188773 3112498715338925833160395)
              ·
                refine ⟨4668748073008388749740593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3112498715338925833160395 4668748073008388749740593)
                ·
                  refine ⟨3501561054756291562305445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4668748073008388749740593 3501561054756291562305445)
                  ·
                    refine ⟨656542697766804667932271, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3501561054756291562305445 656542697766804667932271)
                    ·
                      rfl

theorem cell23_3835837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 4, 1, 2, 4].length) (baseStart_3835837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3835837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3835837 prefixEnd_3835837 := by exact prefixLift 3835837
  have htrace : WordTrace (prefixWord ++ tailWord_3835837) baseStart_3835837 baseEnd_3835837 := by
    simpa [prefixWord, tailWord_3835837, baseEnd_3835837] using wordTrace_append hprefix tailTrace_3835837
  have hstable : (prefixWord ++ tailWord_3835837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3835837).length < 2 ^ (prefixWord ++ tailWord_3835837).sum := by decide
  have hdescent : baseEnd_3835837 < baseStart_3835837 := by decide
  rcases family_descends (prefixWord ++ tailWord_3835837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3835856 : List Nat := [2, 1, 1, 1, 1, 2, 4, 1, 1, 4, 5]
def baseStart_3835856 : Nat := 118140960795 + 3835856 * 2 ^ 59
def prefixEnd_3835856 : Nat := 4983230072969 + 3 ^ 40 * 3835856 * 2
def baseEnd_3835856 : Nat := 1969637849432849429459225

theorem tailTrace_3835856 : CollatzResearch.WordTrace tailWord_3835856 prefixEnd_3835856 1969637849432849429459225 := by
  unfold tailWord_3835856
  simp only [CollatzResearch.WordTrace]
  refine ⟨69952580995678149446887711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93270107994237532595850281 69952580995678149446887711)
  ·
    refine ⟨104928871493517224170331567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69952580995678149446887711 104928871493517224170331567)
    ·
      refine ⟨157393307240275836255497351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104928871493517224170331567 157393307240275836255497351)
      ·
        refine ⟨236089960860413754383246027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157393307240275836255497351 236089960860413754383246027)
        ·
          refine ⟨354134941290620631574869041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 236089960860413754383246027 354134941290620631574869041)
          ·
            refine ⟨265601205967965473681151781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 354134941290620631574869041 265601205967965473681151781)
            ·
              refine ⟨49800226118993526315215959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 265601205967965473681151781 49800226118993526315215959)
              ·
                refine ⟨74700339178490289472823939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49800226118993526315215959 74700339178490289472823939)
                ·
                  refine ⟨112050508767735434209235909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 74700339178490289472823939 112050508767735434209235909)
                  ·
                    refine ⟨21009470393950393914231733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 112050508767735434209235909 21009470393950393914231733)
                    ·
                      refine ⟨1969637849432849429459225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21009470393950393914231733 1969637849432849429459225)
                      ·
                        rfl

theorem cell23_3835856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 4, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 4, 1, 1, 4, 5].length) (baseStart_3835856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3835856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3835856 prefixEnd_3835856 := by exact prefixLift 3835856
  have htrace : WordTrace (prefixWord ++ tailWord_3835856) baseStart_3835856 baseEnd_3835856 := by
    simpa [prefixWord, tailWord_3835856, baseEnd_3835856] using wordTrace_append hprefix tailTrace_3835856
  have hstable : (prefixWord ++ tailWord_3835856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3835856).length < 2 ^ (prefixWord ++ tailWord_3835856).sum := by decide
  have hdescent : baseEnd_3835856 < baseStart_3835856 := by decide
  rcases family_descends (prefixWord ++ tailWord_3835856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3835860 : List Nat := [2, 4, 1, 2, 1, 1, 3, 2, 1, 3, 3]
def baseStart_3835860 : Nat := 118140960795 + 3835860 * 2 ^ 59
def prefixEnd_3835860 : Nat := 4983230072969 + 3 ^ 40 * 3835860 * 2
def baseEnd_3835860 : Nat := 1969639903355467413809207

theorem tailTrace_3835860 : CollatzResearch.WordTrace tailWord_3835860 prefixEnd_3835860 1969639903355467413809207 := by
  unfold tailWord_3835860
  simp only [CollatzResearch.WordTrace]
  refine ⟨69952653941670903788460517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93270205255561205051280689 69952653941670903788460517)
  ·
    refine ⟨13116122614063294460336347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 69952653941670903788460517 13116122614063294460336347)
    ·
      refine ⟨19674183921094941690504521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13116122614063294460336347 19674183921094941690504521)
      ·
        refine ⟨14755637940821206267878391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19674183921094941690504521 14755637940821206267878391)
        ·
          refine ⟨22133456911231809401817587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14755637940821206267878391 22133456911231809401817587)
          ·
            refine ⟨33200185366847714102726381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22133456911231809401817587 33200185366847714102726381)
            ·
              refine ⟨12450069512567892788522393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33200185366847714102726381 12450069512567892788522393)
              ·
                refine ⟨9337552134425919591391795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12450069512567892788522393 9337552134425919591391795)
                ·
                  refine ⟨14006328201638879387087693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9337552134425919591391795 14006328201638879387087693)
                  ·
                    refine ⟨5252373075614579770157885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14006328201638879387087693 5252373075614579770157885)
                    ·
                      refine ⟨1969639903355467413809207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5252373075614579770157885 1969639903355467413809207)
                      ·
                        rfl

theorem cell23_3835860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 3, 2, 1, 3, 3].length) (baseStart_3835860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3835860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3835860 prefixEnd_3835860 := by exact prefixLift 3835860
  have htrace : WordTrace (prefixWord ++ tailWord_3835860) baseStart_3835860 baseEnd_3835860 := by
    simpa [prefixWord, tailWord_3835860, baseEnd_3835860] using wordTrace_append hprefix tailTrace_3835860
  have hstable : (prefixWord ++ tailWord_3835860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3835860).length < 2 ^ (prefixWord ++ tailWord_3835860).sum := by decide
  have hdescent : baseEnd_3835860 < baseStart_3835860 := by decide
  rcases family_descends (prefixWord ++ tailWord_3835860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3835953 : List Nat := [1, 2, 2, 3, 1, 3, 1, 2, 1, 7]
def baseStart_3835953 : Nat := 118140960795 + 3835953 * 2 ^ 59
def prefixEnd_3835953 : Nat := 4983230072969 + 3 ^ 40 * 3835953 * 2
def baseEnd_3835953 : Nat := 656562552352111849982093

theorem tailTrace_3835953 : CollatzResearch.WordTrace tailWord_3835953 prefixEnd_3835953 656562552352111849982093 := by
  unfold tailWord_3835953
  simp only [CollatzResearch.WordTrace]
  refine ⟨139908699872004884460056513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93272466581336589640037675 139908699872004884460056513)
  ·
    refine ⟨104931524904003663345042385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139908699872004884460056513 104931524904003663345042385)
    ·
      refine ⟨78698643678002747508781789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104931524904003663345042385 78698643678002747508781789)
      ·
        refine ⟨29511991379251030315793171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 78698643678002747508781789 29511991379251030315793171)
        ·
          refine ⟨44267987068876545473689757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29511991379251030315793171 44267987068876545473689757)
          ·
            refine ⟨16600495150828704552633659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44267987068876545473689757 16600495150828704552633659)
            ·
              refine ⟨24900742726243056828950489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16600495150828704552633659 24900742726243056828950489)
              ·
                refine ⟨18675557044682292621712867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24900742726243056828950489 18675557044682292621712867)
                ·
                  refine ⟨28013335567023438932569301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18675557044682292621712867 28013335567023438932569301)
                  ·
                    refine ⟨656562552352111849982093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 28013335567023438932569301 656562552352111849982093)
                    ·
                      rfl

theorem cell23_3835953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 1, 2, 1, 7].length) (baseStart_3835953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3835953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3835953 prefixEnd_3835953 := by exact prefixLift 3835953
  have htrace : WordTrace (prefixWord ++ tailWord_3835953) baseStart_3835953 baseEnd_3835953 := by
    simpa [prefixWord, tailWord_3835953, baseEnd_3835953] using wordTrace_append hprefix tailTrace_3835953
  have hstable : (prefixWord ++ tailWord_3835953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3835953).length < 2 ^ (prefixWord ++ tailWord_3835953).sum := by decide
  have hdescent : baseEnd_3835953 < baseStart_3835953 := by decide
  rcases family_descends (prefixWord ++ tailWord_3835953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3835997 : List Nat := [1, 4, 4, 1, 1, 2, 1, 1, 1, 2, 5]
def baseStart_3835997 : Nat := 118140960795 + 3835997 * 2 ^ 59
def prefixEnd_3835997 : Nat := 4983230072969 + 3 ^ 40 * 3835997 * 2
def baseEnd_3835997 : Nat := 1969710250205133377796077

theorem tailTrace_3835997 : CollatzResearch.WordTrace tailWord_3835997 prefixEnd_3835997 1969710250205133377796077 := by
  unfold tailWord_3835997
  simp only [CollatzResearch.WordTrace]
  refine ⟨139910304683845479974658245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93273536455896986649772163 139910304683845479974658245)
  ·
    refine ⟨26233182128221027495248421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 139910304683845479974658245 26233182128221027495248421)
    ·
      refine ⟨4918721649041442655359079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26233182128221027495248421 4918721649041442655359079)
      ·
        refine ⟨7378082473562163983038619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4918721649041442655359079 7378082473562163983038619)
        ·
          refine ⟨11067123710343245974557929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7378082473562163983038619 11067123710343245974557929)
          ·
            refine ⟨8300342782757434480918447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11067123710343245974557929 8300342782757434480918447)
            ·
              refine ⟨12450514174136151721377671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8300342782757434480918447 12450514174136151721377671)
              ·
                refine ⟨18675771261204227582066507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12450514174136151721377671 18675771261204227582066507)
                ·
                  refine ⟨28013656891806341373099761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18675771261204227582066507 28013656891806341373099761)
                  ·
                    refine ⟨21010242668854756029824821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28013656891806341373099761 21010242668854756029824821)
                    ·
                      refine ⟨1969710250205133377796077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21010242668854756029824821 1969710250205133377796077)
                      ·
                        rfl

theorem cell23_3835997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 2, 1, 1, 1, 2, 5].length) (baseStart_3835997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3835997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3835997 prefixEnd_3835997 := by exact prefixLift 3835997
  have htrace : WordTrace (prefixWord ++ tailWord_3835997) baseStart_3835997 baseEnd_3835997 := by
    simpa [prefixWord, tailWord_3835997, baseEnd_3835997] using wordTrace_append hprefix tailTrace_3835997
  have hstable : (prefixWord ++ tailWord_3835997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3835997).length < 2 ^ (prefixWord ++ tailWord_3835997).sum := by decide
  have hdescent : baseEnd_3835997 < baseStart_3835997 := by decide
  rcases family_descends (prefixWord ++ tailWord_3835997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3836003 : List Nat := [1, 1, 1, 5, 1, 1, 2, 2, 2, 1, 6]
def baseStart_3836003 : Nat := 118140960795 + 3836003 * 2 ^ 59
def prefixEnd_3836003 : Nat := 4983230072969 + 3 ^ 40 * 3836003 * 2
def baseEnd_3836003 : Nat := 1969713331089060354321049

theorem tailTrace_3836003 : CollatzResearch.WordTrace tailWord_3836003 prefixEnd_3836003 1969713331089060354321049 := by
  unfold tailWord_3836003
  simp only [CollatzResearch.WordTrace]
  refine ⟨139910523521823742999376663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93273682347882495332917775 139910523521823742999376663)
  ·
    refine ⟨209865785282735614499064995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139910523521823742999376663 209865785282735614499064995)
    ·
      refine ⟨314798677924103421748597493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209865785282735614499064995 314798677924103421748597493)
      ·
        refine ⟨29512376055384695788931015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 314798677924103421748597493 29512376055384695788931015)
        ·
          refine ⟨44268564083077043683396523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29512376055384695788931015 44268564083077043683396523)
          ·
            refine ⟨66402846124615565525094785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44268564083077043683396523 66402846124615565525094785)
            ·
              refine ⟨49802134593461674143821089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66402846124615565525094785 49802134593461674143821089)
              ·
                refine ⟨37351600945096255607865817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49802134593461674143821089 37351600945096255607865817)
                ·
                  refine ⟨28013700708822191705899363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37351600945096255607865817 28013700708822191705899363)
                  ·
                    refine ⟨42020551063233287558849045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28013700708822191705899363 42020551063233287558849045)
                    ·
                      refine ⟨1969713331089060354321049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 42020551063233287558849045 1969713331089060354321049)
                      ·
                        rfl

theorem cell23_3836003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 2, 2, 2, 1, 6].length) (baseStart_3836003 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3836003 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3836003 prefixEnd_3836003 := by exact prefixLift 3836003
  have htrace : WordTrace (prefixWord ++ tailWord_3836003) baseStart_3836003 baseEnd_3836003 := by
    simpa [prefixWord, tailWord_3836003, baseEnd_3836003] using wordTrace_append hprefix tailTrace_3836003
  have hstable : (prefixWord ++ tailWord_3836003).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3836003).length < 2 ^ (prefixWord ++ tailWord_3836003).sum := by decide
  have hdescent : baseEnd_3836003 < baseStart_3836003 := by decide
  rcases family_descends (prefixWord ++ tailWord_3836003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3836050 : List Nat := [3, 2, 3, 1, 1, 1, 2, 1, 1, 2, 6]
def baseStart_3836050 : Nat := 118140960795 + 3836050 * 2 ^ 59
def prefixEnd_3836050 : Nat := 4983230072969 + 3 ^ 40 * 3836050 * 2
def baseEnd_3836050 : Nat := 1969737464679821670433333

theorem tailTrace_3836050 : CollatzResearch.WordTrace tailWord_3836050 prefixEnd_3836050 1969737464679821670433333 := by
  unfold tailWord_3836050
  simp only [CollatzResearch.WordTrace]
  refine ⟨34978059438163367506584401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93274825168435646684225069 34978059438163367506584401)
  ·
    refine ⟨26233544578622525629938301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34978059438163367506584401 26233544578622525629938301)
    ·
      refine ⟨9837579216983447111226863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26233544578622525629938301 9837579216983447111226863)
      ·
        refine ⟨14756368825475170666840295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9837579216983447111226863 14756368825475170666840295)
        ·
          refine ⟨22134553238212756000260443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14756368825475170666840295 22134553238212756000260443)
          ·
            refine ⟨33201829857319134000390665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22134553238212756000260443 33201829857319134000390665)
            ·
              refine ⟨24901372392989350500292999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33201829857319134000390665 24901372392989350500292999)
              ·
                refine ⟨37352058589484025750439499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24901372392989350500292999 37352058589484025750439499)
                ·
                  refine ⟨56028087884226038625659249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37352058589484025750439499 56028087884226038625659249)
                  ·
                    refine ⟨42021065913169528969244437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 56028087884226038625659249 42021065913169528969244437)
                    ·
                      refine ⟨1969737464679821670433333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 42021065913169528969244437 1969737464679821670433333)
                      ·
                        rfl

theorem cell23_3836050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 2, 1, 1, 2, 6].length) (baseStart_3836050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3836050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3836050 prefixEnd_3836050 := by exact prefixLift 3836050
  have htrace : WordTrace (prefixWord ++ tailWord_3836050) baseStart_3836050 baseEnd_3836050 := by
    simpa [prefixWord, tailWord_3836050, baseEnd_3836050] using wordTrace_append hprefix tailTrace_3836050
  have hstable : (prefixWord ++ tailWord_3836050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3836050).length < 2 ^ (prefixWord ++ tailWord_3836050).sum := by decide
  have hdescent : baseEnd_3836050 < baseStart_3836050 := by decide
  rcases family_descends (prefixWord ++ tailWord_3836050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3836060 : List Nat := [2, 2, 3, 2, 1, 1, 1, 1, 5, 5]
def baseStart_3836060 : Nat := 118140960795 + 3836060 * 2 ^ 59
def prefixEnd_3836060 : Nat := 4983230072969 + 3 ^ 40 * 3836060 * 2
def baseEnd_3836060 : Nat := 656580866495455543769429

theorem tailTrace_3836060 : CollatzResearch.WordTrace tailWord_3836060 prefixEnd_3836060 656580866495455543769429 := by
  unfold tailWord_3836060
  simp only [CollatzResearch.WordTrace]
  refine ⟨69956301241308620867100817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93275068321744827822801089 69956301241308620867100817)
  ·
    refine ⟨52467225930981465650325613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69956301241308620867100817 52467225930981465650325613)
    ·
      refine ⟨19675209724118049618872105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52467225930981465650325613 19675209724118049618872105)
      ·
        refine ⟨14756407293088537214154079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19675209724118049618872105 14756407293088537214154079)
        ·
          refine ⟨22134610939632805821231119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14756407293088537214154079 22134610939632805821231119)
          ·
            refine ⟨33201916409449208731846679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22134610939632805821231119 33201916409449208731846679)
            ·
              refine ⟨49802874614173813097770019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33201916409449208731846679 49802874614173813097770019)
              ·
                refine ⟨74704311921260719646655029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49802874614173813097770019 74704311921260719646655029)
                ·
                  refine ⟨7003529242618192466873909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 74704311921260719646655029 7003529242618192466873909)
                  ·
                    refine ⟨656580866495455543769429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7003529242618192466873909 656580866495455543769429)
                    ·
                      rfl

theorem cell23_3836060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 1, 1, 5, 5].length) (baseStart_3836060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3836060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3836060 prefixEnd_3836060 := by exact prefixLift 3836060
  have htrace : WordTrace (prefixWord ++ tailWord_3836060) baseStart_3836060 baseEnd_3836060 := by
    simpa [prefixWord, tailWord_3836060, baseEnd_3836060] using wordTrace_append hprefix tailTrace_3836060
  have hstable : (prefixWord ++ tailWord_3836060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3836060).length < 2 ^ (prefixWord ++ tailWord_3836060).sum := by decide
  have hdescent : baseEnd_3836060 < baseStart_3836060 := by decide
  rcases family_descends (prefixWord ++ tailWord_3836060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3836077 : List Nat := [1, 5, 2, 1, 2, 1, 2, 1, 3, 5]
def baseStart_3836077 : Nat := 118140960795 + 3836077 * 2 ^ 59
def prefixEnd_3836077 : Nat := 4983230072969 + 3 ^ 40 * 3836077 * 2
def baseEnd_3836077 : Nat := 656583776219164354931903

theorem tailTrace_3836077 : CollatzResearch.WordTrace tailWord_3836077 prefixEnd_3836077 656583776219164354931903 := by
  unfold tailWord_3836077
  simp only [CollatzResearch.WordTrace]
  refine ⟨139913222523555653637570485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93275481682370435758380323 139913222523555653637570485)
  ·
    refine ⟨13116864611583342528522233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 139913222523555653637570485 13116864611583342528522233)
    ·
      refine ⟨9837648458687506896391675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13116864611583342528522233 9837648458687506896391675)
      ·
        refine ⟨14756472688031260344587513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9837648458687506896391675 14756472688031260344587513)
        ·
          refine ⟨11067354516023445258440635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14756472688031260344587513 11067354516023445258440635)
          ·
            refine ⟨16601031774035167887660953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11067354516023445258440635 16601031774035167887660953)
            ·
              refine ⟨12450773830526375915745715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16601031774035167887660953 12450773830526375915745715)
              ·
                refine ⟨18676160745789563873618573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12450773830526375915745715 18676160745789563873618573)
                ·
                  refine ⟨7003560279671086452606965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18676160745789563873618573 7003560279671086452606965)
                  ·
                    refine ⟨656583776219164354931903, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7003560279671086452606965 656583776219164354931903)
                    ·
                      rfl

theorem cell23_3836077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 2, 1, 3, 5].length) (baseStart_3836077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3836077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3836077 prefixEnd_3836077 := by exact prefixLift 3836077
  have htrace : WordTrace (prefixWord ++ tailWord_3836077) baseStart_3836077 baseEnd_3836077 := by
    simpa [prefixWord, tailWord_3836077, baseEnd_3836077] using wordTrace_append hprefix tailTrace_3836077
  have hstable : (prefixWord ++ tailWord_3836077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3836077).length < 2 ^ (prefixWord ++ tailWord_3836077).sum := by decide
  have hdescent : baseEnd_3836077 < baseStart_3836077 := by decide
  rcases family_descends (prefixWord ++ tailWord_3836077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3836078 : List Nat := [4, 1, 4, 2, 1, 2, 1, 1, 2, 2, 3]
def baseStart_3836078 : Nat := 118140960795 + 3836078 * 2 ^ 59
def prefixEnd_3836078 : Nat := 4983230072969 + 3 ^ 40 * 3836078 * 2
def baseEnd_3836078 : Nat := 1969751842138147560883205

theorem tailTrace_3836078 : CollatzResearch.WordTrace tailWord_3836078 prefixEnd_3836078 1969751842138147560883205 := by
  unfold tailWord_3836078
  simp only [CollatzResearch.WordTrace]
  refine ⟨17489157374569003851044611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 93275505997701353872237925 17489157374569003851044611)
  ·
    refine ⟨26233736061853505776566917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17489157374569003851044611 26233736061853505776566917)
    ·
      refine ⟨4918825511597532333106297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26233736061853505776566917 4918825511597532333106297)
      ·
        refine ⟨3689119133698149249829723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4918825511597532333106297 3689119133698149249829723)
        ·
          refine ⟨5533678700547223874744585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3689119133698149249829723 5533678700547223874744585)
          ·
            refine ⟨4150259025410417906058439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5533678700547223874744585 4150259025410417906058439)
            ·
              refine ⟨6225388538115626859087659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4150259025410417906058439 6225388538115626859087659)
              ·
                refine ⟨9338082807173440288631489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6225388538115626859087659 9338082807173440288631489)
                ·
                  refine ⟨7003562105380080216473617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9338082807173440288631489 7003562105380080216473617)
                  ·
                    refine ⟨5252671579035060162355213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7003562105380080216473617 5252671579035060162355213)
                    ·
                      refine ⟨1969751842138147560883205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5252671579035060162355213 1969751842138147560883205)
                      ·
                        rfl

theorem cell23_3836078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 2, 1, 1, 2, 2, 3].length) (baseStart_3836078 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3836078 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3836078 prefixEnd_3836078 := by exact prefixLift 3836078
  have htrace : WordTrace (prefixWord ++ tailWord_3836078) baseStart_3836078 baseEnd_3836078 := by
    simpa [prefixWord, tailWord_3836078, baseEnd_3836078] using wordTrace_append hprefix tailTrace_3836078
  have hstable : (prefixWord ++ tailWord_3836078).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3836078).length < 2 ^ (prefixWord ++ tailWord_3836078).sum := by decide
  have hdescent : baseEnd_3836078 < baseStart_3836078 := by decide
  rcases family_descends (prefixWord ++ tailWord_3836078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3836090 : List Nat := [3, 1, 1, 1, 2, 2, 4, 2, 1, 6]
def baseStart_3836090 : Nat := 118140960795 + 3836090 * 2 ^ 59
def prefixEnd_3836090 : Nat := 4983230072969 + 3 ^ 40 * 3836090 * 2
def baseEnd_3836090 : Nat := 656586001302000504644383

theorem tailTrace_3836090 : CollatzResearch.WordTrace tailWord_3836090 prefixEnd_3836090 656586001302000504644383 := by
  unfold tailWord_3836090
  simp only [CollatzResearch.WordTrace]
  refine ⟨34978424168127139214448431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93275797781672371238529149 34978424168127139214448431)
  ·
    refine ⟨52467636252190708821672647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34978424168127139214448431 52467636252190708821672647)
    ·
      refine ⟨78701454378286063232508971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52467636252190708821672647 78701454378286063232508971)
      ·
        refine ⟨118052181567429094848763457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78701454378286063232508971 118052181567429094848763457)
        ·
          refine ⟨88539136175571821136572593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 118052181567429094848763457 88539136175571821136572593)
          ·
            refine ⟨66404352131678865852429445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 88539136175571821136572593 66404352131678865852429445)
            ·
              refine ⟨12450816024689787347330521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 66404352131678865852429445 12450816024689787347330521)
              ·
                refine ⟨9338112018517340510497891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12450816024689787347330521 9338112018517340510497891)
                ·
                  refine ⟨14007168027776010765746837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9338112018517340510497891 14007168027776010765746837)
                  ·
                    refine ⟨656586001302000504644383, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14007168027776010765746837 656586001302000504644383)
                    ·
                      rfl

theorem cell23_3836090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 4, 2, 1, 6].length) (baseStart_3836090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3836090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3836090 prefixEnd_3836090 := by exact prefixLift 3836090
  have htrace : WordTrace (prefixWord ++ tailWord_3836090) baseStart_3836090 baseEnd_3836090 := by
    simpa [prefixWord, tailWord_3836090, baseEnd_3836090] using wordTrace_append hprefix tailTrace_3836090
  have hstable : (prefixWord ++ tailWord_3836090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3836090).length < 2 ^ (prefixWord ++ tailWord_3836090).sum := by decide
  have hdescent : baseEnd_3836090 < baseStart_3836090 := by decide
  rcases family_descends (prefixWord ++ tailWord_3836090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3836094 : List Nat := [4, 2, 1, 1, 4, 1, 1, 3, 1, 5]
def baseStart_3836094 : Nat := 118140960795 + 3836094 * 2 ^ 59
def prefixEnd_3836094 : Nat := 4983230072969 + 3 ^ 40 * 3836094 * 2
def baseEnd_3836094 : Nat := 656586685942873166094377

theorem tailTrace_3836094 : CollatzResearch.WordTrace tailWord_3836094 prefixEnd_3836094 656586685942873166094377 := by
  unfold tailWord_3836094
  simp only [CollatzResearch.WordTrace]
  refine ⟨17489230320561758192617417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 93275895042996043693959557 17489230320561758192617417)
  ·
    refine ⟨13116922740421318644463063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17489230320561758192617417 13116922740421318644463063)
    ·
      refine ⟨19675384110631977966694595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13116922740421318644463063 19675384110631977966694595)
      ·
        refine ⟨29513076165947966950041893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19675384110631977966694595 29513076165947966950041893)
        ·
          refine ⟨5533701781115243803132855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29513076165947966950041893 5533701781115243803132855)
          ·
            refine ⟨8300552671672865704699283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5533701781115243803132855 8300552671672865704699283)
            ·
              refine ⟨12450829007509298557048925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8300552671672865704699283 12450829007509298557048925)
              ·
                refine ⟨4669060877815986958893347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12450829007509298557048925 4669060877815986958893347)
                ·
                  refine ⟨7003591316723980438340021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4669060877815986958893347 7003591316723980438340021)
                  ·
                    refine ⟨656586685942873166094377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7003591316723980438340021 656586685942873166094377)
                    ·
                      rfl

theorem cell23_3836094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 1, 1, 3, 1, 5].length) (baseStart_3836094 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3836094 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3836094 prefixEnd_3836094 := by exact prefixLift 3836094
  have htrace : WordTrace (prefixWord ++ tailWord_3836094) baseStart_3836094 baseEnd_3836094 := by
    simpa [prefixWord, tailWord_3836094, baseEnd_3836094] using wordTrace_append hprefix tailTrace_3836094
  have hstable : (prefixWord ++ tailWord_3836094).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3836094).length < 2 ^ (prefixWord ++ tailWord_3836094).sum := by decide
  have hdescent : baseEnd_3836094 < baseStart_3836094 := by decide
  rcases family_descends (prefixWord ++ tailWord_3836094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3836131 : List Nat := [1, 1, 1, 8, 1, 1, 2, 2, 1, 1, 4]
def baseStart_3836131 : Nat := 118140960795 + 3836131 * 2 ^ 59
def prefixEnd_3836131 : Nat := 4983230072969 + 3 ^ 40 * 3836131 * 2
def baseEnd_3836131 : Nat := 1969779056612835853520461

theorem tailTrace_3836131 : CollatzResearch.WordTrace tailWord_3836131 prefixEnd_3836131 1969779056612835853520461 := by
  unfold tailWord_3836131
  simp only [CollatzResearch.WordTrace]
  refine ⟨139915192065360020860036247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93276794710240013906690831 139915192065360020860036247)
  ·
    refine ⟨209872788098040031290054371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139915192065360020860036247 209872788098040031290054371)
    ·
      refine ⟨314809182147060046935081557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209872788098040031290054371 314809182147060046935081557)
      ·
        refine ⟨3689170103285859925020487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 8 314809182147060046935081557 3689170103285859925020487)
        ·
          refine ⟨5533755154928789887530731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3689170103285859925020487 5533755154928789887530731)
          ·
            refine ⟨8300632732393184831296097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5533755154928789887530731 8300632732393184831296097)
            ·
              refine ⟨6225474549294888623472073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8300632732393184831296097 6225474549294888623472073)
              ·
                refine ⟨4669105911971166467604055, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6225474549294888623472073 4669105911971166467604055)
                ·
                  refine ⟨7003658867956749701406083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4669105911971166467604055 7003658867956749701406083)
                  ·
                    refine ⟨10505488301935124552109125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7003658867956749701406083 10505488301935124552109125)
                    ·
                      refine ⟨1969779056612835853520461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10505488301935124552109125 1969779056612835853520461)
                      ·
                        rfl

theorem cell23_3836131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 1, 2, 2, 1, 1, 4].length) (baseStart_3836131 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3836131 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3836131 prefixEnd_3836131 := by exact prefixLift 3836131
  have htrace : WordTrace (prefixWord ++ tailWord_3836131) baseStart_3836131 baseEnd_3836131 := by
    simpa [prefixWord, tailWord_3836131, baseEnd_3836131] using wordTrace_append hprefix tailTrace_3836131
  have hstable : (prefixWord ++ tailWord_3836131).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3836131).length < 2 ^ (prefixWord ++ tailWord_3836131).sum := by decide
  have hdescent : baseEnd_3836131 < baseStart_3836131 := by decide
  rcases family_descends (prefixWord ++ tailWord_3836131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3836147 : List Nat := [1, 1, 1, 2, 2, 4, 1, 1, 6, 1, 3]
def baseStart_3836147 : Nat := 118140960795 + 3836147 * 2 ^ 59
def prefixEnd_3836147 : Nat := 4983230072969 + 3 ^ 40 * 3836147 * 2
def baseEnd_3836147 : Nat := 1969787272303307790920387

theorem tailTrace_3836147 : CollatzResearch.WordTrace tailWord_3836147 prefixEnd_3836147 1969787272303307790920387 := by
  unfold tailWord_3836147
  simp only [CollatzResearch.WordTrace]
  refine ⟨139915775633302055592618695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93277183755534703728412463 139915775633302055592618695)
  ·
    refine ⟨209873663449953083388928043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139915775633302055592618695 209873663449953083388928043)
    ·
      refine ⟨314810495174929625083392065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209873663449953083388928043 314810495174929625083392065)
      ·
        refine ⟨236107871381197218812544049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 314810495174929625083392065 236107871381197218812544049)
        ·
          refine ⟨177080903535897914109408037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 236107871381197218812544049 177080903535897914109408037)
          ·
            refine ⟨33202669412980858895514007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 177080903535897914109408037 33202669412980858895514007)
            ·
              refine ⟨49804004119471288343271011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33202669412980858895514007 49804004119471288343271011)
              ·
                refine ⟨74706006179206932514906517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49804004119471288343271011 74706006179206932514906517)
                ·
                  refine ⟨3501844039650324961636243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 74706006179206932514906517 3501844039650324961636243)
                  ·
                    refine ⟨5252766059475487442454365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3501844039650324961636243 5252766059475487442454365)
                    ·
                      refine ⟨1969787272303307790920387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5252766059475487442454365 1969787272303307790920387)
                      ·
                        rfl

theorem cell23_3836147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 1, 1, 6, 1, 3].length) (baseStart_3836147 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3836147 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3836147 prefixEnd_3836147 := by exact prefixLift 3836147
  have htrace : WordTrace (prefixWord ++ tailWord_3836147) baseStart_3836147 baseEnd_3836147 := by
    simpa [prefixWord, tailWord_3836147, baseEnd_3836147] using wordTrace_append hprefix tailTrace_3836147
  have hstable : (prefixWord ++ tailWord_3836147).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3836147).length < 2 ^ (prefixWord ++ tailWord_3836147).sum := by decide
  have hdescent : baseEnd_3836147 < baseStart_3836147 := by decide
  rcases family_descends (prefixWord ++ tailWord_3836147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3836174 : List Nat := [4, 1, 1, 2, 1, 2, 2, 2, 3, 3, 2]
def baseStart_3836174 : Nat := 118140960795 + 3836174 * 2 ^ 59
def prefixEnd_3836174 : Nat := 4983230072969 + 3 ^ 40 * 3836174 * 2
def baseEnd_3836174 : Nat := 1969801136280979185282763

theorem tailTrace_3836174 : CollatzResearch.WordTrace tailWord_3836174 prefixEnd_3836174 1969801136280979185282763 := by
  unfold tailWord_3836174
  simp only [CollatzResearch.WordTrace]
  refine ⟨17489595050525529900481447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 93277840269469492802567717 17489595050525529900481447)
  ·
    refine ⟨26234392575788294850722171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17489595050525529900481447 26234392575788294850722171)
    ·
      refine ⟨39351588863682442276083257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26234392575788294850722171 39351588863682442276083257)
      ·
        refine ⟨29513691647761831707062443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39351588863682442276083257 29513691647761831707062443)
        ·
          refine ⟨44270537471642747560593665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29513691647761831707062443 44270537471642747560593665)
          ·
            refine ⟨33202903103732060670445249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44270537471642747560593665 33202903103732060670445249)
            ·
              refine ⟨24902177327799045502833937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33202903103732060670445249 24902177327799045502833937)
              ·
                refine ⟨18676632995849284127125453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24902177327799045502833937 18676632995849284127125453)
                ·
                  refine ⟨7003737373443481547672045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18676632995849284127125453 7003737373443481547672045)
                  ·
                    refine ⟨2626401515041305580377017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7003737373443481547672045 2626401515041305580377017)
                    ·
                      refine ⟨1969801136280979185282763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2626401515041305580377017 1969801136280979185282763)
                      ·
                        rfl

theorem cell23_3836174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 2, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 2, 2, 3, 3, 2].length) (baseStart_3836174 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3836174 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3836174 prefixEnd_3836174 := by exact prefixLift 3836174
  have htrace : WordTrace (prefixWord ++ tailWord_3836174) baseStart_3836174 baseEnd_3836174 := by
    simpa [prefixWord, tailWord_3836174, baseEnd_3836174] using wordTrace_append hprefix tailTrace_3836174
  have hstable : (prefixWord ++ tailWord_3836174).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3836174).length < 2 ^ (prefixWord ++ tailWord_3836174).sum := by decide
  have hdescent : baseEnd_3836174 < baseStart_3836174 := by decide
  rcases family_descends (prefixWord ++ tailWord_3836174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3836181 : List Nat := [1, 3, 2, 1, 2, 1, 6, 1, 2, 1, 3]
def baseStart_3836181 : Nat := 118140960795 + 3836181 * 2 ^ 59
def prefixEnd_3836181 : Nat := 4983230072969 + 3 ^ 40 * 3836181 * 2
def baseEnd_3836181 : Nat := 1969804730645560657895231

theorem tailTrace_3836181 : CollatzResearch.WordTrace tailWord_3836181 prefixEnd_3836181 1969804730645560657895231 := by
  unfold tailWord_3836181
  simp only [CollatzResearch.WordTrace]
  refine ⟨139917015715178879399356397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93278010476785919599570931 139917015715178879399356397)
  ·
    refine ⟨52468880893192079774758649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 139917015715178879399356397 52468880893192079774758649)
    ·
      refine ⟨39351660669894059831068987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52468880893192079774758649 39351660669894059831068987)
      ·
        refine ⟨59027491004841089746603481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39351660669894059831068987 59027491004841089746603481)
        ·
          refine ⟨44270618253630817309952611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59027491004841089746603481 44270618253630817309952611)
          ·
            refine ⟨66405927380446225964928917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44270618253630817309952611 66405927380446225964928917)
            ·
              refine ⟨3112777845958416842106043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 66405927380446225964928917 3112777845958416842106043)
              ·
                refine ⟨4669166768937625263159065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3112777845958416842106043 4669166768937625263159065)
                ·
                  refine ⟨3501875076703218947369299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4669166768937625263159065 3501875076703218947369299)
                  ·
                    refine ⟨5252812615054828421053949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3501875076703218947369299 5252812615054828421053949)
                    ·
                      refine ⟨1969804730645560657895231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5252812615054828421053949 1969804730645560657895231)
                      ·
                        rfl

theorem cell23_3836181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 6, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 6, 1, 2, 1, 3].length) (baseStart_3836181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3836181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3836181 prefixEnd_3836181 := by exact prefixLift 3836181
  have htrace : WordTrace (prefixWord ++ tailWord_3836181) baseStart_3836181 baseEnd_3836181 := by
    simpa [prefixWord, tailWord_3836181, baseEnd_3836181] using wordTrace_append hprefix tailTrace_3836181
  have hstable : (prefixWord ++ tailWord_3836181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3836181).length < 2 ^ (prefixWord ++ tailWord_3836181).sum := by decide
  have hdescent : baseEnd_3836181 < baseStart_3836181 := by decide
  rcases family_descends (prefixWord ++ tailWord_3836181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3836191 : List Nat := [1, 1, 2, 4, 3, 1, 3, 2, 1, 3, 2]
def baseStart_3836191 : Nat := 118140960795 + 3836191 * 2 ^ 59
def prefixEnd_3836191 : Nat := 4983230072969 + 3 ^ 40 * 3836191 * 2
def baseEnd_3836191 : Nat := 1969809865452105618770185

theorem tailTrace_3836191 : CollatzResearch.WordTrace tailWord_3836191 prefixEnd_3836191 1969809865452105618770185 := by
  unfold tailWord_3836191
  simp only [CollatzResearch.WordTrace]
  refine ⟨139917380445142651107220427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93278253630095100738146951 139917380445142651107220427)
  ·
    refine ⟨209876070667713976660830641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139917380445142651107220427 209876070667713976660830641)
    ·
      refine ⟨157407053000785482495622981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 209876070667713976660830641 157407053000785482495622981)
      ·
        refine ⟨29513822437647277967929309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 157407053000785482495622981 29513822437647277967929309)
        ·
          refine ⟨11067683414117729237973491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29513822437647277967929309 11067683414117729237973491)
          ·
            refine ⟨16601525121176593856960237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11067683414117729237973491 16601525121176593856960237)
            ·
              refine ⟨6225571920441222696360089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16601525121176593856960237 6225571920441222696360089)
              ·
                refine ⟨4669178940330917022270067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6225571920441222696360089 4669178940330917022270067)
                ·
                  refine ⟨7003768410496375533405101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4669178940330917022270067 7003768410496375533405101)
                  ·
                    refine ⟨2626413153936140825026913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7003768410496375533405101 2626413153936140825026913)
                    ·
                      refine ⟨1969809865452105618770185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2626413153936140825026913 1969809865452105618770185)
                      ·
                        rfl

theorem cell23_3836191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 3, 2, 1, 3, 2].length) (baseStart_3836191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3836191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3836191 prefixEnd_3836191 := by exact prefixLift 3836191
  have htrace : WordTrace (prefixWord ++ tailWord_3836191) baseStart_3836191 baseEnd_3836191 := by
    simpa [prefixWord, tailWord_3836191, baseEnd_3836191] using wordTrace_append hprefix tailTrace_3836191
  have hstable : (prefixWord ++ tailWord_3836191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3836191).length < 2 ^ (prefixWord ++ tailWord_3836191).sum := by decide
  have hdescent : baseEnd_3836191 < baseStart_3836191 := by decide
  rcases family_descends (prefixWord ++ tailWord_3836191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3836204 : List Nat := [2, 2, 1, 1, 1, 3, 2, 1, 6, 2, 2]
def baseStart_3836204 : Nat := 118140960795 + 3836204 * 2 ^ 59
def prefixEnd_3836204 : Nat := 4983230072969 + 3 ^ 40 * 3836204 * 2
def baseEnd_3836204 : Nat := 1969816540700614067907625

theorem tailTrace_3836204 : CollatzResearch.WordTrace tailWord_3836204 prefixEnd_3836204 1969816540700614067907625 := by
  unfold tailWord_3836204
  simp only [CollatzResearch.WordTrace]
  refine ⟨69958927297047777163721833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93278569729397036218295777 69958927297047777163721833)
  ·
    refine ⟨52469195472785832872791375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69958927297047777163721833 52469195472785832872791375)
    ·
      refine ⟨78703793209178749309187063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52469195472785832872791375 78703793209178749309187063)
      ·
        refine ⟨118055689813768123963780595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78703793209178749309187063 118055689813768123963780595)
        ·
          refine ⟨177083534720652185945670893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118055689813768123963780595 177083534720652185945670893)
          ·
            refine ⟨66406325520244569729626585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 177083534720652185945670893 66406325520244569729626585)
            ·
              refine ⟨49804744140183427297219939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66406325520244569729626585 49804744140183427297219939)
              ·
                refine ⟨74707116210275140945829909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49804744140183427297219939 74707116210275140945829909)
                ·
                  refine ⟨3501896072356647231835777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 74707116210275140945829909 3501896072356647231835777)
                  ·
                    refine ⟨2626422054267485423876833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3501896072356647231835777 2626422054267485423876833)
                    ·
                      refine ⟨1969816540700614067907625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2626422054267485423876833 1969816540700614067907625)
                      ·
                        rfl

theorem cell23_3836204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 6, 2, 2].length) (baseStart_3836204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3836204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3836204 prefixEnd_3836204 := by exact prefixLift 3836204
  have htrace : WordTrace (prefixWord ++ tailWord_3836204) baseStart_3836204 baseEnd_3836204 := by
    simpa [prefixWord, tailWord_3836204, baseEnd_3836204] using wordTrace_append hprefix tailTrace_3836204
  have hstable : (prefixWord ++ tailWord_3836204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3836204).length < 2 ^ (prefixWord ++ tailWord_3836204).sum := by decide
  have hdescent : baseEnd_3836204 < baseStart_3836204 := by decide
  rcases family_descends (prefixWord ++ tailWord_3836204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3836287 : List Nat := [1, 1, 2, 2, 1, 1, 2, 2, 7, 4]
def baseStart_3836287 : Nat := 118140960795 + 3836287 * 2 ^ 59
def prefixEnd_3836287 : Nat := 4983230072969 + 3 ^ 40 * 3836287 * 2
def baseEnd_3836287 : Nat := 656619719864979081056581

theorem tailTrace_3836287 : CollatzResearch.WordTrace tailWord_3836287 prefixEnd_3836287 656619719864979081056581 := by
  unfold tailWord_3836287
  simp only [CollatzResearch.WordTrace]
  refine ⟨139920881852794859502715115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93280587901863239668476743 139920881852794859502715115)
  ·
    refine ⟨209881322779192289254072673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139920881852794859502715115 209881322779192289254072673)
    ·
      refine ⟨157410992084394216940554505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 209881322779192289254072673 157410992084394216940554505)
      ·
        refine ⟨118058244063295662705415879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 157410992084394216940554505 118058244063295662705415879)
        ·
          refine ⟨177087366094943494058123819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118058244063295662705415879 177087366094943494058123819)
          ·
            refine ⟨265631049142415241087185729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 177087366094943494058123819 265631049142415241087185729)
            ·
              refine ⟨199223286856811430815389297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 265631049142415241087185729 199223286856811430815389297)
              ·
                refine ⟨149417465142608573111541973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 199223286856811430815389297 149417465142608573111541973)
                ·
                  refine ⟨3501971839279888432301765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 149417465142608573111541973 3501971839279888432301765)
                  ·
                    refine ⟨656619719864979081056581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3501971839279888432301765 656619719864979081056581)
                    ·
                      rfl

theorem cell23_3836287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 2, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 2, 7, 4].length) (baseStart_3836287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3836287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3836287 prefixEnd_3836287 := by exact prefixLift 3836287
  have htrace : WordTrace (prefixWord ++ tailWord_3836287) baseStart_3836287 baseEnd_3836287 := by
    simpa [prefixWord, tailWord_3836287, baseEnd_3836287] using wordTrace_append hprefix tailTrace_3836287
  have hstable : (prefixWord ++ tailWord_3836287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3836287).length < 2 ^ (prefixWord ++ tailWord_3836287).sum := by decide
  have hdescent : baseEnd_3836287 < baseStart_3836287 := by decide
  rcases family_descends (prefixWord ++ tailWord_3836287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3836314 : List Nat := [3, 1, 1, 4, 1, 2, 2, 1, 1, 4, 3]
def baseStart_3836314 : Nat := 118140960795 + 3836314 * 2 ^ 59
def prefixEnd_3836314 : Nat := 4983230072969 + 3 ^ 40 * 3836314 * 2
def baseEnd_3836314 : Nat := 1969873023572608637532119

theorem tailTrace_3836314 : CollatzResearch.WordTrace tailWord_3836314 prefixEnd_3836314 1969873023572608637532119 := by
  unfold tailWord_3836314
  simp only [CollatzResearch.WordTrace]
  refine ⟨34980466655924260778486999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93281244415798028742631997 34980466655924260778486999)
  ·
    refine ⟨52470699983886391167730499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34980466655924260778486999 52470699983886391167730499)
    ·
      refine ⟨78706049975829586751595749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52470699983886391167730499 78706049975829586751595749)
      ·
        refine ⟨14757384370468047515924203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 78706049975829586751595749 14757384370468047515924203)
        ·
          refine ⟨22136076555702071273886305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14757384370468047515924203 22136076555702071273886305)
          ·
            refine ⟨16602057416776553455414729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22136076555702071273886305 16602057416776553455414729)
            ·
              refine ⟨12451543062582415091561047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16602057416776553455414729 12451543062582415091561047)
              ·
                refine ⟨18677314593873622637341571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12451543062582415091561047 18677314593873622637341571)
                ·
                  refine ⟨28015971890810433956012357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18677314593873622637341571 28015971890810433956012357)
                  ·
                    refine ⟨5252994729526956366752317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28015971890810433956012357 5252994729526956366752317)
                    ·
                      refine ⟨1969873023572608637532119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5252994729526956366752317 1969873023572608637532119)
                      ·
                        rfl

theorem cell23_3836314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 2, 1, 1, 4, 3].length) (baseStart_3836314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3836314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3836314 prefixEnd_3836314 := by exact prefixLift 3836314
  have htrace : WordTrace (prefixWord ++ tailWord_3836314) baseStart_3836314 baseEnd_3836314 := by
    simpa [prefixWord, tailWord_3836314, baseEnd_3836314] using wordTrace_append hprefix tailTrace_3836314
  have hstable : (prefixWord ++ tailWord_3836314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3836314).length < 2 ^ (prefixWord ++ tailWord_3836314).sum := by decide
  have hdescent : baseEnd_3836314 < baseStart_3836314 := by decide
  rcases family_descends (prefixWord ++ tailWord_3836314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3836338 : List Nat := [3, 2, 1, 1, 1, 1, 7, 2, 1, 4]
def baseStart_3836338 : Nat := 118140960795 + 3836338 * 2 ^ 59
def prefixEnd_3836338 : Nat := 4983230072969 + 3 ^ 40 * 3836338 * 2
def baseEnd_3836338 : Nat := 656628449036105514544003

theorem tailTrace_3836338 : CollatzResearch.WordTrace tailWord_3836338 prefixEnd_3836338 656628449036105514544003 := by
  unfold tailWord_3836338
  simp only [CollatzResearch.WordTrace]
  refine ⟨34980685493902523803205417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93281827983740063475214445 34980685493902523803205417)
  ·
    refine ⟨26235514120426892852404063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34980685493902523803205417 26235514120426892852404063)
    ·
      refine ⟨39353271180640339278606095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26235514120426892852404063 39353271180640339278606095)
      ·
        refine ⟨59029906770960508917909143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39353271180640339278606095 59029906770960508917909143)
        ·
          refine ⟨88544860156440763376863715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59029906770960508917909143 88544860156440763376863715)
          ·
            refine ⟨132817290234661145065295573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88544860156440763376863715 132817290234661145065295573)
            ·
              refine ⟨3112905239874870587467865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 132817290234661145065295573 3112905239874870587467865)
              ·
                refine ⟨2334678929906152940600899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3112905239874870587467865 2334678929906152940600899)
                ·
                  refine ⟨3502018394859229410901349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2334678929906152940600899 3502018394859229410901349)
                  ·
                    refine ⟨656628449036105514544003, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3502018394859229410901349 656628449036105514544003)
                    ·
                      rfl

theorem cell23_3836338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 7, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 7, 2, 1, 4].length) (baseStart_3836338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3836338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3836338 prefixEnd_3836338 := by exact prefixLift 3836338
  have htrace : WordTrace (prefixWord ++ tailWord_3836338) baseStart_3836338 baseEnd_3836338 := by
    simpa [prefixWord, tailWord_3836338, baseEnd_3836338] using wordTrace_append hprefix tailTrace_3836338
  have hstable : (prefixWord ++ tailWord_3836338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3836338).length < 2 ^ (prefixWord ++ tailWord_3836338).sum := by decide
  have hdescent : baseEnd_3836338 < baseStart_3836338 := by decide
  rcases family_descends (prefixWord ++ tailWord_3836338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3836378 : List Nat := [3, 1, 1, 2, 3, 1, 2, 5, 1, 1, 3]
def baseStart_3836378 : Nat := 118140960795 + 3836378 * 2 ^ 59
def prefixEnd_3836378 : Nat := 4983230072969 + 3 ^ 40 * 3836378 * 2
def baseEnd_3836378 : Nat := 1969905886334496387131825

theorem tailTrace_3836378 : CollatzResearch.WordTrace tailWord_3836378 prefixEnd_3836378 1969905886334496387131825 := by
  unfold tailWord_3836378
  simp only [CollatzResearch.WordTrace]
  refine ⟨34981050223866295511069447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93282800596976788029518525 34981050223866295511069447)
  ·
    refine ⟨52471575335799443266604171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34981050223866295511069447 52471575335799443266604171)
    ·
      refine ⟨78707363003699164899906257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52471575335799443266604171 78707363003699164899906257)
      ·
        refine ⟨59030522252774373674929693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78707363003699164899906257 59030522252774373674929693)
        ·
          refine ⟨22136445844790390128098635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59030522252774373674929693 22136445844790390128098635)
          ·
            refine ⟨33204668767185585192147953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22136445844790390128098635 33204668767185585192147953)
            ·
              refine ⟨24903501575389188894110965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33204668767185585192147953 24903501575389188894110965)
              ·
                refine ⟨2334703272692736458822903, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 24903501575389188894110965 2334703272692736458822903)
                ·
                  refine ⟨3502054909039104688234355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2334703272692736458822903 3502054909039104688234355)
                  ·
                    refine ⟨5253082363558657032351533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3502054909039104688234355 5253082363558657032351533)
                    ·
                      refine ⟨1969905886334496387131825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5253082363558657032351533 1969905886334496387131825)
                      ·
                        rfl

theorem cell23_3836378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 2, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 2, 5, 1, 1, 3].length) (baseStart_3836378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3836378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3836378 prefixEnd_3836378 := by exact prefixLift 3836378
  have htrace : WordTrace (prefixWord ++ tailWord_3836378) baseStart_3836378 baseEnd_3836378 := by
    simpa [prefixWord, tailWord_3836378, baseEnd_3836378] using wordTrace_append hprefix tailTrace_3836378
  have hstable : (prefixWord ++ tailWord_3836378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3836378).length < 2 ^ (prefixWord ++ tailWord_3836378).sum := by decide
  have hdescent : baseEnd_3836378 < baseStart_3836378 := by decide
  rcases family_descends (prefixWord ++ tailWord_3836378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3836422 : List Nat := [6, 2, 1, 1, 1, 2, 1, 1, 1, 5, 2]
def baseStart_3836422 : Nat := 118140960795 + 3836422 * 2 ^ 59
def prefixEnd_3836422 : Nat := 4983230072969 + 3 ^ 40 * 3836422 * 2
def baseEnd_3836422 : Nat := 1969928479483294214981623

theorem tailTrace_3836422 : CollatzResearch.WordTrace tailWord_3836422 prefixEnd_3836422 1969928479483294214981623 := by
  unfold tailWord_3836422
  simp only [CollatzResearch.WordTrace]
  refine ⟨4372681428353305548714985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 93283870471537185039253013 4372681428353305548714985)
  ·
    refine ⟨3279511071264979161536239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4372681428353305548714985 3279511071264979161536239)
    ·
      refine ⟨4919266606897468742304359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3279511071264979161536239 4919266606897468742304359)
      ·
        refine ⟨7378899910346203113456539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4919266606897468742304359 7378899910346203113456539)
        ·
          refine ⟨11068349865519304670184809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7378899910346203113456539 11068349865519304670184809)
          ·
            refine ⟨8301262399139478502638607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11068349865519304670184809 8301262399139478502638607)
            ·
              refine ⟨12451893598709217753957911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8301262399139478502638607 12451893598709217753957911)
              ·
                refine ⟨18677840398063826630936867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12451893598709217753957911 18677840398063826630936867)
                ·
                  refine ⟨28016760597095739946405301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18677840398063826630936867 28016760597095739946405301)
                  ·
                    refine ⟨2626571305977725619975497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 28016760597095739946405301 2626571305977725619975497)
                    ·
                      refine ⟨1969928479483294214981623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2626571305977725619975497 1969928479483294214981623)
                      ·
                        rfl

theorem cell23_3836422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 2, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 2, 1, 1, 1, 5, 2].length) (baseStart_3836422 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3836422 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3836422 prefixEnd_3836422 := by exact prefixLift 3836422
  have htrace : WordTrace (prefixWord ++ tailWord_3836422) baseStart_3836422 baseEnd_3836422 := by
    simpa [prefixWord, tailWord_3836422, baseEnd_3836422] using wordTrace_append hprefix tailTrace_3836422
  have hstable : (prefixWord ++ tailWord_3836422).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3836422).length < 2 ^ (prefixWord ++ tailWord_3836422).sum := by decide
  have hdescent : baseEnd_3836422 < baseStart_3836422 := by decide
  rcases family_descends (prefixWord ++ tailWord_3836422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3836429 : List Nat := [1, 7, 1, 1, 1, 2, 2, 3, 1, 1, 3]
def baseStart_3836429 : Nat := 118140960795 + 3836429 * 2 ^ 59
def prefixEnd_3836429 : Nat := 4983230072969 + 3 ^ 40 * 3836429 * 2
def baseEnd_3836429 : Nat := 1969932073847875687594091

theorem tailTrace_3836429 : CollatzResearch.WordTrace tailWord_3836429 prefixEnd_3836429 1969932073847875687594091 := by
  unfold tailWord_3836429
  simp only [CollatzResearch.WordTrace]
  refine ⟨139926061018280417754384341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93284040678853611836256227 139926061018280417754384341)
  ·
    refine ⟨3279517055115947291118383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 139926061018280417754384341 3279517055115947291118383)
    ·
      refine ⟨4919275582673920936677575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3279517055115947291118383 4919275582673920936677575)
      ·
        refine ⟨7378913374010881405016363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4919275582673920936677575 7378913374010881405016363)
        ·
          refine ⟨11068370061016322107524545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7378913374010881405016363 11068370061016322107524545)
          ·
            refine ⟨8301277545762241580643409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11068370061016322107524545 8301277545762241580643409)
            ·
              refine ⟨6225958159321681185482557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8301277545762241580643409 6225958159321681185482557)
              ·
                refine ⟨2334734309745630444555959, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6225958159321681185482557 2334734309745630444555959)
                ·
                  refine ⟨3502101464618445666833939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2334734309745630444555959 3502101464618445666833939)
                  ·
                    refine ⟨5253152196927668500250909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3502101464618445666833939 5253152196927668500250909)
                    ·
                      refine ⟨1969932073847875687594091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5253152196927668500250909 1969932073847875687594091)
                      ·
                        rfl

theorem cell23_3836429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 2, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 2, 2, 3, 1, 1, 3].length) (baseStart_3836429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3836429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3836429 prefixEnd_3836429 := by exact prefixLift 3836429
  have htrace : WordTrace (prefixWord ++ tailWord_3836429) baseStart_3836429 baseEnd_3836429 := by
    simpa [prefixWord, tailWord_3836429, baseEnd_3836429] using wordTrace_append hprefix tailTrace_3836429
  have hstable : (prefixWord ++ tailWord_3836429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3836429).length < 2 ^ (prefixWord ++ tailWord_3836429).sum := by decide
  have hdescent : baseEnd_3836429 < baseStart_3836429 := by decide
  rcases family_descends (prefixWord ++ tailWord_3836429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3836435 : List Nat := [1, 1, 1, 2, 1, 5, 4, 3, 1, 2, 2]
def baseStart_3836435 : Nat := 118140960795 + 3836435 * 2 ^ 59
def prefixEnd_3836435 : Nat := 4983230072969 + 3 ^ 40 * 3836435 * 2
def baseEnd_3836435 : Nat := 1969935154731802664119063

theorem tailTrace_3836435 : CollatzResearch.WordTrace tailWord_3836435 prefixEnd_3836435 1969935154731802664119063 := by
  unfold tailWord_3836435
  simp only [CollatzResearch.WordTrace]
  refine ⟨139926279856258680779102759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93284186570839120519401839 139926279856258680779102759)
  ·
    refine ⟨209889419784388021168654139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139926279856258680779102759 209889419784388021168654139)
    ·
      refine ⟨314834129676582031752981209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209889419784388021168654139 314834129676582031752981209)
      ·
        refine ⟨236125597257436523814735907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 314834129676582031752981209 236125597257436523814735907)
        ·
          refine ⟨354188395886154785722103861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 236125597257436523814735907 354188395886154785722103861)
          ·
            refine ⟨33205162114327011161447237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 354188395886154785722103861 33205162114327011161447237)
            ·
              refine ⟨6225967896436314592771357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33205162114327011161447237 6225967896436314592771357)
              ·
                refine ⟨2334737961163617972289259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6225967896436314592771357 2334737961163617972289259)
                ·
                  refine ⟨3502106941745426958433889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2334737961163617972289259 3502106941745426958433889)
                  ·
                    refine ⟨2626580206309070218825417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3502106941745426958433889 2626580206309070218825417)
                    ·
                      refine ⟨1969935154731802664119063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2626580206309070218825417 1969935154731802664119063)
                      ·
                        rfl

theorem cell23_3836435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 4, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 4, 3, 1, 2, 2].length) (baseStart_3836435 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3836435 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3836435 prefixEnd_3836435 := by exact prefixLift 3836435
  have htrace : WordTrace (prefixWord ++ tailWord_3836435) baseStart_3836435 baseEnd_3836435 := by
    simpa [prefixWord, tailWord_3836435, baseEnd_3836435] using wordTrace_append hprefix tailTrace_3836435
  have hstable : (prefixWord ++ tailWord_3836435).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3836435).length < 2 ^ (prefixWord ++ tailWord_3836435).sum := by decide
  have hdescent : baseEnd_3836435 < baseStart_3836435 := by decide
  rcases family_descends (prefixWord ++ tailWord_3836435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3836452 : List Nat := [2, 3, 1, 5, 1, 1, 2, 1, 3, 2, 2]
def baseStart_3836452 : Nat := 118140960795 + 3836452 * 2 ^ 59
def prefixEnd_3836452 : Nat := 4983230072969 + 3 ^ 40 * 3836452 * 2
def baseEnd_3836452 : Nat := 1969943883902929097606485

theorem tailTrace_3836452 : CollatzResearch.WordTrace tailWord_3836452 prefixEnd_3836452 1969943883902929097606485 := by
  unfold tailWord_3836452
  simp only [CollatzResearch.WordTrace]
  refine ⟨69963449948598546341235805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93284599931464728454981073 69963449948598546341235805)
  ·
    refine ⟨26236293730724454877963427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69963449948598546341235805 26236293730724454877963427)
    ·
      refine ⟨39354440596086682316945141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26236293730724454877963427 39354440596086682316945141)
      ·
        refine ⟨3689478805883126467213607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 39354440596086682316945141 3689478805883126467213607)
        ·
          refine ⟨5534218208824689700820411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3689478805883126467213607 5534218208824689700820411)
          ·
            refine ⟨8301327313237034551230617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5534218208824689700820411 8301327313237034551230617)
            ·
              refine ⟨6225995484927775913422963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8301327313237034551230617 6225995484927775913422963)
              ·
                refine ⟨9338993227391663870134445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6225995484927775913422963 9338993227391663870134445)
                ·
                  refine ⟨3502122460271873951300417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9338993227391663870134445 3502122460271873951300417)
                  ·
                    refine ⟨2626591845203905463475313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3502122460271873951300417 2626591845203905463475313)
                    ·
                      refine ⟨1969943883902929097606485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2626591845203905463475313 1969943883902929097606485)
                      ·
                        rfl

theorem cell23_3836452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 1, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 1, 2, 1, 3, 2, 2].length) (baseStart_3836452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3836452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3836452 prefixEnd_3836452 := by exact prefixLift 3836452
  have htrace : WordTrace (prefixWord ++ tailWord_3836452) baseStart_3836452 baseEnd_3836452 := by
    simpa [prefixWord, tailWord_3836452, baseEnd_3836452] using wordTrace_append hprefix tailTrace_3836452
  have hstable : (prefixWord ++ tailWord_3836452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3836452).length < 2 ^ (prefixWord ++ tailWord_3836452).sum := by decide
  have hdescent : baseEnd_3836452 < baseStart_3836452 := by decide
  rcases family_descends (prefixWord ++ tailWord_3836452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3836486 : List Nat := [6, 1, 1, 1, 2, 3, 1, 3, 1, 2, 2]
def baseStart_3836486 : Nat := 118140960795 + 3836486 * 2 ^ 59
def prefixEnd_3836486 : Nat := 4983230072969 + 3 ^ 40 * 3836486 * 2
def baseEnd_3836486 : Nat := 1969961342245181964581329

theorem tailTrace_3836486 : CollatzResearch.WordTrace tailWord_3836486 prefixEnd_3836486 1969961342245181964581329 := by
  unfold tailWord_3836486
  simp only [CollatzResearch.WordTrace]
  refine ⟨4372754374346059890287791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 93285426652715944326139541 4372754374346059890287791)
  ·
    refine ⟨6559131561519089835431687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4372754374346059890287791 6559131561519089835431687)
    ·
      refine ⟨9838697342278634753147531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6559131561519089835431687 9838697342278634753147531)
      ·
        refine ⟨14758046013417952129721297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9838697342278634753147531 14758046013417952129721297)
        ·
          refine ⟨11068534510063464097290973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14758046013417952129721297 11068534510063464097290973)
          ·
            refine ⟨4150700441273799036484115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11068534510063464097290973 4150700441273799036484115)
            ·
              refine ⟨6226050661910698554726173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4150700441273799036484115 6226050661910698554726173)
              ·
                refine ⟨2334768998216511958022315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6226050661910698554726173 2334768998216511958022315)
                ·
                  refine ⟨3502153497324767937033473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2334768998216511958022315 3502153497324767937033473)
                  ·
                    refine ⟨2626615122993575952775105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3502153497324767937033473 2626615122993575952775105)
                    ·
                      refine ⟨1969961342245181964581329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2626615122993575952775105 1969961342245181964581329)
                      ·
                        rfl

theorem cell23_3836486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 3, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 3, 1, 3, 1, 2, 2].length) (baseStart_3836486 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3836486 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3836486 prefixEnd_3836486 := by exact prefixLift 3836486
  have htrace : WordTrace (prefixWord ++ tailWord_3836486) baseStart_3836486 baseEnd_3836486 := by
    simpa [prefixWord, tailWord_3836486, baseEnd_3836486] using wordTrace_append hprefix tailTrace_3836486
  have hstable : (prefixWord ++ tailWord_3836486).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3836486).length < 2 ^ (prefixWord ++ tailWord_3836486).sum := by decide
  have hdescent : baseEnd_3836486 < baseStart_3836486 := by decide
  rcases family_descends (prefixWord ++ tailWord_3836486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3836491 : List Nat := [1, 1, 1, 1, 3, 1, 4, 4, 1, 4, 2]
def baseStart_3836491 : Nat := 118140960795 + 3836491 * 2 ^ 59
def prefixEnd_3836491 : Nat := 4983230072969 + 3 ^ 40 * 3836491 * 2
def baseEnd_3836491 : Nat := 1969963909648454445018805

theorem tailTrace_3836491 : CollatzResearch.WordTrace tailWord_3836491 prefixEnd_3836491 1969963909648454445018805 := by
  unfold tailWord_3836491
  simp only [CollatzResearch.WordTrace]
  refine ⟨139928322344055802343141327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93285548229370534895427551 139928322344055802343141327)
  ·
    refine ⟨209892483516083703514711991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139928322344055802343141327 209892483516083703514711991)
    ·
      refine ⟨314838725274125555272067987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209892483516083703514711991 314838725274125555272067987)
      ·
        refine ⟨472258087911188332908101981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 314838725274125555272067987 472258087911188332908101981)
        ·
          refine ⟨177096782966695624840538243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 472258087911188332908101981 177096782966695624840538243)
          ·
            refine ⟨265645174450043437260807365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 177096782966695624840538243 265645174450043437260807365)
            ·
              refine ⟨49808470209383144486401381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 265645174450043437260807365 49808470209383144486401381)
              ·
                refine ⟨9339088164259339591200259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 49808470209383144486401381 9339088164259339591200259)
                ·
                  refine ⟨14008632246389009386800389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9339088164259339591200259 14008632246389009386800389)
                  ·
                    refine ⟨2626618546197939260025073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14008632246389009386800389 2626618546197939260025073)
                    ·
                      refine ⟨1969963909648454445018805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2626618546197939260025073 1969963909648454445018805)
                      ·
                        rfl

theorem cell23_3836491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 4, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 4, 4, 1, 4, 2].length) (baseStart_3836491 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3836491 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3836491 prefixEnd_3836491 := by exact prefixLift 3836491
  have htrace : WordTrace (prefixWord ++ tailWord_3836491) baseStart_3836491 baseEnd_3836491 := by
    simpa [prefixWord, tailWord_3836491, baseEnd_3836491] using wordTrace_append hprefix tailTrace_3836491
  have hstable : (prefixWord ++ tailWord_3836491).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3836491).length < 2 ^ (prefixWord ++ tailWord_3836491).sum := by decide
  have hdescent : baseEnd_3836491 < baseStart_3836491 := by decide
  rcases family_descends (prefixWord ++ tailWord_3836491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3836494 : List Nat := [4, 1, 1, 1, 1, 2, 3, 1, 1, 3, 5]
def baseStart_3836494 : Nat := 118140960795 + 3836494 * 2 ^ 59
def prefixEnd_3836494 : Nat := 4983230072969 + 3 ^ 40 * 3836494 * 2
def baseEnd_3836494 : Nat := 1969965450090417933281291

theorem tailTrace_3836494 : CollatzResearch.WordTrace tailWord_3836494 prefixEnd_3836494 1969965450090417933281291 := by
  unfold tailWord_3836494
  simp only [CollatzResearch.WordTrace]
  refine ⟨17491053970380616731937567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 93285621175363289237000357 17491053970380616731937567)
  ·
    refine ⟨26236580955570925097906351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17491053970380616731937567 26236580955570925097906351)
    ·
      refine ⟨39354871433356387646859527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26236580955570925097906351 39354871433356387646859527)
      ·
        refine ⟨59032307150034581470289291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39354871433356387646859527 59032307150034581470289291)
        ·
          refine ⟨88548460725051872205433937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59032307150034581470289291 88548460725051872205433937)
          ·
            refine ⟨66411345543788904154075453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 88548460725051872205433937 66411345543788904154075453)
            ·
              refine ⟨24904254578920839057778295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 66411345543788904154075453 24904254578920839057778295)
              ·
                refine ⟨37356381868381258586667443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24904254578920839057778295 37356381868381258586667443)
                ·
                  refine ⟨56034572802571887880001165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37356381868381258586667443 56034572802571887880001165)
                  ·
                    refine ⟨21012964800964457955000437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 56034572802571887880001165 21012964800964457955000437)
                    ·
                      refine ⟨1969965450090417933281291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21012964800964457955000437 1969965450090417933281291)
                      ·
                        rfl

theorem cell23_3836494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 3, 1, 1, 3, 5].length) (baseStart_3836494 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3836494 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3836494 prefixEnd_3836494 := by exact prefixLift 3836494
  have htrace : WordTrace (prefixWord ++ tailWord_3836494) baseStart_3836494 baseEnd_3836494 := by
    simpa [prefixWord, tailWord_3836494, baseEnd_3836494] using wordTrace_append hprefix tailTrace_3836494
  have hstable : (prefixWord ++ tailWord_3836494).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3836494).length < 2 ^ (prefixWord ++ tailWord_3836494).sum := by decide
  have hdescent : baseEnd_3836494 < baseStart_3836494 := by decide
  rcases family_descends (prefixWord ++ tailWord_3836494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3836504 : List Nat := [2, 1, 2, 2, 1, 2, 2, 1, 4, 2, 4]
def baseStart_3836504 : Nat := 118140960795 + 3836504 * 2 ^ 59
def prefixEnd_3836504 : Nat := 4983230072969 + 3 ^ 40 * 3836504 * 2
def baseEnd_3836504 : Nat := 1969970584896962894156245

theorem tailTrace_3836504 : CollatzResearch.WordTrace tailWord_3836504 prefixEnd_3836504 1969970584896962894156245 := by
  unfold tailWord_3836504
  simp only [CollatzResearch.WordTrace]
  refine ⟨69964398246504352781682283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93285864328672470375576377 69964398246504352781682283)
  ·
    refine ⟨104946597369756529172523425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69964398246504352781682283 104946597369756529172523425)
    ·
      refine ⟨78709948027317396879392569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104946597369756529172523425 78709948027317396879392569)
      ·
        refine ⟨59032461020488047659544427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78709948027317396879392569 59032461020488047659544427)
        ·
          refine ⟨88548691530732071489316641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59032461020488047659544427 88548691530732071489316641)
          ·
            refine ⟨66411518648049053616987481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 88548691530732071489316641 66411518648049053616987481)
            ·
              refine ⟨49808638986036790212740611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66411518648049053616987481 49808638986036790212740611)
              ·
                refine ⟨74712958479055185319110917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49808638986036790212740611 74712958479055185319110917)
                ·
                  refine ⟨14008679714822847247333297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 74712958479055185319110917 14008679714822847247333297)
                  ·
                    refine ⟨10506509786117135435499973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14008679714822847247333297 10506509786117135435499973)
                    ·
                      refine ⟨1969970584896962894156245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10506509786117135435499973 1969970584896962894156245)
                      ·
                        rfl

theorem cell23_3836504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 2, 1, 4, 2, 4].length) (baseStart_3836504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3836504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3836504 prefixEnd_3836504 := by exact prefixLift 3836504
  have htrace : WordTrace (prefixWord ++ tailWord_3836504) baseStart_3836504 baseEnd_3836504 := by
    simpa [prefixWord, tailWord_3836504, baseEnd_3836504] using wordTrace_append hprefix tailTrace_3836504
  have hstable : (prefixWord ++ tailWord_3836504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3836504).length < 2 ^ (prefixWord ++ tailWord_3836504).sum := by decide
  have hdescent : baseEnd_3836504 < baseStart_3836504 := by decide
  rcases family_descends (prefixWord ++ tailWord_3836504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3836591 : List Nat := [1, 1, 2, 1, 2, 5, 1, 1, 5, 4]
def baseStart_3836591 : Nat := 118140960795 + 3836591 * 2 ^ 59
def prefixEnd_3836591 : Nat := 4983230072969 + 3 ^ 40 * 3836591 * 2
def baseEnd_3836591 : Nat := 656671752571301351256115

theorem tailTrace_3836591 : CollatzResearch.WordTrace tailWord_3836591 prefixEnd_3836591 656671752571301351256115 := by
  unfold tailWord_3836591
  simp only [CollatzResearch.WordTrace]
  refine ⟨139931969643693519421781627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93287979762462346281187751 139931969643693519421781627)
  ·
    refine ⟨209897954465540279132672441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139931969643693519421781627 209897954465540279132672441)
    ·
      refine ⟨157423465849155209349504331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 209897954465540279132672441 157423465849155209349504331)
      ·
        refine ⟨236135198773732814024256497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157423465849155209349504331 236135198773732814024256497)
        ·
          refine ⟨177101399080299610518192373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 236135198773732814024256497 177101399080299610518192373)
          ·
            refine ⟨16603256163778088486080535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 177101399080299610518192373 16603256163778088486080535)
            ·
              refine ⟨24904884245667132729120803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16603256163778088486080535 24904884245667132729120803)
              ·
                refine ⟨37357326368500699093681205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24904884245667132729120803 37357326368500699093681205)
                ·
                  refine ⟨3502249347046940540032613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 37357326368500699093681205 3502249347046940540032613)
                  ·
                    refine ⟨656671752571301351256115, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3502249347046940540032613 656671752571301351256115)
                    ·
                      rfl

theorem cell23_3836591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 1, 1, 5, 4].length) (baseStart_3836591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3836591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3836591 prefixEnd_3836591 := by exact prefixLift 3836591
  have htrace : WordTrace (prefixWord ++ tailWord_3836591) baseStart_3836591 baseEnd_3836591 := by
    simpa [prefixWord, tailWord_3836591, baseEnd_3836591] using wordTrace_append hprefix tailTrace_3836591
  have hstable : (prefixWord ++ tailWord_3836591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3836591).length < 2 ^ (prefixWord ++ tailWord_3836591).sum := by decide
  have hdescent : baseEnd_3836591 < baseStart_3836591 := by decide
  rcases family_descends (prefixWord ++ tailWord_3836591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3836668 : List Nat := [2, 2, 2, 1, 3, 2, 2, 3, 1, 5]
def baseStart_3836668 : Nat := 118140960795 + 3836668 * 2 ^ 59
def prefixEnd_3836668 : Nat := 4983230072969 + 3 ^ 40 * 3836668 * 2
def baseEnd_3836668 : Nat := 656684931908100084168497

theorem tailTrace_3836668 : CollatzResearch.WordTrace tailWord_3836668 prefixEnd_3836668 656684931908100084168497 := by
  unfold tailWord_3836668
  simp only [CollatzResearch.WordTrace]
  refine ⟨69967389032207280786167329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93289852042943041048223105 69967389032207280786167329)
  ·
    refine ⟨52475541774155460589625497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69967389032207280786167329 52475541774155460589625497)
    ·
      refine ⟨39356656330616595442219123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52475541774155460589625497 39356656330616595442219123)
      ·
        refine ⟨59034984495924893163328685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39356656330616595442219123 59034984495924893163328685)
        ·
          refine ⟨22138119185971834936248257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59034984495924893163328685 22138119185971834936248257)
          ·
            refine ⟨16603589389478876202186193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22138119185971834936248257 16603589389478876202186193)
            ·
              refine ⟨12452692042109157151639645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16603589389478876202186193 12452692042109157151639645)
              ·
                refine ⟨4669759515790933931864867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12452692042109157151639645 4669759515790933931864867)
                ·
                  refine ⟨7004639273686400897797301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4669759515790933931864867 7004639273686400897797301)
                  ·
                    refine ⟨656684931908100084168497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7004639273686400897797301 656684931908100084168497)
                    ·
                      rfl

theorem cell23_3836668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 2, 3, 1, 5].length) (baseStart_3836668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3836668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3836668 prefixEnd_3836668 := by exact prefixLift 3836668
  have htrace : WordTrace (prefixWord ++ tailWord_3836668) baseStart_3836668 baseEnd_3836668 := by
    simpa [prefixWord, tailWord_3836668, baseEnd_3836668] using wordTrace_append hprefix tailTrace_3836668
  have hstable : (prefixWord ++ tailWord_3836668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3836668).length < 2 ^ (prefixWord ++ tailWord_3836668).sum := by decide
  have hdescent : baseEnd_3836668 < baseStart_3836668 := by decide
  rcases family_descends (prefixWord ++ tailWord_3836668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3836671 : List Nat := [1, 1, 2, 2, 1, 3, 1, 2, 5, 1, 4]
def baseStart_3836671 : Nat := 118140960795 + 3836671 * 2 ^ 59
def prefixEnd_3836671 : Nat := 4983230072969 + 3 ^ 40 * 3836671 * 2
def baseEnd_3836671 : Nat := 1970056336166263740767977

theorem tailTrace_3836671 : CollatzResearch.WordTrace tailWord_3836671 prefixEnd_3836671 1970056336166263740767977 := by
  unfold tailWord_3836671
  simp only [CollatzResearch.WordTrace]
  refine ⟨139934887483403693084693867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93289924988935795389795911 139934887483403693084693867)
  ·
    refine ⟨209902331225105539627040801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139934887483403693084693867 209902331225105539627040801)
    ·
      refine ⟨157426748418829154720280601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 209902331225105539627040801 157426748418829154720280601)
      ·
        refine ⟨118070061314121866040210451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 157426748418829154720280601 118070061314121866040210451)
        ·
          refine ⟨177105091971182799060315677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118070061314121866040210451 177105091971182799060315677)
          ·
            refine ⟨66414409489193549647618379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 177105091971182799060315677 66414409489193549647618379)
            ·
              refine ⟨99621614233790324471427569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66414409489193549647618379 99621614233790324471427569)
              ·
                refine ⟨74716210675342743353570677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 99621614233790324471427569 74716210675342743353570677)
                ·
                  refine ⟨7004644750813382189397251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 74716210675342743353570677 7004644750813382189397251)
                  ·
                    refine ⟨10506967126220073284095877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7004644750813382189397251 10506967126220073284095877)
                    ·
                      refine ⟨1970056336166263740767977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10506967126220073284095877 1970056336166263740767977)
                      ·
                        rfl

theorem cell23_3836671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 2, 5, 1, 4].length) (baseStart_3836671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3836671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3836671 prefixEnd_3836671 := by exact prefixLift 3836671
  have htrace : WordTrace (prefixWord ++ tailWord_3836671) baseStart_3836671 baseEnd_3836671 := by
    simpa [prefixWord, tailWord_3836671, baseEnd_3836671] using wordTrace_append hprefix tailTrace_3836671
  have hstable : (prefixWord ++ tailWord_3836671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3836671).length < 2 ^ (prefixWord ++ tailWord_3836671).sum := by decide
  have hdescent : baseEnd_3836671 < baseStart_3836671 := by decide
  rcases family_descends (prefixWord ++ tailWord_3836671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3836691 : List Nat := [1, 1, 1, 2, 1, 3, 3, 4, 1, 1, 5]
def baseStart_3836691 : Nat := 118140960795 + 3836691 * 2 ^ 59
def prefixEnd_3836691 : Nat := 4983230072969 + 3 ^ 40 * 3836691 * 2
def baseEnd_3836691 : Nat := 1970066605779353662517885

theorem tailTrace_3836691 : CollatzResearch.WordTrace tailWord_3836691 prefixEnd_3836691 1970066605779353662517885 := by
  unfold tailWord_3836691
  simp only [CollatzResearch.WordTrace]
  refine ⟨139935616943331236500421927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93290411295554157666947951 139935616943331236500421927)
  ·
    refine ⟨209903425414996854750632891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139935616943331236500421927 209903425414996854750632891)
    ·
      refine ⟨314855138122495282125949337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209903425414996854750632891 314855138122495282125949337)
      ·
        refine ⟨236141353591871461594462003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 314855138122495282125949337 236141353591871461594462003)
        ·
          refine ⟨354212030387807192391693005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 236141353591871461594462003 354212030387807192391693005)
          ·
            refine ⟨132829511395427697146884877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 354212030387807192391693005 132829511395427697146884877)
            ·
              refine ⟨49811066773285386430081829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 132829511395427697146884877 49811066773285386430081829)
              ·
                refine ⟨9339575019991009955640343, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 49811066773285386430081829 9339575019991009955640343)
                ·
                  refine ⟨14009362529986514933460515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9339575019991009955640343 14009362529986514933460515)
                  ·
                    refine ⟨21014043794979772400190773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14009362529986514933460515 21014043794979772400190773)
                    ·
                      refine ⟨1970066605779353662517885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21014043794979772400190773 1970066605779353662517885)
                      ·
                        rfl

theorem cell23_3836691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 3, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 3, 4, 1, 1, 5].length) (baseStart_3836691 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3836691 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3836691 prefixEnd_3836691 := by exact prefixLift 3836691
  have htrace : WordTrace (prefixWord ++ tailWord_3836691) baseStart_3836691 baseEnd_3836691 := by
    simpa [prefixWord, tailWord_3836691, baseEnd_3836691] using wordTrace_append hprefix tailTrace_3836691
  have hstable : (prefixWord ++ tailWord_3836691).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3836691).length < 2 ^ (prefixWord ++ tailWord_3836691).sum := by decide
  have hdescent : baseEnd_3836691 < baseStart_3836691 := by decide
  rcases family_descends (prefixWord ++ tailWord_3836691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3836705 : List Nat := [1, 2, 3, 2, 1, 2, 2, 1, 5, 2, 2]
def baseStart_3836705 : Nat := 118140960795 + 3836705 * 2 ^ 59
def prefixEnd_3836705 : Nat := 4983230072969 + 3 ^ 40 * 3836705 * 2
def baseEnd_3836705 : Nat := 1970073794508516607742821

theorem tailTrace_3836705 : CollatzResearch.WordTrace tailWord_3836705 prefixEnd_3836705 1970073794508516607742821 := by
  unfold tailWord_3836705
  simp only [CollatzResearch.WordTrace]
  refine ⟨139936127565280516891431569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93290751710187011260954379 139936127565280516891431569)
  ·
    refine ⟨104952095673960387668573677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139936127565280516891431569 104952095673960387668573677)
    ·
      refine ⟨39357035877735145375715129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 104952095673960387668573677 39357035877735145375715129)
      ·
        refine ⟨29517776908301359031786347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39357035877735145375715129 29517776908301359031786347)
        ·
          refine ⟨44276665362452038547679521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29517776908301359031786347 44276665362452038547679521)
          ·
            refine ⟨33207499021839028910759641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44276665362452038547679521 33207499021839028910759641)
            ·
              refine ⟨24905624266379271683069731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33207499021839028910759641 24905624266379271683069731)
              ·
                refine ⟨37358436399568907524604597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24905624266379271683069731 37358436399568907524604597)
                ·
                  refine ⟨3502353412459585080431681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 37358436399568907524604597 3502353412459585080431681)
                  ·
                    refine ⟨2626765059344688810323761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3502353412459585080431681 2626765059344688810323761)
                    ·
                      refine ⟨1970073794508516607742821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2626765059344688810323761 1970073794508516607742821)
                      ·
                        rfl

theorem cell23_3836705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 2, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 2, 1, 5, 2, 2].length) (baseStart_3836705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3836705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3836705 prefixEnd_3836705 := by exact prefixLift 3836705
  have htrace : WordTrace (prefixWord ++ tailWord_3836705) baseStart_3836705 baseEnd_3836705 := by
    simpa [prefixWord, tailWord_3836705, baseEnd_3836705] using wordTrace_append hprefix tailTrace_3836705
  have hstable : (prefixWord ++ tailWord_3836705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3836705).length < 2 ^ (prefixWord ++ tailWord_3836705).sum := by decide
  have hdescent : baseEnd_3836705 < baseStart_3836705 := by decide
  rcases family_descends (prefixWord ++ tailWord_3836705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3836725 : List Nat := [1, 3, 3, 1, 3, 3, 1, 1, 1, 1, 5]
def baseStart_3836725 : Nat := 118140960795 + 3836725 * 2 ^ 59
def prefixEnd_3836725 : Nat := 4983230072969 + 3 ^ 40 * 3836725 * 2
def baseEnd_3836725 : Nat := 1970084064121606529492729

theorem tailTrace_3836725 : CollatzResearch.WordTrace tailWord_3836725 prefixEnd_3836725 1970084064121606529492729 := by
  unfold tailWord_3836725
  simp only [CollatzResearch.WordTrace]
  refine ⟨139936857025208060307159629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93291238016805373538106419 139936857025208060307159629)
  ·
    refine ⟨52476321384453022615184861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 139936857025208060307159629 52476321384453022615184861)
    ·
      refine ⟨19678620519169883480694323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52476321384453022615184861 19678620519169883480694323)
      ·
        refine ⟨29517930778754825221041485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19678620519169883480694323 29517930778754825221041485)
        ·
          refine ⟨11069224042033059457890557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29517930778754825221041485 11069224042033059457890557)
          ·
            refine ⟨4150959015762397296708959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11069224042033059457890557 4150959015762397296708959)
            ·
              refine ⟨6226438523643595945063439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4150959015762397296708959 6226438523643595945063439)
              ·
                refine ⟨9339657785465393917595159, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6226438523643595945063439 9339657785465393917595159)
                ·
                  refine ⟨14009486678198090876392739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9339657785465393917595159 14009486678198090876392739)
                  ·
                    refine ⟨21014230017297136314589109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14009486678198090876392739 21014230017297136314589109)
                    ·
                      refine ⟨1970084064121606529492729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21014230017297136314589109 1970084064121606529492729)
                      ·
                        rfl

theorem cell23_3836725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 3, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 3, 1, 1, 1, 1, 5].length) (baseStart_3836725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3836725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3836725 prefixEnd_3836725 := by exact prefixLift 3836725
  have htrace : WordTrace (prefixWord ++ tailWord_3836725) baseStart_3836725 baseEnd_3836725 := by
    simpa [prefixWord, tailWord_3836725, baseEnd_3836725] using wordTrace_append hprefix tailTrace_3836725
  have hstable : (prefixWord ++ tailWord_3836725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3836725).length < 2 ^ (prefixWord ++ tailWord_3836725).sum := by decide
  have hdescent : baseEnd_3836725 < baseStart_3836725 := by decide
  rcases family_descends (prefixWord ++ tailWord_3836725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3836733 : List Nat := [1, 4, 1, 4, 3, 1, 2, 2, 1, 1, 3]
def baseStart_3836733 : Nat := 118140960795 + 3836733 * 2 ^ 59
def prefixEnd_3836733 : Nat := 4983230072969 + 3 ^ 40 * 3836733 * 2
def baseEnd_3836733 : Nat := 1970088171966842498192693

theorem tailTrace_3836733 : CollatzResearch.WordTrace tailWord_3836733 prefixEnd_3836733 1970088171966842498192693 := by
  unfold tailWord_3836733
  simp only [CollatzResearch.WordTrace]
  refine ⟨139937148809179077673450853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93291432539452718448967235 139937148809179077673450853)
  ·
    refine ⟨26238215401721077063772035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 139937148809179077673450853 26238215401721077063772035)
    ·
      refine ⟨39357323102581615595658053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26238215401721077063772035 39357323102581615595658053)
      ·
        refine ⟨7379498081734052924185885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 39357323102581615595658053 7379498081734052924185885)
        ·
          refine ⟨2767311780650269846569707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7379498081734052924185885 2767311780650269846569707)
          ·
            refine ⟨4150967670975404769854561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2767311780650269846569707 4150967670975404769854561)
            ·
              refine ⟨3113225753231553577390921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4150967670975404769854561 3113225753231553577390921)
              ·
                refine ⟨2334919314923665183043191, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3113225753231553577390921 2334919314923665183043191)
                ·
                  refine ⟨3502378972385497774564787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2334919314923665183043191 3502378972385497774564787)
                  ·
                    refine ⟨5253568458578246661847181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3502378972385497774564787 5253568458578246661847181)
                    ·
                      refine ⟨1970088171966842498192693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5253568458578246661847181 1970088171966842498192693)
                      ·
                        rfl

theorem cell23_3836733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 3, 1, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 3, 1, 2, 2, 1, 1, 3].length) (baseStart_3836733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3836733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3836733 prefixEnd_3836733 := by exact prefixLift 3836733
  have htrace : WordTrace (prefixWord ++ tailWord_3836733) baseStart_3836733 baseEnd_3836733 := by
    simpa [prefixWord, tailWord_3836733, baseEnd_3836733] using wordTrace_append hprefix tailTrace_3836733
  have hstable : (prefixWord ++ tailWord_3836733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3836733).length < 2 ^ (prefixWord ++ tailWord_3836733).sum := by decide
  have hdescent : baseEnd_3836733 < baseStart_3836733 := by decide
  rcases family_descends (prefixWord ++ tailWord_3836733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3836789 : List Nat := [1, 3, 4, 1, 1, 4, 1, 2, 2, 1, 3]
def baseStart_3836789 : Nat := 118140960795 + 3836789 * 2 ^ 59
def prefixEnd_3836789 : Nat := 4983230072969 + 3 ^ 40 * 3836789 * 2
def baseEnd_3836789 : Nat := 1970116926883494279092435

theorem tailTrace_3836789 : CollatzResearch.WordTrace tailWord_3836789 prefixEnd_3836789 1970116926883494279092435 := by
  unfold tailWord_3836789
  simp only [CollatzResearch.WordTrace]
  refine ⟨139939191296976199237489421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93292794197984132824992947 139939191296976199237489421)
  ·
    refine ⟨52477196736366074714058533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 139939191296976199237489421 52477196736366074714058533)
    ·
      refine ⟨9839474388068639008885975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 52477196736366074714058533 9839474388068639008885975)
      ·
        refine ⟨14759211582102958513328963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9839474388068639008885975 14759211582102958513328963)
        ·
          refine ⟨22138817373154437769993445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14759211582102958513328963 22138817373154437769993445)
          ·
            refine ⟨4151028257466457081873771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22138817373154437769993445 4151028257466457081873771)
            ·
              refine ⟨6226542386199685622810657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4151028257466457081873771 6226542386199685622810657)
              ·
                refine ⟨4669906789649764217107993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6226542386199685622810657 4669906789649764217107993)
                ·
                  refine ⟨3502430092237323162830995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4669906789649764217107993 3502430092237323162830995)
                  ·
                    refine ⟨5253645138355984744246493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3502430092237323162830995 5253645138355984744246493)
                    ·
                      refine ⟨1970116926883494279092435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5253645138355984744246493 1970116926883494279092435)
                      ·
                        rfl

theorem cell23_3836789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 4, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 4, 1, 2, 2, 1, 3].length) (baseStart_3836789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3836789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3836789 prefixEnd_3836789 := by exact prefixLift 3836789
  have htrace : WordTrace (prefixWord ++ tailWord_3836789) baseStart_3836789 baseEnd_3836789 := by
    simpa [prefixWord, tailWord_3836789, baseEnd_3836789] using wordTrace_append hprefix tailTrace_3836789
  have hstable : (prefixWord ++ tailWord_3836789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3836789).length < 2 ^ (prefixWord ++ tailWord_3836789).sum := by decide
  have hdescent : baseEnd_3836789 < baseStart_3836789 := by decide
  rcases family_descends (prefixWord ++ tailWord_3836789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3836812 : List Nat := [2, 2, 1, 2, 1, 2, 2, 5, 2, 2, 2]
def baseStart_3836812 : Nat := 118140960795 + 3836812 * 2 ^ 59
def prefixEnd_3836812 : Nat := 4983230072969 + 3 ^ 40 * 3836812 * 2
def baseEnd_3836812 : Nat := 1970128736938547689104829

theorem tailTrace_3836812 : CollatzResearch.WordTrace tailWord_3836812 prefixEnd_3836812 1970128736938547689104829 := by
  unfold tailWord_3836812
  simp only [CollatzResearch.WordTrace]
  refine ⟨69970015087946437082788345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93293353450595249443717793 69970015087946437082788345)
  ·
    refine ⟨52477511315959827812091259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69970015087946437082788345 52477511315959827812091259)
    ·
      refine ⟨78716266973939741718136889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52477511315959827812091259 78716266973939741718136889)
      ·
        refine ⟨59037200230454806288602667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78716266973939741718136889 59037200230454806288602667)
        ·
          refine ⟨88555800345682209432904001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59037200230454806288602667 88555800345682209432904001)
          ·
            refine ⟨66416850259261657074678001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 88555800345682209432904001 66416850259261657074678001)
            ·
              refine ⟨49812637694446242806008501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66416850259261657074678001 49812637694446242806008501)
              ·
                refine ⟨4669934783854335263063297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 49812637694446242806008501 4669934783854335263063297)
                ·
                  refine ⟨3502451087890751447297473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4669934783854335263063297 3502451087890751447297473)
                  ·
                    refine ⟨2626838315918063585473105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3502451087890751447297473 2626838315918063585473105)
                    ·
                      refine ⟨1970128736938547689104829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2626838315918063585473105 1970128736938547689104829)
                      ·
                        rfl

theorem cell23_3836812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 2, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 2, 5, 2, 2, 2].length) (baseStart_3836812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3836812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3836812 prefixEnd_3836812 := by exact prefixLift 3836812
  have htrace : WordTrace (prefixWord ++ tailWord_3836812) baseStart_3836812 baseEnd_3836812 := by
    simpa [prefixWord, tailWord_3836812, baseEnd_3836812] using wordTrace_append hprefix tailTrace_3836812
  have hstable : (prefixWord ++ tailWord_3836812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3836812).length < 2 ^ (prefixWord ++ tailWord_3836812).sum := by decide
  have hdescent : baseEnd_3836812 < baseStart_3836812 := by decide
  rcases family_descends (prefixWord ++ tailWord_3836812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3836835 : List Nat := [1, 1, 1, 4, 1, 2, 5, 3, 5]
def baseStart_3836835 : Nat := 118140960795 + 3836835 * 2 ^ 59
def prefixEnd_3836835 : Nat := 4983230072969 + 3 ^ 40 * 3836835 * 2
def baseEnd_3836835 : Nat := 218904505221511233235247

theorem tailTrace_3836835 : CollatzResearch.WordTrace tailWord_3836835 prefixEnd_3836835 218904505221511233235247 := by
  unfold tailWord_3836835
  simp only [CollatzResearch.WordTrace]
  refine ⟨139940869054809549093663959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93293912703206366062442639 139940869054809549093663959)
  ·
    refine ⟨209911303582214323640495939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139940869054809549093663959 209911303582214323640495939)
    ·
      refine ⟨314866955373321485460743909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209911303582214323640495939 314866955373321485460743909)
      ·
        refine ⟨59037554132497778523889483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 314866955373321485460743909 59037554132497778523889483)
        ·
          refine ⟨88556331198746667785834225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59037554132497778523889483 88556331198746667785834225)
          ·
            refine ⟨66417248399060000839375669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 88556331198746667785834225 66417248399060000839375669)
            ·
              refine ⟨6226617037411875078691469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 66417248399060000839375669 6226617037411875078691469)
              ·
                refine ⟨2334981389029453154509301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6226617037411875078691469 2334981389029453154509301)
                ·
                  refine ⟨218904505221511233235247, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2334981389029453154509301 218904505221511233235247)
                  ·
                    rfl

theorem cell23_3836835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 5, 3, 5].length) (baseStart_3836835 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3836835 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3836835 prefixEnd_3836835 := by exact prefixLift 3836835
  have htrace : WordTrace (prefixWord ++ tailWord_3836835) baseStart_3836835 baseEnd_3836835 := by
    simpa [prefixWord, tailWord_3836835, baseEnd_3836835] using wordTrace_append hprefix tailTrace_3836835
  have hstable : (prefixWord ++ tailWord_3836835).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3836835).length < 2 ^ (prefixWord ++ tailWord_3836835).sum := by decide
  have hdescent : baseEnd_3836835 < baseStart_3836835 := by decide
  rcases family_descends (prefixWord ++ tailWord_3836835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
