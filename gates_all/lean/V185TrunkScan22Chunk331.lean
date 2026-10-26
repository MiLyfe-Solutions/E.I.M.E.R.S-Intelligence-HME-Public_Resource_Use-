import V185TrunkScan22Chunk330

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_2953221 : List Nat := [1, 3, 1, 1, 2, 4, 1, 9]
def baseStart_2953221 : Nat := 118140960795 + 2953221 * 2 ^ 59
def prefixEnd_2953221 : Nat := 4983230072969 + 3 ^ 40 * 2953221 * 2
def baseEnd_2953221 : Nat := 112327544589014462441177

theorem tailTrace_2953221 : CollatzResearch.WordTrace tailWord_2953221 prefixEnd_2953221 112327544589014462441177 := by
  unfold tailWord_2953221
  simp only [CollatzResearch.WordTrace]
  refine ⟨107712818833992161836963517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71808545889328107891309011 107712818833992161836963517)
  ·
    refine ⟨40392307062747060688861319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 107712818833992161836963517 40392307062747060688861319)
    ·
      refine ⟨60588460594120591033291979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40392307062747060688861319 60588460594120591033291979)
      ·
        refine ⟨90882690891180886549937969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60588460594120591033291979 90882690891180886549937969)
        ·
          refine ⟨68162018168385664912453477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 90882690891180886549937969 68162018168385664912453477)
          ·
            refine ⟨12780378406572312171085027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 68162018168385664912453477 12780378406572312171085027)
            ·
              refine ⟨19170567609858468256627541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12780378406572312171085027 19170567609858468256627541)
              ·
                refine ⟨112327544589014462441177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 19170567609858468256627541 112327544589014462441177)
                ·
                  rfl

theorem cell22_2953221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 1, 9].length) (baseStart_2953221 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2953221 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2953221 prefixEnd_2953221 := by exact prefixLift 2953221
  have htrace : WordTrace (prefixWord ++ tailWord_2953221) baseStart_2953221 baseEnd_2953221 := by
    simpa [prefixWord, tailWord_2953221, baseEnd_2953221] using wordTrace_append hprefix tailTrace_2953221
  have hstable : (prefixWord ++ tailWord_2953221).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2953221).length < 2 ^ (prefixWord ++ tailWord_2953221).sum := by decide
  have hdescent : baseEnd_2953221 < baseStart_2953221 := by decide
  rcases family_descends (prefixWord ++ tailWord_2953221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2953229 : List Nat := [1, 7, 1, 2, 1, 1, 1, 1, 3, 4]
def baseStart_2953229 : Nat := 118140960795 + 2953229 * 2 ^ 59
def prefixEnd_2953229 : Nat := 4983230072969 + 3 ^ 40 * 2953229 * 2
def baseEnd_2953229 : Nat := 1010950639864620807770569

theorem tailTrace_2953229 : CollatzResearch.WordTrace tailWord_2953229 prefixEnd_2953229 1010950639864620807770569 := by
  unfold tailWord_2953229
  simp only [CollatzResearch.WordTrace]
  refine ⟨107713110617963179203254741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71808740411975452802169827 107713110617963179203254741)
  ·
    refine ⟨2524526030108512012576283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 107713110617963179203254741 2524526030108512012576283)
    ·
      refine ⟨3786789045162768018864425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2524526030108512012576283 3786789045162768018864425)
      ·
        refine ⟨2840091783872076014148319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3786789045162768018864425 2840091783872076014148319)
        ·
          refine ⟨4260137675808114021222479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2840091783872076014148319 4260137675808114021222479)
          ·
            refine ⟨6390206513712171031833719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4260137675808114021222479 6390206513712171031833719)
            ·
              refine ⟨9585309770568256547750579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6390206513712171031833719 9585309770568256547750579)
              ·
                refine ⟨14377964655852384821625869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9585309770568256547750579 14377964655852384821625869)
                ·
                  refine ⟨5391736745944644308109701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14377964655852384821625869 5391736745944644308109701)
                  ·
                    refine ⟨1010950639864620807770569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5391736745944644308109701 1010950639864620807770569)
                    ·
                      rfl

theorem cell22_2953229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 1, 1, 1, 3, 4].length) (baseStart_2953229 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2953229 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2953229 prefixEnd_2953229 := by exact prefixLift 2953229
  have htrace : WordTrace (prefixWord ++ tailWord_2953229) baseStart_2953229 baseEnd_2953229 := by
    simpa [prefixWord, tailWord_2953229, baseEnd_2953229] using wordTrace_append hprefix tailTrace_2953229
  have hstable : (prefixWord ++ tailWord_2953229).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2953229).length < 2 ^ (prefixWord ++ tailWord_2953229).sum := by decide
  have hdescent : baseEnd_2953229 < baseStart_2953229 := by decide
  rcases family_descends (prefixWord ++ tailWord_2953229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2953255 : List Nat := [1, 1, 7, 1, 3, 9]
def baseStart_2953255 : Nat := 118140960795 + 2953255 * 2 ^ 59
def prefixEnd_2953255 : Nat := 4983230072969 + 3 ^ 40 * 2953255 * 2
def baseEnd_2953255 : Nat := 12480981977727967982969

theorem tailTrace_2953255 : CollatzResearch.WordTrace tailWord_2953255 prefixEnd_2953255 12480981977727967982969 := by
  unfold tailWord_2953255
  simp only [CollatzResearch.WordTrace]
  refine ⟨107714058915868985643701219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71809372610579323762467479 107714058915868985643701219)
  ·
    refine ⟨161571088373803478465551829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107714058915868985643701219 161571088373803478465551829)
    ·
      refine ⟨3786822383761019026536371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 161571088373803478465551829 3786822383761019026536371)
      ·
        refine ⟨5680233575641528539804557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3786822383761019026536371 5680233575641528539804557)
        ·
          refine ⟨2130087590865573202426709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5680233575641528539804557 2130087590865573202426709)
          ·
            refine ⟨12480981977727967982969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 2130087590865573202426709 12480981977727967982969)
            ·
              rfl

theorem cell22_2953255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 3, 9].length) (baseStart_2953255 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2953255 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2953255 prefixEnd_2953255 := by exact prefixLift 2953255
  have htrace : WordTrace (prefixWord ++ tailWord_2953255) baseStart_2953255 baseEnd_2953255 := by
    simpa [prefixWord, tailWord_2953255, baseEnd_2953255] using wordTrace_append hprefix tailTrace_2953255
  have hstable : (prefixWord ++ tailWord_2953255).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2953255).length < 2 ^ (prefixWord ++ tailWord_2953255).sum := by decide
  have hdescent : baseEnd_2953255 < baseStart_2953255 := by decide
  rcases family_descends (prefixWord ++ tailWord_2953255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2953328 : List Nat := [2, 1, 1, 1, 5, 2, 1, 3, 6]
def baseStart_2953328 : Nat := 118140960795 + 2953328 * 2 ^ 59
def prefixEnd_2953328 : Nat := 4983230072969 + 3 ^ 40 * 2953328 * 2
def baseEnd_2953328 : Nat := 336994843195939183181755

theorem tailTrace_2953328 : CollatzResearch.WordTrace tailWord_2953328 prefixEnd_2953328 336994843195939183181755 := by
  unfold tailWord_2953328
  simp only [CollatzResearch.WordTrace]
  refine ⟨53858360722302259555554319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71811147629736346074072425 53858360722302259555554319)
  ·
    refine ⟨80787541083453389333331479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53858360722302259555554319 80787541083453389333331479)
    ·
      refine ⟨121181311625180083999997219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80787541083453389333331479 121181311625180083999997219)
      ·
        refine ⟨181771967437770125999995829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121181311625180083999997219 181771967437770125999995829)
        ·
          refine ⟨17041121947290949312499609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 181771967437770125999995829 17041121947290949312499609)
          ·
            refine ⟨12780841460468211984374707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17041121947290949312499609 12780841460468211984374707)
            ·
              refine ⟨19171262190702317976562061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12780841460468211984374707 19171262190702317976562061)
              ·
                refine ⟨7189223321513369241210773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19171262190702317976562061 7189223321513369241210773)
                ·
                  refine ⟨336994843195939183181755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7189223321513369241210773 336994843195939183181755)
                  ·
                    rfl

theorem cell22_2953328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 1, 3, 6].length) (baseStart_2953328 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2953328 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2953328 prefixEnd_2953328 := by exact prefixLift 2953328
  have htrace : WordTrace (prefixWord ++ tailWord_2953328) baseStart_2953328 baseEnd_2953328 := by
    simpa [prefixWord, tailWord_2953328, baseEnd_2953328] using wordTrace_append hprefix tailTrace_2953328
  have hstable : (prefixWord ++ tailWord_2953328).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2953328).length < 2 ^ (prefixWord ++ tailWord_2953328).sum := by decide
  have hdescent : baseEnd_2953328 < baseStart_2953328 := by decide
  rcases family_descends (prefixWord ++ tailWord_2953328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2953373 : List Nat := [1, 4, 2, 1, 1, 3, 10]
def baseStart_2953373 : Nat := 118140960795 + 2953373 * 2 ^ 59
def prefixEnd_2953373 : Nat := 4983230072969 + 3 ^ 40 * 2953373 * 2
def baseEnd_2953373 : Nat := 37444442000276016006301

theorem tailTrace_2953373 : CollatzResearch.WordTrace tailWord_2953373 prefixEnd_2953373 37444442000276016006301 := by
  unfold tailWord_2953373
  simp only [CollatzResearch.WordTrace]
  refine ⟨107718362729441491796496773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71812241819627661197664515 107718362729441491796496773)
  ·
    refine ⟨20197193011770279711843145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 107718362729441491796496773 20197193011770279711843145)
    ·
      refine ⟨15147894758827709783882359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20197193011770279711843145 15147894758827709783882359)
      ·
        refine ⟨22721842138241564675823539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15147894758827709783882359 22721842138241564675823539)
        ·
          refine ⟨34082763207362347013735309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22721842138241564675823539 34082763207362347013735309)
          ·
            refine ⟨12781036202760880130150741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34082763207362347013735309 12781036202760880130150741)
            ·
              refine ⟨37444442000276016006301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 12781036202760880130150741 37444442000276016006301)
              ·
                rfl

theorem cell22_2953373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 10].length) (baseStart_2953373 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2953373 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2953373 prefixEnd_2953373 := by exact prefixLift 2953373
  have htrace : WordTrace (prefixWord ++ tailWord_2953373) baseStart_2953373 baseEnd_2953373 := by
    simpa [prefixWord, tailWord_2953373, baseEnd_2953373] using wordTrace_append hprefix tailTrace_2953373
  have hstable : (prefixWord ++ tailWord_2953373).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2953373).length < 2 ^ (prefixWord ++ tailWord_2953373).sum := by decide
  have hdescent : baseEnd_2953373 < baseStart_2953373 := by decide
  rcases family_descends (prefixWord ++ tailWord_2953373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2953375 : List Nat := [1, 1, 2, 6, 1, 1, 1, 1, 4, 4]
def baseStart_2953375 : Nat := 118140960795 + 2953375 * 2 ^ 59
def prefixEnd_2953375 : Nat := 4983230072969 + 3 ^ 40 * 2953375 * 2
def baseEnd_2953375 : Nat := 1011000618648325093620121

theorem tailTrace_2953375 : CollatzResearch.WordTrace tailWord_2953375 prefixEnd_2953375 1011000618648325093620121 := by
  unfold tailWord_2953375
  simp only [CollatzResearch.WordTrace]
  refine ⟨107718435675434246138069579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71812290450289497425379719 107718435675434246138069579)
  ·
    refine ⟨161577653513151369207104369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107718435675434246138069579 161577653513151369207104369)
    ·
      refine ⟨121183240134863526905328277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 161577653513151369207104369 121183240134863526905328277)
      ·
        refine ⟨5680464381321727823687263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 121183240134863526905328277 5680464381321727823687263)
        ·
          refine ⟨8520696571982591735530895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5680464381321727823687263 8520696571982591735530895)
          ·
            refine ⟨12781044857973887603296343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8520696571982591735530895 12781044857973887603296343)
            ·
              refine ⟨19171567286960831404944515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12781044857973887603296343 19171567286960831404944515)
              ·
                refine ⟨28757350930441247107416773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19171567286960831404944515 28757350930441247107416773)
                ·
                  refine ⟨5392003299457733832640645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28757350930441247107416773 5392003299457733832640645)
                  ·
                    refine ⟨1011000618648325093620121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5392003299457733832640645 1011000618648325093620121)
                    ·
                      rfl

theorem cell22_2953375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 1, 1, 4, 4].length) (baseStart_2953375 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2953375 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2953375 prefixEnd_2953375 := by exact prefixLift 2953375
  have htrace : WordTrace (prefixWord ++ tailWord_2953375) baseStart_2953375 baseEnd_2953375 := by
    simpa [prefixWord, tailWord_2953375, baseEnd_2953375] using wordTrace_append hprefix tailTrace_2953375
  have hstable : (prefixWord ++ tailWord_2953375).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2953375).length < 2 ^ (prefixWord ++ tailWord_2953375).sum := by decide
  have hdescent : baseEnd_2953375 < baseStart_2953375 := by decide
  rcases family_descends (prefixWord ++ tailWord_2953375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2953405 : List Nat := [1, 4, 1, 2, 1, 1, 1, 3, 5, 3]
def baseStart_2953405 : Nat := 118140960795 + 2953405 * 2 ^ 59
def prefixEnd_2953405 : Nat := 4983230072969 + 3 ^ 40 * 2953405 * 2
def baseEnd_2953405 : Nat := 1011010888261415015370029

theorem tailTrace_2953405 : CollatzResearch.WordTrace tailWord_2953405 prefixEnd_2953405 1011010888261415015370029 := by
  unfold tailWord_2953405
  simp only [CollatzResearch.WordTrace]
  refine ⟨107719529865325561261661669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71813019910217040841107779 107719529865325561261661669)
  ·
    refine ⟨20197411849748542736561563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 107719529865325561261661669 20197411849748542736561563)
    ·
      refine ⟨30296117774622814104842345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20197411849748542736561563 30296117774622814104842345)
      ·
        refine ⟨22722088330967110578631759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30296117774622814104842345 22722088330967110578631759)
        ·
          refine ⟨34083132496450665867947639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22722088330967110578631759 34083132496450665867947639)
          ·
            refine ⟨51124698744675998801921459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34083132496450665867947639 51124698744675998801921459)
            ·
              refine ⟨76687048117013998202882189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51124698744675998801921459 76687048117013998202882189)
              ·
                refine ⟨28757643043880249326080821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 76687048117013998202882189 28757643043880249326080821)
                ·
                  refine ⟨2696029035363773374320077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 28757643043880249326080821 2696029035363773374320077)
                  ·
                    refine ⟨1011010888261415015370029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2696029035363773374320077 1011010888261415015370029)
                    ·
                      rfl

theorem cell22_2953405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 3, 5, 3].length) (baseStart_2953405 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2953405 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2953405 prefixEnd_2953405 := by exact prefixLift 2953405
  have htrace : WordTrace (prefixWord ++ tailWord_2953405) baseStart_2953405 baseEnd_2953405 := by
    simpa [prefixWord, tailWord_2953405, baseEnd_2953405] using wordTrace_append hprefix tailTrace_2953405
  have hstable : (prefixWord ++ tailWord_2953405).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2953405).length < 2 ^ (prefixWord ++ tailWord_2953405).sum := by decide
  have hdescent : baseEnd_2953405 < baseStart_2953405 := by decide
  rcases family_descends (prefixWord ++ tailWord_2953405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2953409 : List Nat := [1, 2, 6, 1, 2, 1, 2, 1, 2, 4]
def baseStart_2953409 : Nat := 118140960795 + 2953409 * 2 ^ 59
def prefixEnd_2953409 : Nat := 4983230072969 + 3 ^ 40 * 2953409 * 2
def baseEnd_2953409 : Nat := 1011012257543160338270017

theorem tailTrace_2953409 : CollatzResearch.WordTrace tailWord_2953409 prefixEnd_2953409 1011012257543160338270017 := by
  unfold tailWord_2953409
  simp only [CollatzResearch.WordTrace]
  refine ⟨107719675757311069944807281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71813117171540713296538187 107719675757311069944807281)
  ·
    refine ⟨80789756817983302458605461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107719675757311069944807281 80789756817983302458605461)
    ·
      refine ⟨3787019850842967302747131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 80789756817983302458605461 3787019850842967302747131)
      ·
        refine ⟨5680529776264450954120697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3787019850842967302747131 5680529776264450954120697)
        ·
          refine ⟨4260397332198338215590523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5680529776264450954120697 4260397332198338215590523)
          ·
            refine ⟨6390595998297507323385785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4260397332198338215590523 6390595998297507323385785)
            ·
              refine ⟨4792946998723130492539339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6390595998297507323385785 4792946998723130492539339)
              ·
                refine ⟨7189420498084695738809009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4792946998723130492539339 7189420498084695738809009)
                ·
                  refine ⟨5392065373563521804106757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7189420498084695738809009 5392065373563521804106757)
                  ·
                    refine ⟨1011012257543160338270017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5392065373563521804106757 1011012257543160338270017)
                    ·
                      rfl

theorem cell22_2953409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 1, 2, 1, 2, 4].length) (baseStart_2953409 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2953409 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2953409 prefixEnd_2953409 := by exact prefixLift 2953409
  have htrace : WordTrace (prefixWord ++ tailWord_2953409) baseStart_2953409 baseEnd_2953409 := by
    simpa [prefixWord, tailWord_2953409, baseEnd_2953409] using wordTrace_append hprefix tailTrace_2953409
  have hstable : (prefixWord ++ tailWord_2953409).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2953409).length < 2 ^ (prefixWord ++ tailWord_2953409).sum := by decide
  have hdescent : baseEnd_2953409 < baseStart_2953409 := by decide
  rcases family_descends (prefixWord ++ tailWord_2953409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2953450 : List Nat := [3, 1, 3, 1, 1, 2, 3, 1, 2, 5]
def baseStart_2953450 : Nat := 118140960795 + 2953450 * 2 ^ 59
def prefixEnd_2953450 : Nat := 4983230072969 + 3 ^ 40 * 2953450 * 2
def baseEnd_2953450 : Nat := 1011026292681049897994891

theorem tailTrace_2953450 : CollatzResearch.WordTrace tailWord_2953450 prefixEnd_2953450 1011026292681049897994891 := by
  unfold tailWord_2953450
  simp only [CollatzResearch.WordTrace]
  refine ⟨26930292787540633486762451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71814114100108355964699869 26930292787540633486762451)
  ·
    refine ⟨40395439181310950230143677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26930292787540633486762451 40395439181310950230143677)
    ·
      refine ⟨15148289692991606336303879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40395439181310950230143677 15148289692991606336303879)
      ·
        refine ⟨22722434539487409504455819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15148289692991606336303879 22722434539487409504455819)
        ·
          refine ⟨34083651809231114256683729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22722434539487409504455819 34083651809231114256683729)
          ·
            refine ⟨25562738856923335692512797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34083651809231114256683729 25562738856923335692512797)
            ·
              refine ⟨9586027071346250884692299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25562738856923335692512797 9586027071346250884692299)
              ·
                refine ⟨14379040607019376327038449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9586027071346250884692299 14379040607019376327038449)
                ·
                  refine ⟨10784280455264532245278837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14379040607019376327038449 10784280455264532245278837)
                  ·
                    refine ⟨1011026292681049897994891, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10784280455264532245278837 1011026292681049897994891)
                    ·
                      rfl

theorem cell22_2953450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 3, 1, 2, 5].length) (baseStart_2953450 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2953450 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2953450 prefixEnd_2953450 := by exact prefixLift 2953450
  have htrace : WordTrace (prefixWord ++ tailWord_2953450) baseStart_2953450 baseEnd_2953450 := by
    simpa [prefixWord, tailWord_2953450, baseEnd_2953450] using wordTrace_append hprefix tailTrace_2953450
  have hstable : (prefixWord ++ tailWord_2953450).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2953450).length < 2 ^ (prefixWord ++ tailWord_2953450).sum := by decide
  have hdescent : baseEnd_2953450 < baseStart_2953450 := by decide
  rcases family_descends (prefixWord ++ tailWord_2953450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2953525 : List Nat := [1, 3, 3, 1, 2, 1, 3, 8]
def baseStart_2953525 : Nat := 118140960795 + 2953525 * 2 ^ 59
def prefixEnd_2953525 : Nat := 4983230072969 + 3 ^ 40 * 2953525 * 2
def baseEnd_2953525 : Nat := 112339107412641633596629

theorem tailTrace_2953525 : CollatzResearch.WordTrace tailWord_2953525 prefixEnd_2953525 112339107412641633596629 := by
  unfold tailWord_2953525
  simp only [CollatzResearch.WordTrace]
  refine ⟨107723906624890821756030029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71815937749927214504020019 107723906624890821756030029)
  ·
    refine ⟨40396464984334058158511261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 107723906624890821756030029 40396464984334058158511261)
    ·
      refine ⟨15148674369125271809441723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40396464984334058158511261 15148674369125271809441723)
      ·
        refine ⟨22723011553687907714162585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15148674369125271809441723 22723011553687907714162585)
        ·
          refine ⟨17042258665265930785621939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22723011553687907714162585 17042258665265930785621939)
          ·
            refine ⟨25563387997898896178432909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17042258665265930785621939 25563387997898896178432909)
            ·
              refine ⟨9586270499212086066912341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25563387997898896178432909 9586270499212086066912341)
              ·
                refine ⟨112339107412641633596629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9586270499212086066912341 112339107412641633596629)
                ·
                  rfl

theorem cell22_2953525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 3, 8].length) (baseStart_2953525 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2953525 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2953525 prefixEnd_2953525 := by exact prefixLift 2953525
  have htrace : WordTrace (prefixWord ++ tailWord_2953525) baseStart_2953525 baseEnd_2953525 := by
    simpa [prefixWord, tailWord_2953525, baseEnd_2953525] using wordTrace_append hprefix tailTrace_2953525
  have hstable : (prefixWord ++ tailWord_2953525).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2953525).length < 2 ^ (prefixWord ++ tailWord_2953525).sum := by decide
  have hdescent : baseEnd_2953525 < baseStart_2953525 := by decide
  rcases family_descends (prefixWord ++ tailWord_2953525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2953585 : List Nat := [1, 2, 2, 2, 1, 2, 1, 2, 4, 5]
def baseStart_2953585 : Nat := 118140960795 + 2953585 * 2 ^ 59
def prefixEnd_2953585 : Nat := 4983230072969 + 3 ^ 40 * 2953585 * 2
def baseEnd_2953585 : Nat := 1011072505939954545869477

theorem tailTrace_2953585 : CollatzResearch.WordTrace tailWord_2953585 prefixEnd_2953585 1011072505939954545869477 := by
  unfold tailWord_2953585
  simp only [CollatzResearch.WordTrace]
  refine ⟨107726095004673452003214209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71817396669782301335476139 107726095004673452003214209)
  ·
    refine ⟨80794571253505089002410657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107726095004673452003214209 80794571253505089002410657)
    ·
      refine ⟨60595928440128816751807993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80794571253505089002410657 60595928440128816751807993)
      ·
        refine ⟨45446946330096612563855995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60595928440128816751807993 45446946330096612563855995)
        ·
          refine ⟨68170419495144918845783993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45446946330096612563855995 68170419495144918845783993)
          ·
            refine ⟨51127814621358689134337995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 68170419495144918845783993 51127814621358689134337995)
            ·
              refine ⟨76691721932038033701506993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51127814621358689134337995 76691721932038033701506993)
              ·
                refine ⟨57518791449028525276130245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 76691721932038033701506993 57518791449028525276130245)
                ·
                  refine ⟨10784773396692848489274421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 57518791449028525276130245 10784773396692848489274421)
                  ·
                    refine ⟨1011072505939954545869477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10784773396692848489274421 1011072505939954545869477)
                    ·
                      rfl

theorem cell22_2953585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 2, 4, 5].length) (baseStart_2953585 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2953585 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2953585 prefixEnd_2953585 := by exact prefixLift 2953585
  have htrace : WordTrace (prefixWord ++ tailWord_2953585) baseStart_2953585 baseEnd_2953585 := by
    simpa [prefixWord, tailWord_2953585, baseEnd_2953585] using wordTrace_append hprefix tailTrace_2953585
  have hstable : (prefixWord ++ tailWord_2953585).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2953585).length < 2 ^ (prefixWord ++ tailWord_2953585).sum := by decide
  have hdescent : baseEnd_2953585 < baseStart_2953585 := by decide
  rcases family_descends (prefixWord ++ tailWord_2953585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2953632 : List Nat := [2, 1, 1, 4, 1, 4, 1, 2, 6]
def baseStart_2953632 : Nat := 118140960795 + 2953632 * 2 ^ 59
def prefixEnd_2953632 : Nat := 4983230072969 + 3 ^ 40 * 2953632 * 2
def baseEnd_2953632 : Nat := 337029531666820696648111

theorem tailTrace_2953632 : CollatzResearch.WordTrace tailWord_2953632 prefixEnd_2953632 337029531666820696648111 := by
  unfold tailWord_2953632
  simp only [CollatzResearch.WordTrace]
  refine ⟨53863904617751589515087575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71818539490335452686783433 53863904617751589515087575)
  ·
    refine ⟨80795856926627384272631363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53863904617751589515087575 80795856926627384272631363)
    ·
      refine ⟨121193785389941076408947045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80795856926627384272631363 121193785389941076408947045)
      ·
        refine ⟨22723834760613951826677571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 121193785389941076408947045 22723834760613951826677571)
        ·
          refine ⟨34085752140920927740016357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22723834760613951826677571 34085752140920927740016357)
          ·
            refine ⟨6391078526422673951253067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 34085752140920927740016357 6391078526422673951253067)
            ·
              refine ⟨9586617789634010926879601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6391078526422673951253067 9586617789634010926879601)
              ·
                refine ⟨7189963342225508195159701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9586617789634010926879601 7189963342225508195159701)
                ·
                  refine ⟨337029531666820696648111, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7189963342225508195159701 337029531666820696648111)
                  ·
                    rfl

theorem cell22_2953632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 4, 1, 2, 6].length) (baseStart_2953632 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2953632 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2953632 prefixEnd_2953632 := by exact prefixLift 2953632
  have htrace : WordTrace (prefixWord ++ tailWord_2953632) baseStart_2953632 baseEnd_2953632 := by
    simpa [prefixWord, tailWord_2953632, baseEnd_2953632] using wordTrace_append hprefix tailTrace_2953632
  have hstable : (prefixWord ++ tailWord_2953632).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2953632).length < 2 ^ (prefixWord ++ tailWord_2953632).sum := by decide
  have hdescent : baseEnd_2953632 < baseStart_2953632 := by decide
  rcases family_descends (prefixWord ++ tailWord_2953632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2953634 : List Nat := [3, 3, 1, 2, 1, 1, 2, 4, 1, 4]
def baseStart_2953634 : Nat := 118140960795 + 2953634 * 2 ^ 59
def prefixEnd_2953634 : Nat := 4983230072969 + 3 ^ 40 * 2953634 * 2
def baseEnd_2953634 : Nat := 1011089279641334751394327

theorem tailTrace_2953634 : CollatzResearch.WordTrace tailWord_2953634 prefixEnd_2953634 1011089279641334751394327 := by
  unfold tailWord_2953634
  simp only [CollatzResearch.WordTrace]
  refine ⟨26931970545373983342936989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71818588120997288914498637 26931970545373983342936989)
  ·
    refine ⟨10099488954515243753601371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26931970545373983342936989 10099488954515243753601371)
    ·
      refine ⟨15149233431772865630402057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10099488954515243753601371 15149233431772865630402057)
      ·
        refine ⟨11361925073829649222801543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15149233431772865630402057 11361925073829649222801543)
        ·
          refine ⟨17042887610744473834202315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11361925073829649222801543 17042887610744473834202315)
          ·
            refine ⟨25564331416116710751303473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17042887610744473834202315 25564331416116710751303473)
            ·
              refine ⟨19173248562087533063477605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25564331416116710751303473 19173248562087533063477605)
              ·
                refine ⟨3594984105391412449402051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19173248562087533063477605 3594984105391412449402051)
                ·
                  refine ⟨5392476158087118674103077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3594984105391412449402051 5392476158087118674103077)
                  ·
                    refine ⟨1011089279641334751394327, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5392476158087118674103077 1011089279641334751394327)
                    ·
                      rfl

theorem cell22_2953634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 2, 4, 1, 4].length) (baseStart_2953634 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2953634 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2953634 prefixEnd_2953634 := by exact prefixLift 2953634
  have htrace : WordTrace (prefixWord ++ tailWord_2953634) baseStart_2953634 baseEnd_2953634 := by
    simpa [prefixWord, tailWord_2953634, baseEnd_2953634] using wordTrace_append hprefix tailTrace_2953634
  have hstable : (prefixWord ++ tailWord_2953634).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2953634).length < 2 ^ (prefixWord ++ tailWord_2953634).sum := by decide
  have hdescent : baseEnd_2953634 < baseStart_2953634 := by decide
  rcases family_descends (prefixWord ++ tailWord_2953634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2953642 : List Nat := [3, 1, 6, 1, 1, 1, 2, 3, 1, 3]
def baseStart_2953642 : Nat := 118140960795 + 2953642 * 2 ^ 59
def prefixEnd_2953642 : Nat := 4983230072969 + 3 ^ 40 * 2953642 * 2
def baseEnd_2953642 : Nat := 1011092018204825397194303

theorem tailTrace_2953642 : CollatzResearch.WordTrace tailWord_2953642 prefixEnd_2953642 1011092018204825397194303 := by
  unfold tailWord_2953642
  simp only [CollatzResearch.WordTrace]
  refine ⟨26932043491366737684509795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71818782643644633825359453 26932043491366737684509795)
  ·
    refine ⟨40398065237050106526764693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26932043491366737684509795 40398065237050106526764693)
    ·
      refine ⟨1893659307986723743442095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 40398065237050106526764693 1893659307986723743442095)
      ·
        refine ⟨2840488961980085615163143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1893659307986723743442095 2840488961980085615163143)
        ·
          refine ⟨4260733442970128422744715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2840488961980085615163143 4260733442970128422744715)
          ·
            refine ⟨6391100164455192634117073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4260733442970128422744715 6391100164455192634117073)
            ·
              refine ⟨4793325123341394475587805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6391100164455192634117073 4793325123341394475587805)
              ·
                refine ⟨1797496921253022928345427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4793325123341394475587805 1797496921253022928345427)
                ·
                  refine ⟨2696245381879534392518141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1797496921253022928345427 2696245381879534392518141)
                  ·
                    refine ⟨1011092018204825397194303, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2696245381879534392518141 1011092018204825397194303)
                    ·
                      rfl

theorem cell22_2953642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 1, 2, 3, 1, 3].length) (baseStart_2953642 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2953642 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2953642 prefixEnd_2953642 := by exact prefixLift 2953642
  have htrace : WordTrace (prefixWord ++ tailWord_2953642) baseStart_2953642 baseEnd_2953642 := by
    simpa [prefixWord, tailWord_2953642, baseEnd_2953642] using wordTrace_append hprefix tailTrace_2953642
  have hstable : (prefixWord ++ tailWord_2953642).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2953642).length < 2 ^ (prefixWord ++ tailWord_2953642).sum := by decide
  have hdescent : baseEnd_2953642 < baseStart_2953642 := by decide
  rcases family_descends (prefixWord ++ tailWord_2953642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2953649 : List Nat := [1, 2, 2, 4, 1, 2, 1, 5, 4]
def baseStart_2953649 : Nat := 118140960795 + 2953649 * 2 ^ 59
def prefixEnd_2953649 : Nat := 4983230072969 + 3 ^ 40 * 2953649 * 2
def baseEnd_2953649 : Nat := 337031471482626570756427

theorem tailTrace_2953649 : CollatzResearch.WordTrace tailWord_2953649 prefixEnd_2953649 337031471482626570756427 := by
  unfold tailWord_2953649
  simp only [CollatzResearch.WordTrace]
  refine ⟨107728429276441590933544001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71818952850961060622362667 107728429276441590933544001)
  ·
    refine ⟨80796321957331193200158001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107728429276441590933544001 80796321957331193200158001)
    ·
      refine ⟨60597241467998394900118501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80796321957331193200158001 60597241467998394900118501)
      ·
        refine ⟨11361982775249699043772219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 60597241467998394900118501 11361982775249699043772219)
        ·
          refine ⟨17042974162874548565658329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11361982775249699043772219 17042974162874548565658329)
          ·
            refine ⟨12782230622155911424243747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17042974162874548565658329 12782230622155911424243747)
            ·
              refine ⟨19173345933233867136365621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12782230622155911424243747 19173345933233867136365621)
              ·
                refine ⟨1797501181240675044034277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 19173345933233867136365621 1797501181240675044034277)
                ·
                  refine ⟨337031471482626570756427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1797501181240675044034277 337031471482626570756427)
                  ·
                    rfl

theorem cell22_2953649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 1, 5, 4].length) (baseStart_2953649 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2953649 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2953649 prefixEnd_2953649 := by exact prefixLift 2953649
  have htrace : WordTrace (prefixWord ++ tailWord_2953649) baseStart_2953649 baseEnd_2953649 := by
    simpa [prefixWord, tailWord_2953649, baseEnd_2953649] using wordTrace_append hprefix tailTrace_2953649
  have hstable : (prefixWord ++ tailWord_2953649).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2953649).length < 2 ^ (prefixWord ++ tailWord_2953649).sum := by decide
  have hdescent : baseEnd_2953649 < baseStart_2953649 := by decide
  rcases family_descends (prefixWord ++ tailWord_2953649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2953739 : List Nat := [1, 1, 1, 1, 7, 2, 1, 3, 5]
def baseStart_2953739 : Nat := 118140960795 + 2953739 * 2 ^ 59
def prefixEnd_2953739 : Nat := 4983230072969 + 3 ^ 40 * 2953739 * 2
def baseEnd_2953739 : Nat := 337041741095716492506335

theorem tailTrace_2953739 : CollatzResearch.WordTrace tailWord_2953739 prefixEnd_2953739 337041741095716492506335 := by
  unfold tailWord_2953739
  simp only [CollatzResearch.WordTrace]
  refine ⟨107731711846115536304320271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71821141230743690869546847 107731711846115536304320271)
  ·
    refine ⟨161597567769173304456480407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107731711846115536304320271 161597567769173304456480407)
    ·
      refine ⟨242396351653759956684720611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 161597567769173304456480407 242396351653759956684720611)
      ·
        refine ⟨363594527480639935027080917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 242396351653759956684720611 363594527480639935027080917)
        ·
          refine ⟨8521746737827498477197209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 363594527480639935027080917 8521746737827498477197209)
          ·
            refine ⟨6391310053370623857897907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8521746737827498477197209 6391310053370623857897907)
            ·
              refine ⟨9586965080055935786846861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6391310053370623857897907 9586965080055935786846861)
              ·
                refine ⟨3595111905020975920067573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9586965080055935786846861 3595111905020975920067573)
                ·
                  refine ⟨337041741095716492506335, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3595111905020975920067573 337041741095716492506335)
                  ·
                    rfl

theorem cell22_2953739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 2, 1, 3, 5].length) (baseStart_2953739 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2953739 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2953739 prefixEnd_2953739 := by exact prefixLift 2953739
  have htrace : WordTrace (prefixWord ++ tailWord_2953739) baseStart_2953739 baseEnd_2953739 := by
    simpa [prefixWord, tailWord_2953739, baseEnd_2953739] using wordTrace_append hprefix tailTrace_2953739
  have hstable : (prefixWord ++ tailWord_2953739).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2953739).length < 2 ^ (prefixWord ++ tailWord_2953739).sum := by decide
  have hdescent : baseEnd_2953739 < baseStart_2953739 := by decide
  rcases family_descends (prefixWord ++ tailWord_2953739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2953799 : List Nat := [1, 1, 4, 1, 4, 1, 1, 3, 1, 5]
def baseStart_2953799 : Nat := 118140960795 + 2953799 * 2 ^ 59
def prefixEnd_2953799 : Nat := 4983230072969 + 3 ^ 40 * 2953799 * 2
def baseEnd_2953799 : Nat := 1011145762513329321018821

theorem tailTrace_2953799 : CollatzResearch.WordTrace tailWord_2953799 prefixEnd_2953799 1011145762513329321018821 := by
  unfold tailWord_2953799
  simp only [CollatzResearch.WordTrace]
  refine ⟨107733900225898166551504451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71822600150598777701002967 107733900225898166551504451)
  ·
    refine ⟨161600850338847249827256677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107733900225898166551504451 161600850338847249827256677)
    ·
      refine ⟨30300159438533859342610627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 161600850338847249827256677 30300159438533859342610627)
      ·
        refine ⟨45450239157800789013915941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30300159438533859342610627 45450239157800789013915941)
        ·
          refine ⟨8521919842087647940109239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 45450239157800789013915941 8521919842087647940109239)
          ·
            refine ⟨12782879763131471910163859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8521919842087647940109239 12782879763131471910163859)
            ·
              refine ⟨19174319644697207865245789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12782879763131471910163859 19174319644697207865245789)
              ·
                refine ⟨7190369866761452949467171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19174319644697207865245789 7190369866761452949467171)
                ·
                  refine ⟨10785554800142179424200757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7190369866761452949467171 10785554800142179424200757)
                  ·
                    refine ⟨1011145762513329321018821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10785554800142179424200757 1011145762513329321018821)
                    ·
                      rfl

theorem cell22_2953799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 1, 3, 1, 5].length) (baseStart_2953799 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2953799 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2953799 prefixEnd_2953799 := by exact prefixLift 2953799
  have htrace : WordTrace (prefixWord ++ tailWord_2953799) baseStart_2953799 baseEnd_2953799 := by
    simpa [prefixWord, tailWord_2953799, baseEnd_2953799] using wordTrace_append hprefix tailTrace_2953799
  have hstable : (prefixWord ++ tailWord_2953799).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2953799).length < 2 ^ (prefixWord ++ tailWord_2953799).sum := by decide
  have hdescent : baseEnd_2953799 < baseStart_2953799 := by decide
  rcases family_descends (prefixWord ++ tailWord_2953799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2953820 : List Nat := [2, 2, 4, 1, 3, 2, 2, 1, 1, 4]
def baseStart_2953820 : Nat := 118140960795 + 2953820 * 2 ^ 59
def prefixEnd_2953820 : Nat := 4983230072969 + 3 ^ 40 * 2953820 * 2
def baseEnd_2953820 : Nat := 1011152951242492266243757

theorem tailTrace_2953820 : CollatzResearch.WordTrace tailWord_2953820 prefixEnd_2953820 1011152951242492266243757 := by
  unfold tailWord_2953820
  simp only [CollatzResearch.WordTrace]
  refine ⟨53867333079411043569009457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71823110772548058092012609 53867333079411043569009457)
  ·
    refine ⟨40400499809558282676757093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53867333079411043569009457 40400499809558282676757093)
    ·
      refine ⟨7575093714292178001891955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 40400499809558282676757093 7575093714292178001891955)
      ·
        refine ⟨11362640571438267002837933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7575093714292178001891955 11362640571438267002837933)
        ·
          refine ⟨4260990214289350126064225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11362640571438267002837933 4260990214289350126064225)
          ·
            refine ⟨3195742660717012594548169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4260990214289350126064225 3195742660717012594548169)
            ·
              refine ⟨2396806995537759445911127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3195742660717012594548169 2396806995537759445911127)
              ·
                refine ⟨3595210493306639168866691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2396806995537759445911127 3595210493306639168866691)
                ·
                  refine ⟨5392815739959958753300037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3595210493306639168866691 5392815739959958753300037)
                  ·
                    refine ⟨1011152951242492266243757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5392815739959958753300037 1011152951242492266243757)
                    ·
                      rfl

theorem cell22_2953820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 2, 2, 1, 1, 4].length) (baseStart_2953820 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2953820 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2953820 prefixEnd_2953820 := by exact prefixLift 2953820
  have htrace : WordTrace (prefixWord ++ tailWord_2953820) baseStart_2953820 baseEnd_2953820 := by
    simpa [prefixWord, tailWord_2953820, baseEnd_2953820] using wordTrace_append hprefix tailTrace_2953820
  have hstable : (prefixWord ++ tailWord_2953820).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2953820).length < 2 ^ (prefixWord ++ tailWord_2953820).sum := by decide
  have hdescent : baseEnd_2953820 < baseStart_2953820 := by decide
  rcases family_descends (prefixWord ++ tailWord_2953820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2953829 : List Nat := [1, 3, 1, 3, 4, 1, 9]
def baseStart_2953829 : Nat := 118140960795 + 2953829 * 2 ^ 59
def prefixEnd_2953829 : Nat := 4983230072969 + 3 ^ 40 * 2953829 * 2
def baseEnd_2953829 : Nat := 37450223412089601584027

theorem tailTrace_2953829 : CollatzResearch.WordTrace tailWord_2953829 prefixEnd_2953829 37450223412089601584027 := by
  unfold tailWord_2953829
  simp only [CollatzResearch.WordTrace]
  refine ⟨107734994415789481675096541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71823329610526321116731027 107734994415789481675096541)
  ·
    refine ⟨40400622905921055628161203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 107734994415789481675096541 40400622905921055628161203)
    ·
      refine ⟨60600934358881583442241805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40400622905921055628161203 60600934358881583442241805)
      ·
        refine ⟨22725350384580593790840677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 60600934358881583442241805 22725350384580593790840677)
        ·
          refine ⟨4261003197108861335782627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22725350384580593790840677 4261003197108861335782627)
          ·
            refine ⟨6391504795663292003673941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4261003197108861335782627 6391504795663292003673941)
            ·
              refine ⟨37450223412089601584027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 6391504795663292003673941 37450223412089601584027)
              ·
                rfl

theorem cell22_2953829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 1, 9].length) (baseStart_2953829 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2953829 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2953829 prefixEnd_2953829 := by exact prefixLift 2953829
  have htrace : WordTrace (prefixWord ++ tailWord_2953829) baseStart_2953829 baseEnd_2953829 := by
    simpa [prefixWord, tailWord_2953829, baseEnd_2953829] using wordTrace_append hprefix tailTrace_2953829
  have hstable : (prefixWord ++ tailWord_2953829).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2953829).length < 2 ^ (prefixWord ++ tailWord_2953829).sum := by decide
  have hdescent : baseEnd_2953829 < baseStart_2953829 := by decide
  rcases family_descends (prefixWord ++ tailWord_2953829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2953861 : List Nat := [1, 3, 1, 1, 4, 2, 2, 2, 3, 3]
def baseStart_2953861 : Nat := 118140960795 + 2953861 * 2 ^ 59
def prefixEnd_2953861 : Nat := 4983230072969 + 3 ^ 40 * 2953861 * 2
def baseEnd_2953861 : Nat := 1011166986380381825968631

theorem tailTrace_2953861 : CollatzResearch.WordTrace tailWord_2953861 prefixEnd_2953861 1011166986380381825968631 := by
  unfold tailWord_2953861
  simp only [CollatzResearch.WordTrace]
  refine ⟨107736161551673551140261437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71824107701115700760174291 107736161551673551140261437)
  ·
    refine ⟨40401060581877581677598039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 107736161551673551140261437 40401060581877581677598039)
    ·
      refine ⟨60601590872816372516397059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40401060581877581677598039 60601590872816372516397059)
      ·
        refine ⟨90902386309224558774595589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60601590872816372516397059 90902386309224558774595589)
        ·
          refine ⟨17044197432979604770236673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 90902386309224558774595589 17044197432979604770236673)
          ·
            refine ⟨12783148074734703577677505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17044197432979604770236673 12783148074734703577677505)
            ·
              refine ⟨9587361056051027683258129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12783148074734703577677505 9587361056051027683258129)
              ·
                refine ⟨7190520792038270762443597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9587361056051027683258129 7190520792038270762443597)
                ·
                  refine ⟨2696445297014351535916349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7190520792038270762443597 2696445297014351535916349)
                  ·
                    refine ⟨1011166986380381825968631, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2696445297014351535916349 1011166986380381825968631)
                    ·
                      rfl

theorem cell22_2953861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 2, 2, 3, 3].length) (baseStart_2953861 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2953861 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2953861 prefixEnd_2953861 := by exact prefixLift 2953861
  have htrace : WordTrace (prefixWord ++ tailWord_2953861) baseStart_2953861 baseEnd_2953861 := by
    simpa [prefixWord, tailWord_2953861, baseEnd_2953861] using wordTrace_append hprefix tailTrace_2953861
  have hstable : (prefixWord ++ tailWord_2953861).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2953861).length < 2 ^ (prefixWord ++ tailWord_2953861).sum := by decide
  have hdescent : baseEnd_2953861 < baseStart_2953861 := by decide
  rcases family_descends (prefixWord ++ tailWord_2953861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2953904 : List Nat := [2, 1, 1, 1, 2, 1, 3, 4, 3, 4]
def baseStart_2953904 : Nat := 118140960795 + 2953904 * 2 ^ 59
def prefixEnd_2953904 : Nat := 4983230072969 + 3 ^ 40 * 2953904 * 2
def baseEnd_2953904 : Nat := 1011181706159144047143499

theorem tailTrace_2953904 : CollatzResearch.WordTrace tailWord_2953904 prefixEnd_2953904 1011181706159144047143499 := by
  unfold tailWord_2953904
  simp only [CollatzResearch.WordTrace]
  refine ⟨53868864945258884742038383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71825153260345179656051177 53868864945258884742038383)
  ·
    refine ⟨80803297417888327113057575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53868864945258884742038383 80803297417888327113057575)
    ·
      refine ⟨121204946126832490669586363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80803297417888327113057575 121204946126832490669586363)
      ·
        refine ⟨181807419190248736004379545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121204946126832490669586363 181807419190248736004379545)
        ·
          refine ⟨136355564392686552003284659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 181807419190248736004379545 136355564392686552003284659)
          ·
            refine ⟨204533346589029828004926989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 136355564392686552003284659 204533346589029828004926989)
            ·
              refine ⟨76700004970886185501847621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 204533346589029828004926989 76700004970886185501847621)
              ·
                refine ⟨14381250932041159781596429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 76700004970886185501847621 14381250932041159781596429)
                ·
                  refine ⟨5392969099515434918098661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14381250932041159781596429 5392969099515434918098661)
                  ·
                    refine ⟨1011181706159144047143499, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5392969099515434918098661 1011181706159144047143499)
                    ·
                      rfl

theorem cell22_2953904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 4, 3, 4].length) (baseStart_2953904 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2953904 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2953904 prefixEnd_2953904 := by exact prefixLift 2953904
  have htrace : WordTrace (prefixWord ++ tailWord_2953904) baseStart_2953904 baseEnd_2953904 := by
    simpa [prefixWord, tailWord_2953904, baseEnd_2953904] using wordTrace_append hprefix tailTrace_2953904
  have hstable : (prefixWord ++ tailWord_2953904).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2953904).length < 2 ^ (prefixWord ++ tailWord_2953904).sum := by decide
  have hdescent : baseEnd_2953904 < baseStart_2953904 := by decide
  rcases family_descends (prefixWord ++ tailWord_2953904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2953953 : List Nat := [1, 2, 3, 1, 4, 2, 1, 4, 4]
def baseStart_2953953 : Nat := 118140960795 + 2953953 * 2 ^ 59
def prefixEnd_2953953 : Nat := 4983230072969 + 3 ^ 40 * 2953953 * 2
def baseEnd_2953953 : Nat := 337066159953508084222783

theorem tailTrace_2953953 : CollatzResearch.WordTrace tailWord_2953953 prefixEnd_2953953 337066159953508084222783 := by
  unfold tailWord_2953953
  simp only [CollatzResearch.WordTrace]
  refine ⟨107739517067340250852610513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71826344711560167235073675 107739517067340250852610513)
  ·
    refine ⟨80804637800505188139457885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107739517067340250852610513 80804637800505188139457885)
    ·
      refine ⟨30301739175189445552296707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 80804637800505188139457885 30301739175189445552296707)
      ·
        refine ⟨45452608762784168328445061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30301739175189445552296707 45452608762784168328445061)
        ·
          refine ⟨8522364143022031561583449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 45452608762784168328445061 8522364143022031561583449)
          ·
            refine ⟨6391773107266523671187587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8522364143022031561583449 6391773107266523671187587)
            ·
              refine ⟨9587659660899785506781381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6391773107266523671187587 9587659660899785506781381)
              ·
                refine ⟨1797686186418709782521509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9587659660899785506781381 1797686186418709782521509)
                ·
                  refine ⟨337066159953508084222783, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1797686186418709782521509 337066159953508084222783)
                  ·
                    rfl

theorem cell22_2953953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 2, 1, 4, 4].length) (baseStart_2953953 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2953953 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2953953 prefixEnd_2953953 := by exact prefixLift 2953953
  have htrace : WordTrace (prefixWord ++ tailWord_2953953) baseStart_2953953 baseEnd_2953953 := by
    simpa [prefixWord, tailWord_2953953, baseEnd_2953953] using wordTrace_append hprefix tailTrace_2953953
  have hstable : (prefixWord ++ tailWord_2953953).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2953953).length < 2 ^ (prefixWord ++ tailWord_2953953).sum := by decide
  have hdescent : baseEnd_2953953 < baseStart_2953953 := by decide
  rcases family_descends (prefixWord ++ tailWord_2953953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2953981 : List Nat := [1, 4, 1, 1, 1, 1, 7, 6]
def baseStart_2953981 : Nat := 118140960795 + 2953981 * 2 ^ 59
def prefixEnd_2953981 : Nat := 4983230072969 + 3 ^ 40 * 2953981 * 2
def baseEnd_2953981 : Nat := 112356451648082390329807

theorem tailTrace_2953981 : CollatzResearch.WordTrace tailWord_2953981 prefixEnd_2953981 112356451648082390329807 := by
  unfold tailWord_2953981
  simp only [CollatzResearch.WordTrace]
  refine ⟨107740538311238811634629797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71827025540825874423086531 107740538311238811634629797)
  ·
    refine ⟨20201350933357277181493087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 107740538311238811634629797 20201350933357277181493087)
    ·
      refine ⟨30302026400035915772239631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20201350933357277181493087 30302026400035915772239631)
      ·
        refine ⟨45453039600053873658359447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30302026400035915772239631 45453039600053873658359447)
        ·
          refine ⟨68179559400080810487539171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45453039600053873658359447 68179559400080810487539171)
          ·
            refine ⟨102269339100121215731308757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68179559400080810487539171 102269339100121215731308757)
            ·
              refine ⟨2396937635159090993702549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 102269339100121215731308757 2396937635159090993702549)
              ·
                refine ⟨112356451648082390329807, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2396937635159090993702549 112356451648082390329807)
                ·
                  rfl

theorem cell22_2953981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 7, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 7, 6].length) (baseStart_2953981 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2953981 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2953981 prefixEnd_2953981 := by exact prefixLift 2953981
  have htrace : WordTrace (prefixWord ++ tailWord_2953981) baseStart_2953981 baseEnd_2953981 := by
    simpa [prefixWord, tailWord_2953981, baseEnd_2953981] using wordTrace_append hprefix tailTrace_2953981
  have hstable : (prefixWord ++ tailWord_2953981).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2953981).length < 2 ^ (prefixWord ++ tailWord_2953981).sum := by decide
  have hdescent : baseEnd_2953981 < baseStart_2953981 := by decide
  rcases family_descends (prefixWord ++ tailWord_2953981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2953996 : List Nat := [2, 2, 1, 2, 2, 1, 1, 1, 7, 3]
def baseStart_2953996 : Nat := 118140960795 + 2953996 * 2 ^ 59
def prefixEnd_2953996 : Nat := 4983230072969 + 3 ^ 40 * 2953996 * 2
def baseEnd_2953996 : Nat := 1011213199639286473843217

theorem tailTrace_2953996 : CollatzResearch.WordTrace tailWord_2953996 prefixEnd_2953996 1011213199639286473843217 := by
  unfold tailWord_2953996
  simp only [CollatzResearch.WordTrace]
  refine ⟨53870542703092234598212921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71827390270789646130950561 53870542703092234598212921)
  ·
    refine ⟨40402907027319175948659691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53870542703092234598212921 40402907027319175948659691)
    ·
      refine ⟨60604360540978763922989537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40402907027319175948659691 60604360540978763922989537)
      ·
        refine ⟨45453270405734072942242153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60604360540978763922989537 45453270405734072942242153)
        ·
          refine ⟨34089952804300554706681615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45453270405734072942242153 34089952804300554706681615)
          ·
            refine ⟨51134929206450832060022423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34089952804300554706681615 51134929206450832060022423)
            ·
              refine ⟨76702393809676248090033635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51134929206450832060022423 76702393809676248090033635)
              ·
                refine ⟨115053590714514372135050453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 76702393809676248090033635 115053590714514372135050453)
                ·
                  refine ⟨2696568532371430596915245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 115053590714514372135050453 2696568532371430596915245)
                  ·
                    refine ⟨1011213199639286473843217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2696568532371430596915245 1011213199639286473843217)
                    ·
                      rfl

theorem cell22_2953996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 1, 7, 3].length) (baseStart_2953996 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2953996 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2953996 prefixEnd_2953996 := by exact prefixLift 2953996
  have htrace : WordTrace (prefixWord ++ tailWord_2953996) baseStart_2953996 baseEnd_2953996 := by
    simpa [prefixWord, tailWord_2953996, baseEnd_2953996] using wordTrace_append hprefix tailTrace_2953996
  have hstable : (prefixWord ++ tailWord_2953996).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2953996).length < 2 ^ (prefixWord ++ tailWord_2953996).sum := by decide
  have hdescent : baseEnd_2953996 < baseStart_2953996 := by decide
  rcases family_descends (prefixWord ++ tailWord_2953996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2954030 : List Nat := [4, 1, 3, 2, 1, 1, 2, 2, 3, 3]
def baseStart_2954030 : Nat := 118140960795 + 2954030 * 2 ^ 59
def prefixEnd_2954030 : Nat := 4983230072969 + 3 ^ 40 * 2954030 * 2
def baseEnd_2954030 : Nat := 1011224838534121718493113

theorem tailTrace_2954030 : CollatzResearch.WordTrace tailWord_2954030 prefixEnd_2954030 1011224838534121718493113 := by
  unfold tailWord_2954030
  simp only [CollatzResearch.WordTrace]
  refine ⟨13467790686007661625395443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 71828216992040862002109029 13467790686007661625395443)
  ·
    refine ⟨20201686029011492438093165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13467790686007661625395443 20201686029011492438093165)
    ·
      refine ⟨7575632260879309664284937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20201686029011492438093165 7575632260879309664284937)
      ·
        refine ⟨5681724195659482248213703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7575632260879309664284937 5681724195659482248213703)
        ·
          refine ⟨8522586293489223372320555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5681724195659482248213703 8522586293489223372320555)
          ·
            refine ⟨12783879440233835058480833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8522586293489223372320555 12783879440233835058480833)
            ·
              refine ⟨9587909580175376293860625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12783879440233835058480833 9587909580175376293860625)
              ·
                refine ⟨7190932185131532220395469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9587909580175376293860625 7190932185131532220395469)
                ·
                  refine ⟨2696599569424324582648301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7190932185131532220395469 2696599569424324582648301)
                  ·
                    refine ⟨1011224838534121718493113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2696599569424324582648301 1011224838534121718493113)
                    ·
                      rfl

theorem cell22_2954030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 2, 2, 3, 3].length) (baseStart_2954030 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2954030 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2954030 prefixEnd_2954030 := by exact prefixLift 2954030
  have htrace : WordTrace (prefixWord ++ tailWord_2954030) baseStart_2954030 baseEnd_2954030 := by
    simpa [prefixWord, tailWord_2954030, baseEnd_2954030] using wordTrace_append hprefix tailTrace_2954030
  have hstable : (prefixWord ++ tailWord_2954030).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2954030).length < 2 ^ (prefixWord ++ tailWord_2954030).sum := by decide
  have hdescent : baseEnd_2954030 < baseStart_2954030 := by decide
  rcases family_descends (prefixWord ++ tailWord_2954030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2954047 : List Nat := [1, 1, 2, 2, 5, 3, 1, 3, 1, 3]
def baseStart_2954047 : Nat := 118140960795 + 2954047 * 2 ^ 59
def prefixEnd_2954047 : Nat := 4983230072969 + 3 ^ 40 * 2954047 * 2
def baseEnd_2954047 : Nat := 1011230657981539340818061

theorem tailTrace_2954047 : CollatzResearch.WordTrace tailWord_2954047 prefixEnd_2954047 1011230657981539340818061 := by
  unfold tailWord_2954047
  simp only [CollatzResearch.WordTrace]
  refine ⟨107742945528999704906532395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71828630352666469937688263 107742945528999704906532395)
  ·
    refine ⟨161614418293499557359798593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107742945528999704906532395 161614418293499557359798593)
    ·
      refine ⟨121210813720124668019848945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 161614418293499557359798593 121210813720124668019848945)
      ·
        refine ⟨90908110290093501014886709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 121210813720124668019848945 90908110290093501014886709)
        ·
          refine ⟨8522635339696265720145629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 90908110290093501014886709 8522635339696265720145629)
          ·
            refine ⟨3195988252386099645054611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8522635339696265720145629 3195988252386099645054611)
            ·
              refine ⟨4793982378579149467581917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3195988252386099645054611 4793982378579149467581917)
              ·
                refine ⟨1797743391967181050343219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4793982378579149467581917 1797743391967181050343219)
                ·
                  refine ⟨2696615087950771575514829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1797743391967181050343219 2696615087950771575514829)
                  ·
                    refine ⟨1011230657981539340818061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2696615087950771575514829 1011230657981539340818061)
                    ·
                      rfl

theorem cell22_2954047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 3, 1, 3, 1, 3].length) (baseStart_2954047 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2954047 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2954047 prefixEnd_2954047 := by exact prefixLift 2954047
  have htrace : WordTrace (prefixWord ++ tailWord_2954047) baseStart_2954047 baseEnd_2954047 := by
    simpa [prefixWord, tailWord_2954047, baseEnd_2954047] using wordTrace_append hprefix tailTrace_2954047
  have hstable : (prefixWord ++ tailWord_2954047).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2954047).length < 2 ^ (prefixWord ++ tailWord_2954047).sum := by decide
  have hdescent : baseEnd_2954047 < baseStart_2954047 := by decide
  rcases family_descends (prefixWord ++ tailWord_2954047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2954120 : List Nat := [2, 1, 3, 3, 2, 1, 1, 4, 2, 3]
def baseStart_2954120 : Nat := 118140960795 + 2954120 * 2 ^ 59
def prefixEnd_2954120 : Nat := 4983230072969 + 3 ^ 40 * 2954120 * 2
def baseEnd_2954120 : Nat := 1011255647373391483742837

theorem tailTrace_2954120 : CollatzResearch.WordTrace tailWord_2954120 prefixEnd_2954120 1011255647373391483742837 := by
  unfold tailWord_2954120
  simp only [CollatzResearch.WordTrace]
  refine ⟨53872804028867619186969907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71830405371823492249293209 53872804028867619186969907)
  ·
    refine ⟨80809206043301428780454861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53872804028867619186969907 80809206043301428780454861)
    ·
      refine ⟨30303452266238035792670573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 80809206043301428780454861 30303452266238035792670573)
      ·
        refine ⟨11363794599839263422251465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30303452266238035792670573 11363794599839263422251465)
        ·
          refine ⟨8522845949879447566688599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11363794599839263422251465 8522845949879447566688599)
          ·
            refine ⟨12784268924819171350032899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8522845949879447566688599 12784268924819171350032899)
            ·
              refine ⟨19176403387228757025049349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12784268924819171350032899 19176403387228757025049349)
              ·
                refine ⟨3595575635105391942196753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19176403387228757025049349 3595575635105391942196753)
                ·
                  refine ⟨2696681726329043956647565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3595575635105391942196753 2696681726329043956647565)
                  ·
                    refine ⟨1011255647373391483742837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2696681726329043956647565 1011255647373391483742837)
                    ·
                      rfl

theorem cell22_2954120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 1, 4, 2, 3].length) (baseStart_2954120 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2954120 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2954120 prefixEnd_2954120 := by exact prefixLift 2954120
  have htrace : WordTrace (prefixWord ++ tailWord_2954120) baseStart_2954120 baseEnd_2954120 := by
    simpa [prefixWord, tailWord_2954120, baseEnd_2954120] using wordTrace_append hprefix tailTrace_2954120
  have hstable : (prefixWord ++ tailWord_2954120).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2954120).length < 2 ^ (prefixWord ++ tailWord_2954120).sum := by decide
  have hdescent : baseEnd_2954120 < baseStart_2954120 := by decide
  rcases family_descends (prefixWord ++ tailWord_2954120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2954122 : List Nat := [3, 1, 2, 4, 1, 1, 4, 2, 4]
def baseStart_2954122 : Nat := 118140960795 + 2954122 * 2 ^ 59
def prefixEnd_2954122 : Nat := 4983230072969 + 3 ^ 40 * 2954122 * 2
def baseEnd_2954122 : Nat := 337085444004754715064277

theorem tailTrace_2954122 : CollatzResearch.WordTrace tailWord_2954122 prefixEnd_2954122 337085444004754715064277 := by
  unfold tailWord_2954122
  simp only [CollatzResearch.WordTrace]
  refine ⟨26936420250931998178878155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71830454002485328477008413 26936420250931998178878155)
  ·
    refine ⟨40404630376397997268317233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26936420250931998178878155 40404630376397997268317233)
    ·
      refine ⟨30303472782298497951237925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40404630376397997268317233 30303472782298497951237925)
      ·
        refine ⟨5681901146680968365857111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 30303472782298497951237925 5681901146680968365857111)
        ·
          refine ⟨8522851720021452548785667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5681901146680968365857111 8522851720021452548785667)
          ·
            refine ⟨12784277580032178823178501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8522851720021452548785667 12784277580032178823178501)
            ·
              refine ⟨2397052046256033529345969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12784277580032178823178501 2397052046256033529345969)
              ·
                refine ⟨1797789034692025147009477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2397052046256033529345969 1797789034692025147009477)
                ·
                  refine ⟨337085444004754715064277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1797789034692025147009477 337085444004754715064277)
                  ·
                    rfl

theorem cell22_2954122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 4, 2, 4].length) (baseStart_2954122 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2954122 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2954122 prefixEnd_2954122 := by exact prefixLift 2954122
  have htrace : WordTrace (prefixWord ++ tailWord_2954122) baseStart_2954122 baseEnd_2954122 := by
    simpa [prefixWord, tailWord_2954122, baseEnd_2954122] using wordTrace_append hprefix tailTrace_2954122
  have hstable : (prefixWord ++ tailWord_2954122).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2954122).length < 2 ^ (prefixWord ++ tailWord_2954122).sum := by decide
  have hdescent : baseEnd_2954122 < baseStart_2954122 := by decide
  rcases family_descends (prefixWord ++ tailWord_2954122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2954133 : List Nat := [1, 3, 2, 1, 1, 6, 1, 7]
def baseStart_2954133 : Nat := 118140960795 + 2954133 * 2 ^ 59
def prefixEnd_2954133 : Nat := 4983230072969 + 3 ^ 40 * 2954133 * 2
def baseEnd_2954133 : Nat := 112362233059895975907533

theorem tailTrace_2954133 : CollatzResearch.WordTrace tailWord_2954133 prefixEnd_2954133 112362233059895975907533 := by
  unfold tailWord_2954133
  simp only [CollatzResearch.WordTrace]
  refine ⟨107746082206688141594163053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71830721471125427729442035 107746082206688141594163053)
  ·
    refine ⟨40404780827508053097811145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 107746082206688141594163053 40404780827508053097811145)
    ·
      refine ⟨30303585620631039823358359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40404780827508053097811145 30303585620631039823358359)
      ·
        refine ⟨45455378430946559735037539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30303585620631039823358359 45455378430946559735037539)
        ·
          refine ⟨68183067646419839602556309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45455378430946559735037539 68183067646419839602556309)
          ·
            refine ⟨3196081295925929981369827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 68183067646419839602556309 3196081295925929981369827)
            ·
              refine ⟨4794121943888894972054741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3196081295925929981369827 4794121943888894972054741)
              ·
                refine ⟨112362233059895975907533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4794121943888894972054741 112362233059895975907533)
                ·
                  rfl

theorem cell22_2954133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 6, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 6, 1, 7].length) (baseStart_2954133 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2954133 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2954133 prefixEnd_2954133 := by exact prefixLift 2954133
  have htrace : WordTrace (prefixWord ++ tailWord_2954133) baseStart_2954133 baseEnd_2954133 := by
    simpa [prefixWord, tailWord_2954133, baseEnd_2954133] using wordTrace_append hprefix tailTrace_2954133
  have hstable : (prefixWord ++ tailWord_2954133).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2954133).length < 2 ^ (prefixWord ++ tailWord_2954133).sum := by decide
  have hdescent : baseEnd_2954133 < baseStart_2954133 := by decide
  rcases family_descends (prefixWord ++ tailWord_2954133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2954225 : List Nat := [1, 2, 2, 2, 4, 1, 2, 3, 1, 4]
def baseStart_2954225 : Nat := 118140960795 + 2954225 * 2 ^ 59
def prefixEnd_2954225 : Nat := 4983230072969 + 3 ^ 40 * 2954225 * 2
def baseEnd_2954225 : Nat := 1011291591019206209867515

theorem tailTrace_2954225 : CollatzResearch.WordTrace tailWord_2954225 prefixEnd_2954225 1011291591019206209867515 := by
  unfold tailWord_2954225
  simp only [CollatzResearch.WordTrace]
  refine ⟨107749437722354841306512129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71832958481569894204341419 107749437722354841306512129)
  ·
    refine ⟨80812078291766130979884097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107749437722354841306512129 80812078291766130979884097)
    ·
      refine ⟨60609058718824598234913073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80812078291766130979884097 60609058718824598234913073)
      ·
        refine ⟨45456794039118448676184805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60609058718824598234913073 45456794039118448676184805)
        ·
          refine ⟨8523148882334709126784651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 45456794039118448676184805 8523148882334709126784651)
          ·
            refine ⟨12784723323502063690176977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8523148882334709126784651 12784723323502063690176977)
            ·
              refine ⟨9588542492626547767632733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12784723323502063690176977 9588542492626547767632733)
              ·
                refine ⟨3595703434734955412862275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9588542492626547767632733 3595703434734955412862275)
                ·
                  refine ⟨5393555152102433119293413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3595703434734955412862275 5393555152102433119293413)
                  ·
                    refine ⟨1011291591019206209867515, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5393555152102433119293413 1011291591019206209867515)
                    ·
                      rfl

theorem cell22_2954225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 2, 3, 1, 4].length) (baseStart_2954225 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2954225 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2954225 prefixEnd_2954225 := by exact prefixLift 2954225
  have htrace : WordTrace (prefixWord ++ tailWord_2954225) baseStart_2954225 baseEnd_2954225 := by
    simpa [prefixWord, tailWord_2954225, baseEnd_2954225] using wordTrace_append hprefix tailTrace_2954225
  have hstable : (prefixWord ++ tailWord_2954225).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2954225).length < 2 ^ (prefixWord ++ tailWord_2954225).sum := by decide
  have hdescent : baseEnd_2954225 < baseStart_2954225 := by decide
  rcases family_descends (prefixWord ++ tailWord_2954225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2954272 : List Nat := [2, 1, 1, 7, 1, 1, 1, 2, 1, 5]
def baseStart_2954272 : Nat := 118140960795 + 2954272 * 2 ^ 59
def prefixEnd_2954272 : Nat := 4983230072969 + 3 ^ 40 * 2954272 * 2
def baseEnd_2954272 : Nat := 1011307680079713753942371

theorem tailTrace_2954272 : CollatzResearch.WordTrace tailWord_2954272 prefixEnd_2954272 1011307680079713753942371 := by
  unfold tailWord_2954272
  simp only [CollatzResearch.WordTrace]
  refine ⟨53875575976592284166736535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71834101302123045555648713 53875575976592284166736535)
  ·
    refine ⟨80813363964888426250104803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53875575976592284166736535 80813363964888426250104803)
    ·
      refine ⟨121220045947332639375157205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80813363964888426250104803 121220045947332639375157205)
      ·
        refine ⟨2841094826890608735355247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 121220045947332639375157205 2841094826890608735355247)
        ·
          refine ⟨4261642240335913103032871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2841094826890608735355247 4261642240335913103032871)
          ·
            refine ⟨6392463360503869654549307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4261642240335913103032871 6392463360503869654549307)
            ·
              refine ⟨9588695040755804481823961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6392463360503869654549307 9588695040755804481823961)
              ·
                refine ⟨7191521280566853361367971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9588695040755804481823961 7191521280566853361367971)
                ·
                  refine ⟨10787281920850280042051957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7191521280566853361367971 10787281920850280042051957)
                  ·
                    refine ⟨1011307680079713753942371, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10787281920850280042051957 1011307680079713753942371)
                    ·
                      rfl

theorem cell22_2954272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 1, 1, 2, 1, 5].length) (baseStart_2954272 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2954272 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2954272 prefixEnd_2954272 := by exact prefixLift 2954272
  have htrace : WordTrace (prefixWord ++ tailWord_2954272) baseStart_2954272 baseEnd_2954272 := by
    simpa [prefixWord, tailWord_2954272, baseEnd_2954272] using wordTrace_append hprefix tailTrace_2954272
  have hstable : (prefixWord ++ tailWord_2954272).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2954272).length < 2 ^ (prefixWord ++ tailWord_2954272).sum := by decide
  have hdescent : baseEnd_2954272 < baseStart_2954272 := by decide
  rcases family_descends (prefixWord ++ tailWord_2954272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2954298 : List Nat := [3, 1, 1, 1, 3, 1, 3, 1, 2, 6]
def baseStart_2954298 : Nat := 118140960795 + 2954298 * 2 ^ 59
def prefixEnd_2954298 : Nat := 4983230072969 + 3 ^ 40 * 2954298 * 2
def baseEnd_2954298 : Nat := 1011316580411058352792291

theorem tailTrace_2954298 : CollatzResearch.WordTrace tailWord_2954298 prefixEnd_2954298 1011316580411058352792291 := by
  unfold tailWord_2954298
  simp only [CollatzResearch.WordTrace]
  refine ⟨26938025062772593693479887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71834733500726916515946365 26938025062772593693479887)
  ·
    refine ⟨40407037594158890540219831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26938025062772593693479887 40407037594158890540219831)
    ·
      refine ⟨60610556391238335810329747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40407037594158890540219831 60610556391238335810329747)
      ·
        refine ⟨90915834586857503715494621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60610556391238335810329747 90915834586857503715494621)
        ·
          refine ⟨34093437970071563893310483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 90915834586857503715494621 34093437970071563893310483)
          ·
            refine ⟨51140156955107345839965725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34093437970071563893310483 51140156955107345839965725)
            ·
              refine ⟨19177558858165254689987147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 51140156955107345839965725 19177558858165254689987147)
              ·
                refine ⟨28766338287247882034980721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19177558858165254689987147 28766338287247882034980721)
                ·
                  refine ⟨21574753715435911526235541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28766338287247882034980721 21574753715435911526235541)
                  ·
                    refine ⟨1011316580411058352792291, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21574753715435911526235541 1011316580411058352792291)
                    ·
                      rfl

theorem cell22_2954298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 3, 1, 2, 6].length) (baseStart_2954298 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2954298 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2954298 prefixEnd_2954298 := by exact prefixLift 2954298
  have htrace : WordTrace (prefixWord ++ tailWord_2954298) baseStart_2954298 baseEnd_2954298 := by
    simpa [prefixWord, tailWord_2954298, baseEnd_2954298] using wordTrace_append hprefix tailTrace_2954298
  have hstable : (prefixWord ++ tailWord_2954298).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2954298).length < 2 ^ (prefixWord ++ tailWord_2954298).sum := by decide
  have hdescent : baseEnd_2954298 < baseStart_2954298 := by decide
  rcases family_descends (prefixWord ++ tailWord_2954298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2954302 : List Nat := [4, 2, 1, 3, 1, 3, 1, 7]
def baseStart_2954302 : Nat := 118140960795 + 2954302 * 2 ^ 59
def prefixEnd_2954302 : Nat := 4983230072969 + 3 ^ 40 * 2954302 * 2
def baseEnd_2954302 : Nat := 112368661076978186188031

theorem tailTrace_2954302 : CollatzResearch.WordTrace tailWord_2954302 prefixEnd_2954302 112368661076978186188031 := by
  unfold tailWord_2954302
  simp only [CollatzResearch.WordTrace]
  refine ⟨13469030767884485432133145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 71834830762050588971376773 13469030767884485432133145)
  ·
    refine ⟨10101773075913364074099859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13469030767884485432133145 10101773075913364074099859)
    ·
      refine ⟨15152659613870046111149789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10101773075913364074099859 15152659613870046111149789)
      ·
        refine ⟨5682247355201267291681171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15152659613870046111149789 5682247355201267291681171)
        ·
          refine ⟨8523371032801900937521757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5682247355201267291681171 8523371032801900937521757)
          ·
            refine ⟨3196264137300712851570659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8523371032801900937521757 3196264137300712851570659)
            ·
              refine ⟨4794396205951069277355989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3196264137300712851570659 4794396205951069277355989)
              ·
                refine ⟨112368661076978186188031, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4794396205951069277355989 112368661076978186188031)
                ·
                  rfl

theorem cell22_2954302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 3, 1, 7].length) (baseStart_2954302 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2954302 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2954302 prefixEnd_2954302 := by exact prefixLift 2954302
  have htrace : WordTrace (prefixWord ++ tailWord_2954302) baseStart_2954302 baseEnd_2954302 := by
    simpa [prefixWord, tailWord_2954302, baseEnd_2954302] using wordTrace_append hprefix tailTrace_2954302
  have hstable : (prefixWord ++ tailWord_2954302).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2954302).length < 2 ^ (prefixWord ++ tailWord_2954302).sum := by decide
  have hdescent : baseEnd_2954302 < baseStart_2954302 := by decide
  rcases family_descends (prefixWord ++ tailWord_2954302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2954317 : List Nat := [1, 6, 1, 1, 1, 2, 1, 1, 5, 3]
def baseStart_2954317 : Nat := 118140960795 + 2954317 * 2 ^ 59
def prefixEnd_2954317 : Nat := 4983230072969 + 3 ^ 40 * 2954317 * 2
def baseEnd_2954317 : Nat := 1011323084499348636567233

theorem tailTrace_2954317 : CollatzResearch.WordTrace tailWord_2954317 prefixEnd_2954317 1011323084499348636567233 := by
  unfold tailWord_2954317
  simp only [CollatzResearch.WordTrace]
  refine ⟨107752793238021541018861205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71835195492014360679240803 107752793238021541018861205)
  ·
    refine ⟨5050912183032259735259119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 107752793238021541018861205 5050912183032259735259119)
    ·
      refine ⟨7576368274548389602888679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5050912183032259735259119 7576368274548389602888679)
      ·
        refine ⟨11364552411822584404333019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7576368274548389602888679 11364552411822584404333019)
        ·
          refine ⟨17046828617733876606499529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11364552411822584404333019 17046828617733876606499529)
          ·
            refine ⟨12785121463300407454874647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17046828617733876606499529 12785121463300407454874647)
            ·
              refine ⟨19177682194950611182311971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12785121463300407454874647 19177682194950611182311971)
              ·
                refine ⟨28766523292425916773467957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19177682194950611182311971 28766523292425916773467957)
                ·
                  refine ⟨2696861558664929697512621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 28766523292425916773467957 2696861558664929697512621)
                  ·
                    refine ⟨1011323084499348636567233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2696861558664929697512621 1011323084499348636567233)
                    ·
                      rfl

theorem cell22_2954317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 1, 1, 5, 3].length) (baseStart_2954317 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2954317 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2954317 prefixEnd_2954317 := by exact prefixLift 2954317
  have htrace : WordTrace (prefixWord ++ tailWord_2954317) baseStart_2954317 baseEnd_2954317 := by
    simpa [prefixWord, tailWord_2954317, baseEnd_2954317] using wordTrace_append hprefix tailTrace_2954317
  have hstable : (prefixWord ++ tailWord_2954317).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2954317).length < 2 ^ (prefixWord ++ tailWord_2954317).sum := by decide
  have hdescent : baseEnd_2954317 < baseStart_2954317 := by decide
  rcases family_descends (prefixWord ++ tailWord_2954317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2954328 : List Nat := [2, 1, 2, 2, 1, 3, 1, 2, 1, 7]
def baseStart_2954328 : Nat := 118140960795 + 2954328 * 2 ^ 59
def prefixEnd_2954328 : Nat := 4983230072969 + 3 ^ 40 * 2954328 * 2
def baseEnd_2954328 : Nat := 1011326850024148274542199

theorem tailTrace_2954328 : CollatzResearch.WordTrace tailWord_2954328 prefixEnd_2954328 1011326850024148274542199 := by
  unfold tailWord_2954328
  simp only [CollatzResearch.WordTrace]
  refine ⟨53876597220490844948755819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71835462960654459931674425 53876597220490844948755819)
  ·
    refine ⟨80814895830736267423133729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53876597220490844948755819 80814895830736267423133729)
    ·
      refine ⟨60611171873052200567350297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80814895830736267423133729 60611171873052200567350297)
      ·
        refine ⟨45458378904789150425512723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60611171873052200567350297 45458378904789150425512723)
        ·
          refine ⟨68187568357183725638269085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45458378904789150425512723 68187568357183725638269085)
          ·
            refine ⟨25570338133943897114350907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 68187568357183725638269085 25570338133943897114350907)
            ·
              refine ⟨38355507200915845671526361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25570338133943897114350907 38355507200915845671526361)
              ·
                refine ⟨28766630400686884253644771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38355507200915845671526361 28766630400686884253644771)
                ·
                  refine ⟨43149945601030326380467157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28766630400686884253644771 43149945601030326380467157)
                  ·
                    refine ⟨1011326850024148274542199, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 43149945601030326380467157 1011326850024148274542199)
                    ·
                      rfl

theorem cell22_2954328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 1, 2, 1, 7].length) (baseStart_2954328 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2954328 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2954328 prefixEnd_2954328 := by exact prefixLift 2954328
  have htrace : WordTrace (prefixWord ++ tailWord_2954328) baseStart_2954328 baseEnd_2954328 := by
    simpa [prefixWord, tailWord_2954328, baseEnd_2954328] using wordTrace_append hprefix tailTrace_2954328
  have hstable : (prefixWord ++ tailWord_2954328).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2954328).length < 2 ^ (prefixWord ++ tailWord_2954328).sum := by decide
  have hdescent : baseEnd_2954328 < baseStart_2954328 := by decide
  rcases family_descends (prefixWord ++ tailWord_2954328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2954377 : List Nat := [1, 2, 1, 1, 4, 4, 2, 2, 1, 4]
def baseStart_2954377 : Nat := 118140960795 + 2954377 * 2 ^ 59
def prefixEnd_2954377 : Nat := 4983230072969 + 3 ^ 40 * 2954377 * 2
def baseEnd_2954377 : Nat := 1011343623725528480067049

theorem tailTrace_2954377 : CollatzResearch.WordTrace tailWord_2954377 prefixEnd_2954377 1011343623725528480067049 := by
  unfold tailWord_2954377
  simp only [CollatzResearch.WordTrace]
  refine ⟨107754981617804171266045385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71836654411869447510696923 107754981617804171266045385)
  ·
    refine ⟨80816236213353128449534039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107754981617804171266045385 80816236213353128449534039)
    ·
      refine ⟨121224354320029692674301059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80816236213353128449534039 121224354320029692674301059)
      ·
        refine ⟨181836531480044539011451589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121224354320029692674301059 181836531480044539011451589)
        ·
          refine ⟨34094349652508351064647173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 181836531480044539011451589 34094349652508351064647173)
          ·
            refine ⟨6392690559845315824621345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 34094349652508351064647173 6392690559845315824621345)
            ·
              refine ⟨4794517919883986868466009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6392690559845315824621345 4794517919883986868466009)
              ·
                refine ⟨3595888439912990151349507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4794517919883986868466009 3595888439912990151349507)
                ·
                  refine ⟨5393832659869485227024261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3595888439912990151349507 5393832659869485227024261)
                  ·
                    refine ⟨1011343623725528480067049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5393832659869485227024261 1011343623725528480067049)
                    ·
                      rfl

theorem cell22_2954377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 4, 2, 2, 1, 4].length) (baseStart_2954377 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2954377 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2954377 prefixEnd_2954377 := by exact prefixLift 2954377
  have htrace : WordTrace (prefixWord ++ tailWord_2954377) baseStart_2954377 baseEnd_2954377 := by
    simpa [prefixWord, tailWord_2954377, baseEnd_2954377] using wordTrace_append hprefix tailTrace_2954377
  have hstable : (prefixWord ++ tailWord_2954377).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2954377).length < 2 ^ (prefixWord ++ tailWord_2954377).sum := by decide
  have hdescent : baseEnd_2954377 < baseStart_2954377 := by decide
  rcases family_descends (prefixWord ++ tailWord_2954377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2954405 : List Nat := [1, 3, 1, 2, 1, 4, 1, 1, 4, 4]
def baseStart_2954405 : Nat := 118140960795 + 2954405 * 2 ^ 59
def prefixEnd_2954405 : Nat := 4983230072969 + 3 ^ 40 * 2954405 * 2
def baseEnd_2954405 : Nat := 1011353208697745740366963

theorem tailTrace_2954405 : CollatzResearch.WordTrace tailWord_2954405 prefixEnd_2954405 1011353208697745740366963 := by
  unfold tailWord_2954405
  simp only [CollatzResearch.WordTrace]
  refine ⟨107756002861702732048064669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71837335241135154698709779 107756002861702732048064669)
  ·
    refine ⟨40408501073138524518024251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 107756002861702732048064669 40408501073138524518024251)
    ·
      refine ⟨60612751609707786777036377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40408501073138524518024251 60612751609707786777036377)
      ·
        refine ⟨45459563707280840082777283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60612751609707786777036377 45459563707280840082777283)
        ·
          refine ⟨68189345560921260124165925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45459563707280840082777283 68189345560921260124165925)
          ·
            refine ⟨12785502292672736273281111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 68189345560921260124165925 12785502292672736273281111)
            ·
              refine ⟨19178253439009104409921667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12785502292672736273281111 19178253439009104409921667)
              ·
                refine ⟨28767380158513656614882501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19178253439009104409921667 28767380158513656614882501)
                ·
                  refine ⟨5393883779721310615290469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28767380158513656614882501 5393883779721310615290469)
                  ·
                    refine ⟨1011353208697745740366963, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5393883779721310615290469 1011353208697745740366963)
                    ·
                      rfl

theorem cell22_2954405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 1, 1, 4, 4].length) (baseStart_2954405 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2954405 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2954405 prefixEnd_2954405 := by exact prefixLift 2954405
  have htrace : WordTrace (prefixWord ++ tailWord_2954405) baseStart_2954405 baseEnd_2954405 := by
    simpa [prefixWord, tailWord_2954405, baseEnd_2954405] using wordTrace_append hprefix tailTrace_2954405
  have hstable : (prefixWord ++ tailWord_2954405).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2954405).length < 2 ^ (prefixWord ++ tailWord_2954405).sum := by decide
  have hdescent : baseEnd_2954405 < baseStart_2954405 := by decide
  rcases family_descends (prefixWord ++ tailWord_2954405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2954454 : List Nat := [5, 2, 1, 2, 3, 9]
def baseStart_2954454 : Nat := 118140960795 + 2954454 * 2 ^ 59
def prefixEnd_2954454 : Nat := 4983230072969 + 3 ^ 40 * 2954454 * 2
def baseEnd_2954454 : Nat := 12486049165421307973973

theorem tailTrace_2954454 : CollatzResearch.WordTrace tailWord_2954454 prefixEnd_2954454 12486049165421307973973 := by
  unfold tailWord_2954454
  simp only [CollatzResearch.WordTrace]
  refine ⟨6734861877407825838537401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 71838526692350142277732277 6734861877407825838537401)
  ·
    refine ⟨5051146408055869378903051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6734861877407825838537401 5051146408055869378903051)
    ·
      refine ⟨7576719612083804068354577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5051146408055869378903051 7576719612083804068354577)
      ·
        refine ⟨5682539709062853051265933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7576719612083804068354577 5682539709062853051265933)
        ·
          refine ⟨2130952390898569894224725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5682539709062853051265933 2130952390898569894224725)
          ·
            refine ⟨12486049165421307973973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 2130952390898569894224725 12486049165421307973973)
            ·
              rfl

theorem cell22_2954454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 3, 9].length) (baseStart_2954454 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2954454 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2954454 prefixEnd_2954454 := by exact prefixLift 2954454
  have htrace : WordTrace (prefixWord ++ tailWord_2954454) baseStart_2954454 baseEnd_2954454 := by
    simpa [prefixWord, tailWord_2954454, baseEnd_2954454] using wordTrace_append hprefix tailTrace_2954454
  have hstable : (prefixWord ++ tailWord_2954454).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2954454).length < 2 ^ (prefixWord ++ tailWord_2954454).sum := by decide
  have hdescent : baseEnd_2954454 < baseStart_2954454 := by decide
  rcases family_descends (prefixWord ++ tailWord_2954454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2954561 : List Nat := [1, 2, 5, 2, 1, 1, 3, 3, 4]
def baseStart_2954561 : Nat := 118140960795 + 2954561 * 2 ^ 59
def prefixEnd_2954561 : Nat := 4983230072969 + 3 ^ 40 * 2954561 * 2
def baseEnd_2954561 : Nat := 337135536895271111155495

theorem tailTrace_2954561 : CollatzResearch.WordTrace tailWord_2954561 prefixEnd_2954561 337135536895271111155495 := by
  unfold tailWord_2954561
  simp only [CollatzResearch.WordTrace]
  refine ⟨107761692649137570690743537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71841128432758380460495691 107761692649137570690743537)
  ·
    refine ⟨80821269486853178018057653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107761692649137570690743537 80821269486853178018057653)
    ·
      refine ⟨7576994014392485439192905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 80821269486853178018057653 7576994014392485439192905)
      ·
        refine ⟨5682745510794364079394679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7576994014392485439192905 5682745510794364079394679)
        ·
          refine ⟨8524118266191546119092019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5682745510794364079394679 8524118266191546119092019)
          ·
            refine ⟨12786177399287319178638029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8524118266191546119092019 12786177399287319178638029)
            ·
              refine ⟨4794816524732744691989261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12786177399287319178638029 4794816524732744691989261)
              ·
                refine ⟨1798056196774779259495973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4794816524732744691989261 1798056196774779259495973)
                ·
                  refine ⟨337135536895271111155495, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1798056196774779259495973 337135536895271111155495)
                  ·
                    rfl

theorem cell22_2954561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 3, 3, 4].length) (baseStart_2954561 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2954561 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2954561 prefixEnd_2954561 := by exact prefixLift 2954561
  have htrace : WordTrace (prefixWord ++ tailWord_2954561) baseStart_2954561 baseEnd_2954561 := by
    simpa [prefixWord, tailWord_2954561, baseEnd_2954561] using wordTrace_append hprefix tailTrace_2954561
  have hstable : (prefixWord ++ tailWord_2954561).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2954561).length < 2 ^ (prefixWord ++ tailWord_2954561).sum := by decide
  have hdescent : baseEnd_2954561 < baseStart_2954561 := by decide
  rcases family_descends (prefixWord ++ tailWord_2954561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2954572 : List Nat := [2, 2, 1, 3, 2, 4, 8]
def baseStart_2954572 : Nat := 118140960795 + 2954572 * 2 ^ 59
def prefixEnd_2954572 : Nat := 4983230072969 + 3 ^ 40 * 2954572 * 2
def baseEnd_2954572 : Nat := 37459643563356035979313

theorem tailTrace_2954572 : CollatzResearch.WordTrace tailWord_2954572 prefixEnd_2954572 37459643563356035979313 := by
  unfold tailWord_2954572
  simp only [CollatzResearch.WordTrace]
  refine ⟨53881046926048859784696985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71841395901398479712929313 53881046926048859784696985)
  ·
    refine ⟨40410785194536644838522739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53881046926048859784696985 40410785194536644838522739)
    ·
      refine ⟨60616177791804967257784109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40410785194536644838522739 60616177791804967257784109)
      ·
        refine ⟨22731066671926862721669041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 60616177791804967257784109 22731066671926862721669041)
        ·
          refine ⟨17048300003945147041251781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22731066671926862721669041 17048300003945147041251781)
          ·
            refine ⟨3196556250739715070234709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17048300003945147041251781 3196556250739715070234709)
            ·
              refine ⟨37459643563356035979313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3196556250739715070234709 37459643563356035979313)
              ·
                rfl

theorem cell22_2954572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 4, 8].length) (baseStart_2954572 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2954572 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2954572 prefixEnd_2954572 := by exact prefixLift 2954572
  have htrace : WordTrace (prefixWord ++ tailWord_2954572) baseStart_2954572 baseEnd_2954572 := by
    simpa [prefixWord, tailWord_2954572, baseEnd_2954572] using wordTrace_append hprefix tailTrace_2954572
  have hstable : (prefixWord ++ tailWord_2954572).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2954572).length < 2 ^ (prefixWord ++ tailWord_2954572).sum := by decide
  have hdescent : baseEnd_2954572 < baseStart_2954572 := by decide
  rcases family_descends (prefixWord ++ tailWord_2954572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2954621 : List Nat := [1, 4, 1, 1, 2, 2, 2, 5, 1, 3]
def baseStart_2954621 : Nat := 118140960795 + 2954621 * 2 ^ 59
def prefixEnd_2954621 : Nat := 4983230072969 + 3 ^ 40 * 2954621 * 2
def baseEnd_2954621 : Nat := 1011427149911993176966301

theorem tailTrace_2954621 : CollatzResearch.WordTrace tailWord_2954621 prefixEnd_2954621 1011427149911993176966301 := by
  unfold tailWord_2954621
  simp only [CollatzResearch.WordTrace]
  refine ⟨107763881028920200937927717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71842587352613467291951811 107763881028920200937927717)
  ·
    refine ⟨20205727692922537675861447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 107763881028920200937927717 20205727692922537675861447)
    ·
      refine ⟨30308591539383806513792171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20205727692922537675861447 30308591539383806513792171)
      ·
        refine ⟨45462887309075709770688257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30308591539383806513792171 45462887309075709770688257)
        ·
          refine ⟨34097165481806782328016193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45462887309075709770688257 34097165481806782328016193)
          ·
            refine ⟨25572874111355086746012145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34097165481806782328016193 25572874111355086746012145)
            ·
              refine ⟨19179655583516315059509109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25572874111355086746012145 19179655583516315059509109)
              ·
                refine ⟨1798092710954654536828979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 19179655583516315059509109 1798092710954654536828979)
                ·
                  refine ⟨2697139066431981805243469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1798092710954654536828979 2697139066431981805243469)
                  ·
                    refine ⟨1011427149911993176966301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2697139066431981805243469 1011427149911993176966301)
                    ·
                      rfl

theorem cell22_2954621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 2, 5, 1, 3].length) (baseStart_2954621 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2954621 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2954621 prefixEnd_2954621 := by exact prefixLift 2954621
  have htrace : WordTrace (prefixWord ++ tailWord_2954621) baseStart_2954621 baseEnd_2954621 := by
    simpa [prefixWord, tailWord_2954621, baseEnd_2954621] using wordTrace_append hprefix tailTrace_2954621
  have hstable : (prefixWord ++ tailWord_2954621).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2954621).length < 2 ^ (prefixWord ++ tailWord_2954621).sum := by decide
  have hdescent : baseEnd_2954621 < baseStart_2954621 := by decide
  rcases family_descends (prefixWord ++ tailWord_2954621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2954681 : List Nat := [1, 2, 1, 4, 4, 1, 1, 3, 1, 4]
def baseStart_2954681 : Nat := 118140960795 + 2954681 * 2 ^ 59
def prefixEnd_2954681 : Nat := 4983230072969 + 3 ^ 40 * 2954681 * 2
def baseEnd_2954681 : Nat := 1011447689138173020466117

theorem tailTrace_2954681 : CollatzResearch.WordTrace tailWord_2954681 prefixEnd_2954681 1011447689138173020466117 := by
  unfold tailWord_2954681
  simp only [CollatzResearch.WordTrace]
  refine ⟨107766069408702831185111897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71844046272468554123407931 107766069408702831185111897)
  ·
    refine ⟨80824552056527123388833923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107766069408702831185111897 80824552056527123388833923)
    ·
      refine ⟨121236828084790685083250885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80824552056527123388833923 121236828084790685083250885)
      ·
        refine ⟨22731905265898253453109541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 121236828084790685083250885 22731905265898253453109541)
        ·
          refine ⟨4262232237355922522458039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22731905265898253453109541 4262232237355922522458039)
          ·
            refine ⟨6393348356033883783687059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4262232237355922522458039 6393348356033883783687059)
            ·
              refine ⟨9590022534050825675530589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6393348356033883783687059 9590022534050825675530589)
              ·
                refine ⟨3596258450269059628323971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9590022534050825675530589 3596258450269059628323971)
                ·
                  refine ⟨5394387675403589442485957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3596258450269059628323971 5394387675403589442485957)
                  ·
                    refine ⟨1011447689138173020466117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5394387675403589442485957 1011447689138173020466117)
                    ·
                      rfl

theorem cell22_2954681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 1, 1, 3, 1, 4].length) (baseStart_2954681 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2954681 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2954681 prefixEnd_2954681 := by exact prefixLift 2954681
  have htrace : WordTrace (prefixWord ++ tailWord_2954681) baseStart_2954681 baseEnd_2954681 := by
    simpa [prefixWord, tailWord_2954681, baseEnd_2954681] using wordTrace_append hprefix tailTrace_2954681
  have hstable : (prefixWord ++ tailWord_2954681).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2954681).length < 2 ^ (prefixWord ++ tailWord_2954681).sum := by decide
  have hdescent : baseEnd_2954681 < baseStart_2954681 := by decide
  rcases family_descends (prefixWord ++ tailWord_2954681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2954730 : List Nat := [3, 1, 3, 1, 5, 1, 1, 3, 4]
def baseStart_2954730 : Nat := 118140960795 + 2954730 * 2 ^ 59
def prefixEnd_2954730 : Nat := 4983230072969 + 3 ^ 40 * 2954730 * 2
def baseEnd_2954730 : Nat := 337154820946517741996989

theorem tailTrace_2954730 : CollatzResearch.WordTrace tailWord_2954730 prefixEnd_2954730 337154820946517741996989 := by
  unfold tailWord_2954730
  simp only [CollatzResearch.WordTrace]
  refine ⟨26941964146381328138411411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71845237723683541702430429 26941964146381328138411411)
  ·
    refine ⟨40412946219571992207617117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26941964146381328138411411 40412946219571992207617117)
    ·
      refine ⟨15154854832339497077856419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40412946219571992207617117 15154854832339497077856419)
      ·
        refine ⟨22732282248509245616784629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15154854832339497077856419 22732282248509245616784629)
        ·
          refine ⟨2131151460797741776573559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 22732282248509245616784629 2131151460797741776573559)
          ·
            refine ⟨3196727191196612664860339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2131151460797741776573559 3196727191196612664860339)
            ·
              refine ⟨4795090786794918997290509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3196727191196612664860339 4795090786794918997290509)
              ·
                refine ⟨1798159045048094623983941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4795090786794918997290509 1798159045048094623983941)
                ·
                  refine ⟨337154820946517741996989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1798159045048094623983941 337154820946517741996989)
                  ·
                    rfl

theorem cell22_2954730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 5, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 5, 1, 1, 3, 4].length) (baseStart_2954730 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2954730 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2954730 prefixEnd_2954730 := by exact prefixLift 2954730
  have htrace : WordTrace (prefixWord ++ tailWord_2954730) baseStart_2954730 baseEnd_2954730 := by
    simpa [prefixWord, tailWord_2954730, baseEnd_2954730] using wordTrace_append hprefix tailTrace_2954730
  have hstable : (prefixWord ++ tailWord_2954730).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2954730).length < 2 ^ (prefixWord ++ tailWord_2954730).sum := by decide
  have hdescent : baseEnd_2954730 < baseStart_2954730 := by decide
  rcases family_descends (prefixWord ++ tailWord_2954730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2954741 : List Nat := [1, 3, 5, 1, 1, 3, 8]
def baseStart_2954741 : Nat := 118140960795 + 2954741 * 2 ^ 59
def prefixEnd_2954741 : Nat := 4983230072969 + 3 ^ 40 * 2954741 * 2
def baseEnd_2954741 : Nat := 37461786235716772739479

theorem tailTrace_2954741 : CollatzResearch.WordTrace tailWord_2954741 prefixEnd_2954741 37461786235716772739479 := by
  unfold tailWord_2954741
  simp only [CollatzResearch.WordTrace]
  refine ⟨107768257788485461432296077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71845505192323640954864051 107768257788485461432296077)
  ·
    refine ⟨40413096670682048037111029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 107768257788485461432296077 40413096670682048037111029)
    ·
      refine ⟨3788727812876442003479159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 40413096670682048037111029 3788727812876442003479159)
      ·
        refine ⟨5683091719314663005218739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3788727812876442003479159 5683091719314663005218739)
        ·
          refine ⟨8524637578971994507828109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5683091719314663005218739 8524637578971994507828109)
          ·
            refine ⟨3196739092114497940435541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8524637578971994507828109 3196739092114497940435541)
            ·
              refine ⟨37461786235716772739479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3196739092114497940435541 37461786235716772739479)
              ·
                rfl

theorem cell22_2954741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 3, 8].length) (baseStart_2954741 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2954741 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2954741 prefixEnd_2954741 := by exact prefixLift 2954741
  have htrace : WordTrace (prefixWord ++ tailWord_2954741) baseStart_2954741 baseEnd_2954741 := by
    simpa [prefixWord, tailWord_2954741, baseEnd_2954741] using wordTrace_append hprefix tailTrace_2954741
  have hstable : (prefixWord ++ tailWord_2954741).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2954741).length < 2 ^ (prefixWord ++ tailWord_2954741).sum := by decide
  have hdescent : baseEnd_2954741 < baseStart_2954741 := by decide
  rcases family_descends (prefixWord ++ tailWord_2954741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2954769 : List Nat := [1, 2, 2, 1, 1, 2, 5, 3, 5]
def baseStart_2954769 : Nat := 118140960795 + 2954769 * 2 ^ 59
def prefixEnd_2954769 : Nat := 4983230072969 + 3 ^ 40 * 2954769 * 2
def baseEnd_2954769 : Nat := 337159271112190041421949

theorem tailTrace_2954769 : CollatzResearch.WordTrace tailWord_2954769 prefixEnd_2954769 337159271112190041421949 := by
  unfold tailWord_2954769
  simp only [CollatzResearch.WordTrace]
  refine ⟨107769279032384022214315361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71846186021589348142876907 107769279032384022214315361)
  ·
    refine ⟨80826959274288016660736521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107769279032384022214315361 80826959274288016660736521)
    ·
      refine ⟨60620219455716012495552391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80826959274288016660736521 60620219455716012495552391)
      ·
        refine ⟨90930329183574018743328587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60620219455716012495552391 90930329183574018743328587)
        ·
          refine ⟨136395493775361028114992881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90930329183574018743328587 136395493775361028114992881)
          ·
            refine ⟨102296620331520771086244661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 136395493775361028114992881 102296620331520771086244661)
            ·
              refine ⟨9590308156080072289335437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 102296620331520771086244661 9590308156080072289335437)
              ·
                refine ⟨3596365558530027108500789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9590308156080072289335437 3596365558530027108500789)
                ·
                  refine ⟨337159271112190041421949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3596365558530027108500789 337159271112190041421949)
                  ·
                    rfl

theorem cell22_2954769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 5, 3, 5].length) (baseStart_2954769 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2954769 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2954769 prefixEnd_2954769 := by exact prefixLift 2954769
  have htrace : WordTrace (prefixWord ++ tailWord_2954769) baseStart_2954769 baseEnd_2954769 := by
    simpa [prefixWord, tailWord_2954769, baseEnd_2954769] using wordTrace_append hprefix tailTrace_2954769
  have hstable : (prefixWord ++ tailWord_2954769).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2954769).length < 2 ^ (prefixWord ++ tailWord_2954769).sum := by decide
  have hdescent : baseEnd_2954769 < baseStart_2954769 := by decide
  rcases family_descends (prefixWord ++ tailWord_2954769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2954889 : List Nat := [1, 2, 1, 1, 4, 1, 2, 2, 2, 6]
def baseStart_2954889 : Nat := 118140960795 + 2954889 * 2 ^ 59
def prefixEnd_2954889 : Nat := 4983230072969 + 3 ^ 40 * 2954889 * 2
def baseEnd_2954889 : Nat := 1011518891788929811265479

theorem tailTrace_2954889 : CollatzResearch.WordTrace tailWord_2954889 prefixEnd_2954889 1011518891788929811265479 := by
  unfold tailWord_2954889
  simp only [CollatzResearch.WordTrace]
  refine ⟨107773655791949282708683721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71849103861299521805789147 107773655791949282708683721)
  ·
    refine ⟨80830241843961962031512791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107773655791949282708683721 80830241843961962031512791)
    ·
      refine ⟨121245362765942943047269187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80830241843961962031512791 121245362765942943047269187)
      ·
        refine ⟨181868044148914414570903781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121245362765942943047269187 181868044148914414570903781)
        ·
          refine ⟨34100258277921452732044459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 181868044148914414570903781 34100258277921452732044459)
          ·
            refine ⟨51150387416882179098066689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34100258277921452732044459 51150387416882179098066689)
            ·
              refine ⟨38362790562661634323550017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51150387416882179098066689 38362790562661634323550017)
              ·
                refine ⟨28772092921996225742662513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38362790562661634323550017 28772092921996225742662513)
                ·
                  refine ⟨21579069691497169306996885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28772092921996225742662513 21579069691497169306996885)
                  ·
                    refine ⟨1011518891788929811265479, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21579069691497169306996885 1011518891788929811265479)
                    ·
                      rfl

theorem cell22_2954889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 2, 2, 2, 6].length) (baseStart_2954889 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2954889 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2954889 prefixEnd_2954889 := by exact prefixLift 2954889
  have htrace : WordTrace (prefixWord ++ tailWord_2954889) baseStart_2954889 baseEnd_2954889 := by
    simpa [prefixWord, tailWord_2954889, baseEnd_2954889] using wordTrace_append hprefix tailTrace_2954889
  have hstable : (prefixWord ++ tailWord_2954889).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2954889).length < 2 ^ (prefixWord ++ tailWord_2954889).sum := by decide
  have hdescent : baseEnd_2954889 < baseStart_2954889 := by decide
  rcases family_descends (prefixWord ++ tailWord_2954889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2954891 : List Nat := [1, 1, 1, 1, 4, 1, 3, 4, 3, 3]
def baseStart_2954891 : Nat := 118140960795 + 2954891 * 2 ^ 59
def prefixEnd_2954891 : Nat := 4983230072969 + 3 ^ 40 * 2954891 * 2
def baseEnd_2954891 : Nat := 1011519576429802472715473

theorem tailTrace_2954891 : CollatzResearch.WordTrace tailWord_2954891 prefixEnd_2954891 1011519576429802472715473 := by
  unfold tailWord_2954891
  simp only [CollatzResearch.WordTrace]
  refine ⟨107773728737942037050256527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71849152491961358033504351 107773728737942037050256527)
  ·
    refine ⟨161660593106913055575384791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107773728737942037050256527 161660593106913055575384791)
    ·
      refine ⟨242490889660369583363077187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 161660593106913055575384791 242490889660369583363077187)
      ·
        refine ⟨363736334490554375044615781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 242490889660369583363077187 363736334490554375044615781)
        ·
          refine ⟨68200562716978945320865459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 363736334490554375044615781 68200562716978945320865459)
          ·
            refine ⟨102300844075468417981298189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68200562716978945320865459 102300844075468417981298189)
            ·
              refine ⟨38362816528300656742986821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 102300844075468417981298189 38362816528300656742986821)
              ·
                refine ⟨7193028099056373139310029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 38362816528300656742986821 7193028099056373139310029)
                ·
                  refine ⟨2697385537146139927241261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7193028099056373139310029 2697385537146139927241261)
                  ·
                    refine ⟨1011519576429802472715473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2697385537146139927241261 1011519576429802472715473)
                    ·
                      rfl

theorem cell22_2954891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 3, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 3, 4, 3, 3].length) (baseStart_2954891 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2954891 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2954891 prefixEnd_2954891 := by exact prefixLift 2954891
  have htrace : WordTrace (prefixWord ++ tailWord_2954891) baseStart_2954891 baseEnd_2954891 := by
    simpa [prefixWord, tailWord_2954891, baseEnd_2954891] using wordTrace_append hprefix tailTrace_2954891
  have hstable : (prefixWord ++ tailWord_2954891).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2954891).length < 2 ^ (prefixWord ++ tailWord_2954891).sum := by decide
  have hdescent : baseEnd_2954891 < baseStart_2954891 := by decide
  rcases family_descends (prefixWord ++ tailWord_2954891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2954938 : List Nat := [3, 1, 1, 1, 2, 4, 4, 1, 5]
def baseStart_2954938 : Nat := 118140960795 + 2954938 * 2 ^ 59
def prefixEnd_2954938 : Nat := 4983230072969 + 3 ^ 40 * 2954938 * 2
def baseEnd_2954938 : Nat := 337178555163436672263443

theorem tailTrace_2954938 : CollatzResearch.WordTrace tailWord_2954938 prefixEnd_2954938 337178555163436672263443 := by
  unfold tailWord_2954938
  simp only [CollatzResearch.WordTrace]
  refine ⟨26943860742192941019304367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71850295312514509384811645 26943860742192941019304367)
  ·
    refine ⟨40415791113289411528956551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26943860742192941019304367 40415791113289411528956551)
    ·
      refine ⟨60623686669934117293434827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40415791113289411528956551 60623686669934117293434827)
      ·
        refine ⟨90935530004901175940152241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60623686669934117293434827 90935530004901175940152241)
        ·
          refine ⟨68201647503675881955114181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 90935530004901175940152241 68201647503675881955114181)
          ·
            refine ⟨12787808906939227866583909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 68201647503675881955114181 12787808906939227866583909)
            ·
              refine ⟨2397714170051105224984483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12787808906939227866583909 2397714170051105224984483)
              ·
                refine ⟨3596571255076657837476725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2397714170051105224984483 3596571255076657837476725)
                ·
                  refine ⟨337178555163436672263443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3596571255076657837476725 337178555163436672263443)
                  ·
                    rfl

theorem cell22_2954938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 4, 1, 5].length) (baseStart_2954938 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2954938 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2954938 prefixEnd_2954938 := by exact prefixLift 2954938
  have htrace : WordTrace (prefixWord ++ tailWord_2954938) baseStart_2954938 baseEnd_2954938 := by
    simpa [prefixWord, tailWord_2954938, baseEnd_2954938] using wordTrace_append hprefix tailTrace_2954938
  have hstable : (prefixWord ++ tailWord_2954938).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2954938).length < 2 ^ (prefixWord ++ tailWord_2954938).sum := by decide
  have hdescent : baseEnd_2954938 < baseStart_2954938 := by decide
  rcases family_descends (prefixWord ++ tailWord_2954938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2954951 : List Nat := [1, 1, 4, 1, 1, 1, 5, 1, 3, 4]
def baseStart_2954951 : Nat := 118140960795 + 2954951 * 2 ^ 59
def prefixEnd_2954951 : Nat := 4983230072969 + 3 ^ 40 * 2954951 * 2
def baseEnd_2954951 : Nat := 1011540115655982316215289

theorem tailTrace_2954951 : CollatzResearch.WordTrace tailWord_2954951 prefixEnd_2954951 1011540115655982316215289 := by
  unfold tailWord_2954951
  simp only [CollatzResearch.WordTrace]
  refine ⟨107775917117724667297440707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71850611411816444864960471 107775917117724667297440707)
  ·
    refine ⟨161663875676587000946161061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107775917117724667297440707 161663875676587000946161061)
    ·
      refine ⟨30311976689360062677405199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 161663875676587000946161061 30311976689360062677405199)
      ·
        refine ⟨45467965034040094016107799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30311976689360062677405199 45467965034040094016107799)
        ·
          refine ⟨68201947551060141024161699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45467965034040094016107799 68201947551060141024161699)
          ·
            refine ⟨102302921326590211536242549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68201947551060141024161699 102302921326590211536242549)
            ·
              refine ⟨9590898874367832331522739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 102302921326590211536242549 9590898874367832331522739)
              ·
                refine ⟨14386348311551748497284109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9590898874367832331522739 14386348311551748497284109)
                ·
                  refine ⟨5394880616831905686481541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14386348311551748497284109 5394880616831905686481541)
                  ·
                    refine ⟨1011540115655982316215289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5394880616831905686481541 1011540115655982316215289)
                    ·
                      rfl

theorem cell22_2954951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 5, 1, 3, 4].length) (baseStart_2954951 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2954951 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2954951 prefixEnd_2954951 := by exact prefixLift 2954951
  have htrace : WordTrace (prefixWord ++ tailWord_2954951) baseStart_2954951 baseEnd_2954951 := by
    simpa [prefixWord, tailWord_2954951, baseEnd_2954951] using wordTrace_append hprefix tailTrace_2954951
  have hstable : (prefixWord ++ tailWord_2954951).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2954951).length < 2 ^ (prefixWord ++ tailWord_2954951).sum := by decide
  have hdescent : baseEnd_2954951 < baseStart_2954951 := by decide
  rcases family_descends (prefixWord ++ tailWord_2954951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2954981 : List Nat := [1, 3, 1, 4, 1, 1, 1, 2, 3, 5]
def baseStart_2954981 : Nat := 118140960795 + 2954981 * 2 ^ 59
def prefixEnd_2954981 : Nat := 4983230072969 + 3 ^ 40 * 2954981 * 2
def baseEnd_2954981 : Nat := 1011550385269072237965197

theorem tailTrace_2954981 : CollatzResearch.WordTrace tailWord_2954981 prefixEnd_2954981 1011550385269072237965197 := by
  unfold tailWord_2954981
  simp only [CollatzResearch.WordTrace]
  refine ⟨107777011307615982421032797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71851340871743988280688531 107777011307615982421032797)
  ·
    refine ⟨40416379240355993407887299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 107777011307615982421032797 40416379240355993407887299)
    ·
      refine ⟨60624568860533990111830949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40416379240355993407887299 60624568860533990111830949)
      ·
        refine ⟨11367106661350123145968303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 60624568860533990111830949 11367106661350123145968303)
        ·
          refine ⟨17050659992025184718952455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11367106661350123145968303 17050659992025184718952455)
          ·
            refine ⟨25575989988037777078428683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17050659992025184718952455 25575989988037777078428683)
            ·
              refine ⟨38363984982056665617643025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25575989988037777078428683 38363984982056665617643025)
              ·
                refine ⟨28772988736542499213232269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38363984982056665617643025 28772988736542499213232269)
                ·
                  refine ⟨10789870776203437204962101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28772988736542499213232269 10789870776203437204962101)
                  ·
                    refine ⟨1011550385269072237965197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10789870776203437204962101 1011550385269072237965197)
                    ·
                      rfl

theorem cell22_2954981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 1, 2, 3, 5].length) (baseStart_2954981 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2954981 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2954981 prefixEnd_2954981 := by exact prefixLift 2954981
  have htrace : WordTrace (prefixWord ++ tailWord_2954981) baseStart_2954981 baseEnd_2954981 := by
    simpa [prefixWord, tailWord_2954981, baseEnd_2954981] using wordTrace_append hprefix tailTrace_2954981
  have hstable : (prefixWord ++ tailWord_2954981).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2954981).length < 2 ^ (prefixWord ++ tailWord_2954981).sum := by decide
  have hdescent : baseEnd_2954981 < baseStart_2954981 := by decide
  rcases family_descends (prefixWord ++ tailWord_2954981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2954998 : List Nat := [5, 1, 1, 1, 1, 3, 1, 3, 1, 5]
def baseStart_2954998 : Nat := 118140960795 + 2954998 * 2 ^ 59
def prefixEnd_2954998 : Nat := 4983230072969 + 3 ^ 40 * 2954998 * 2
def baseEnd_2954998 : Nat := 1011556204716489860290145

theorem tailTrace_2954998 : CollatzResearch.WordTrace tailWord_2954998 prefixEnd_2954998 1011556204716489860290145 := by
  unfold tailWord_2954998
  simp only [CollatzResearch.WordTrace]
  refine ⟨6736101959284649645275103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 71851754232369596216267765 6736101959284649645275103)
  ·
    refine ⟨10104152938926974467912655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6736101959284649645275103 10104152938926974467912655)
    ·
      refine ⟨15156229408390461701868983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10104152938926974467912655 15156229408390461701868983)
      ·
        refine ⟨22734344112585692552803475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15156229408390461701868983 22734344112585692552803475)
        ·
          refine ⟨34101516168878538829205213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22734344112585692552803475 34101516168878538829205213)
          ·
            refine ⟨12788068563329452060951955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34101516168878538829205213 12788068563329452060951955)
            ·
              refine ⟨19182102844994178091427933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12788068563329452060951955 19182102844994178091427933)
              ·
                refine ⟨7193288566872816784285475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19182102844994178091427933 7193288566872816784285475)
                ·
                  refine ⟨10789932850309225176428213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7193288566872816784285475 10789932850309225176428213)
                  ·
                    refine ⟨1011556204716489860290145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10789932850309225176428213 1011556204716489860290145)
                    ·
                      rfl

theorem cell22_2954998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 1, 3, 1, 5].length) (baseStart_2954998 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2954998 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2954998 prefixEnd_2954998 := by exact prefixLift 2954998
  have htrace : WordTrace (prefixWord ++ tailWord_2954998) baseStart_2954998 baseEnd_2954998 := by
    simpa [prefixWord, tailWord_2954998, baseEnd_2954998] using wordTrace_append hprefix tailTrace_2954998
  have hstable : (prefixWord ++ tailWord_2954998).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2954998).length < 2 ^ (prefixWord ++ tailWord_2954998).sum := by decide
  have hdescent : baseEnd_2954998 < baseStart_2954998 := by decide
  rcases family_descends (prefixWord ++ tailWord_2954998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2955043 : List Nat := [1, 1, 1, 4, 2, 1, 3, 3, 3, 3]
def baseStart_2955043 : Nat := 118140960795 + 2955043 * 2 ^ 59
def prefixEnd_2955043 : Nat := 4983230072969 + 3 ^ 40 * 2955043 * 2
def baseEnd_2955043 : Nat := 1011571609136124742915007

theorem tailTrace_2955043 : CollatzResearch.WordTrace tailWord_2955043 prefixEnd_2955043 1011571609136124742915007 := by
  unfold tailWord_2955043
  simp only [CollatzResearch.WordTrace]
  refine ⟨107779272633391367009789783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71852848422260911339859855 107779272633391367009789783)
  ·
    refine ⟨161668908950087050514684675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107779272633391367009789783 161668908950087050514684675)
    ·
      refine ⟨242503363425130575772027013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 161668908950087050514684675 242503363425130575772027013)
      ·
        refine ⟨45469380642211982957255065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 242503363425130575772027013 45469380642211982957255065)
        ·
          refine ⟨34102035481658987217941299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45469380642211982957255065 34102035481658987217941299)
          ·
            refine ⟨51153053222488480826911949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34102035481658987217941299 51153053222488480826911949)
            ·
              refine ⟨19182394958433180310091981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 51153053222488480826911949 19182394958433180310091981)
              ·
                refine ⟨7193398109412442616284493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19182394958433180310091981 7193398109412442616284493)
                ·
                  refine ⟨2697524291029665981106685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7193398109412442616284493 2697524291029665981106685)
                  ·
                    refine ⟨1011571609136124742915007, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2697524291029665981106685 1011571609136124742915007)
                    ·
                      rfl

theorem cell22_2955043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 3, 3, 3, 3].length) (baseStart_2955043 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2955043 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2955043 prefixEnd_2955043 := by exact prefixLift 2955043
  have htrace : WordTrace (prefixWord ++ tailWord_2955043) baseStart_2955043 baseEnd_2955043 := by
    simpa [prefixWord, tailWord_2955043, baseEnd_2955043] using wordTrace_append hprefix tailTrace_2955043
  have hstable : (prefixWord ++ tailWord_2955043).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2955043).length < 2 ^ (prefixWord ++ tailWord_2955043).sum := by decide
  have hdescent : baseEnd_2955043 < baseStart_2955043 := by decide
  rcases family_descends (prefixWord ++ tailWord_2955043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2955062 : List Nat := [5, 1, 2, 2, 1, 3, 2, 6]
def baseStart_2955062 : Nat := 118140960795 + 2955062 * 2 ^ 59
def prefixEnd_2955062 : Nat := 4983230072969 + 3 ^ 40 * 2955062 * 2
def baseEnd_2955062 : Nat := 112397568136046114076661

theorem tailTrace_2955062 : CollatzResearch.WordTrace tailWord_2955062 prefixEnd_2955062 112397568136046114076661 := by
  unfold tailWord_2955062
  simp only [CollatzResearch.WordTrace]
  refine ⟨6736247851270158328420715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 71853310413548355503154293 6736247851270158328420715)
  ·
    refine ⟨10104371776905237492631073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6736247851270158328420715 10104371776905237492631073)
    ·
      refine ⟨7578278832678928119473305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10104371776905237492631073 7578278832678928119473305)
      ·
        refine ⟨5683709124509196089604979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7578278832678928119473305 5683709124509196089604979)
        ·
          refine ⟨8525563686763794134407469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5683709124509196089604979 8525563686763794134407469)
          ·
            refine ⟨3197086382536422800402801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8525563686763794134407469 3197086382536422800402801)
            ·
              refine ⟨2397814786902317100302101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3197086382536422800402801 2397814786902317100302101)
              ·
                refine ⟨112397568136046114076661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2397814786902317100302101 112397568136046114076661)
                ·
                  rfl

theorem cell22_2955062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 3, 2, 6].length) (baseStart_2955062 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2955062 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2955062 prefixEnd_2955062 := by exact prefixLift 2955062
  have htrace : WordTrace (prefixWord ++ tailWord_2955062) baseStart_2955062 baseEnd_2955062 := by
    simpa [prefixWord, tailWord_2955062, baseEnd_2955062] using wordTrace_append hprefix tailTrace_2955062
  have hstable : (prefixWord ++ tailWord_2955062).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2955062).length < 2 ^ (prefixWord ++ tailWord_2955062).sum := by decide
  have hdescent : baseEnd_2955062 < baseStart_2955062 := by decide
  rcases family_descends (prefixWord ++ tailWord_2955062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2955107 : List Nat := [1, 1, 1, 5, 4, 2, 2, 1, 5]
def baseStart_2955107 : Nat := 118140960795 + 2955107 * 2 ^ 59
def prefixEnd_2955107 : Nat := 4983230072969 + 3 ^ 40 * 2955107 * 2
def baseEnd_2955107 : Nat := 337197839214683303104937

theorem tailTrace_2955107 : CollatzResearch.WordTrace tailWord_2955107 prefixEnd_2955107 337197839214683303104937 := by
  unfold tailWord_2955107
  simp only [CollatzResearch.WordTrace]
  refine ⟨107781606905159505940119575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71854404603439670626746383 107781606905159505940119575)
  ·
    refine ⟨161672410357739258910179363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107781606905159505940119575 161672410357739258910179363)
    ·
      refine ⟨242508615536608888365269045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 161672410357739258910179363 242508615536608888365269045)
      ·
        refine ⟨22735182706557083284243973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 242508615536608888365269045 22735182706557083284243973)
        ·
          refine ⟨4262846757479453115795745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22735182706557083284243973 4262846757479453115795745)
          ·
            refine ⟨3197135068109589836846809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4262846757479453115795745 3197135068109589836846809)
            ·
              refine ⟨2397851301082192377635107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3197135068109589836846809 2397851301082192377635107)
              ·
                refine ⟨3596776951623288566452661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2397851301082192377635107 3596776951623288566452661)
                ·
                  refine ⟨337197839214683303104937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3596776951623288566452661 337197839214683303104937)
                  ·
                    rfl

theorem cell22_2955107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 2, 2, 1, 5].length) (baseStart_2955107 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2955107 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2955107 prefixEnd_2955107 := by exact prefixLift 2955107
  have htrace : WordTrace (prefixWord ++ tailWord_2955107) baseStart_2955107 baseEnd_2955107 := by
    simpa [prefixWord, tailWord_2955107, baseEnd_2955107] using wordTrace_append hprefix tailTrace_2955107
  have hstable : (prefixWord ++ tailWord_2955107).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2955107).length < 2 ^ (prefixWord ++ tailWord_2955107).sum := by decide
  have hdescent : baseEnd_2955107 < baseStart_2955107 := by decide
  rcases family_descends (prefixWord ++ tailWord_2955107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2955188 : List Nat := [2, 5, 2, 1, 3, 1, 2, 1, 1, 4]
def baseStart_2955188 : Nat := 118140960795 + 2955188 * 2 ^ 59
def prefixEnd_2955188 : Nat := 4983230072969 + 3 ^ 40 * 2955188 * 2
def baseEnd_2955188 : Nat := 1011621245599392698039563

theorem tailTrace_2955188 : CollatzResearch.WordTrace tailWord_2955188 prefixEnd_2955188 1011621245599392698039563 := by
  unfold tailWord_2955188
  simp only [CollatzResearch.WordTrace]
  refine ⟨53892280608933028386909109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71856374145244037849212145 53892280608933028386909109)
  ·
    refine ⟨5052401307087471411272729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 53892280608933028386909109 5052401307087471411272729)
    ·
      refine ⟨3789300980315603558454547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5052401307087471411272729 3789300980315603558454547)
      ·
        refine ⟨5683951470473405337681821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3789300980315603558454547 5683951470473405337681821)
        ·
          refine ⟨2131481801427527001630683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5683951470473405337681821 2131481801427527001630683)
          ·
            refine ⟨3197222702141290502446025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2131481801427527001630683 3197222702141290502446025)
            ·
              refine ⟨2397917026605967876834519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3197222702141290502446025 2397917026605967876834519)
              ·
                refine ⟨3596875539908951815251779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2397917026605967876834519 3596875539908951815251779)
                ·
                  refine ⟨5395313309863427722877669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3596875539908951815251779 5395313309863427722877669)
                  ·
                    refine ⟨1011621245599392698039563, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5395313309863427722877669 1011621245599392698039563)
                    ·
                      rfl

theorem cell22_2955188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 3, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 3, 1, 2, 1, 1, 4].length) (baseStart_2955188 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2955188 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2955188 prefixEnd_2955188 := by exact prefixLift 2955188
  have htrace : WordTrace (prefixWord ++ tailWord_2955188) baseStart_2955188 baseEnd_2955188 := by
    simpa [prefixWord, tailWord_2955188, baseEnd_2955188] using wordTrace_append hprefix tailTrace_2955188
  have hstable : (prefixWord ++ tailWord_2955188).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2955188).length < 2 ^ (prefixWord ++ tailWord_2955188).sum := by decide
  have hdescent : baseEnd_2955188 < baseStart_2955188 := by decide
  rcases family_descends (prefixWord ++ tailWord_2955188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2955212 : List Nat := [2, 2, 1, 4, 1, 3, 2, 1, 3, 3]
def baseStart_2955212 : Nat := 118140960795 + 2955212 * 2 ^ 59
def prefixEnd_2955212 : Nat := 4983230072969 + 3 ^ 40 * 2955212 * 2
def baseEnd_2955212 : Nat := 1011629461289864635439489

theorem tailTrace_2955212 : CollatzResearch.WordTrace tailWord_2955212 prefixEnd_2955212 1011629461289864635439489 := by
  unfold tailWord_2955212
  simp only [CollatzResearch.WordTrace]
  refine ⟨53892718284889554436345945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71856957713186072581794593 53892718284889554436345945)
  ·
    refine ⟨40419538713667165827259459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53892718284889554436345945 40419538713667165827259459)
    ·
      refine ⟨60629308070500748740889189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40419538713667165827259459 60629308070500748740889189)
      ·
        refine ⟨11367995263218890388916723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 60629308070500748740889189 11367995263218890388916723)
        ·
          refine ⟨17051992894828335583375085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11367995263218890388916723 17051992894828335583375085)
          ·
            refine ⟨6394497335560625843765657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17051992894828335583375085 6394497335560625843765657)
            ·
              refine ⟨4795873001670469382824243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6394497335560625843765657 4795873001670469382824243)
              ·
                refine ⟨7193809502505704074236365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4795873001670469382824243 7193809502505704074236365)
                ·
                  refine ⟨2697678563439639027838637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7193809502505704074236365 2697678563439639027838637)
                  ·
                    refine ⟨1011629461289864635439489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2697678563439639027838637 1011629461289864635439489)
                    ·
                      rfl

theorem cell22_2955212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 3, 2, 1, 3, 3].length) (baseStart_2955212 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2955212 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2955212 prefixEnd_2955212 := by exact prefixLift 2955212
  have htrace : WordTrace (prefixWord ++ tailWord_2955212) baseStart_2955212 baseEnd_2955212 := by
    simpa [prefixWord, tailWord_2955212, baseEnd_2955212] using wordTrace_append hprefix tailTrace_2955212
  have hstable : (prefixWord ++ tailWord_2955212).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2955212).length < 2 ^ (prefixWord ++ tailWord_2955212).sum := by decide
  have hdescent : baseEnd_2955212 < baseStart_2955212 := by decide
  rcases family_descends (prefixWord ++ tailWord_2955212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2955223 : List Nat := [1, 1, 3, 2, 1, 1, 3, 3, 2, 5]
def baseStart_2955223 : Nat := 118140960795 + 2955223 * 2 ^ 59
def prefixEnd_2955223 : Nat := 4983230072969 + 3 ^ 40 * 2955223 * 2
def baseEnd_2955223 : Nat := 1011633226814664273414455

theorem tailTrace_2955223 : CollatzResearch.WordTrace tailWord_2955223 prefixEnd_2955223 1011633226814664273414455 := by
  unfold tailWord_2955223
  simp only [CollatzResearch.WordTrace]
  refine ⟨107785837772739257751342323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71857225181826171834228215 107785837772739257751342323)
  ·
    refine ⟨161678756659108886627013485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107785837772739257751342323 161678756659108886627013485)
    ·
      refine ⟨60629533747165832485130057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 161678756659108886627013485 60629533747165832485130057)
      ·
        refine ⟨45472150310374374363847543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60629533747165832485130057 45472150310374374363847543)
        ·
          refine ⟨68208225465561561545771315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45472150310374374363847543 68208225465561561545771315)
          ·
            refine ⟨102312338198342342318656973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68208225465561561545771315 102312338198342342318656973)
            ·
              refine ⟨38367126824378378369496365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 102312338198342342318656973 38367126824378378369496365)
              ·
                refine ⟨14387672559141891888561137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38367126824378378369496365 14387672559141891888561137)
                ·
                  refine ⟨10790754419356418916420853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14387672559141891888561137 10790754419356418916420853)
                  ·
                    refine ⟨1011633226814664273414455, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10790754419356418916420853 1011633226814664273414455)
                    ·
                      rfl

theorem cell22_2955223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 3, 3, 2, 5].length) (baseStart_2955223 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2955223 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2955223 prefixEnd_2955223 := by exact prefixLift 2955223
  have htrace : WordTrace (prefixWord ++ tailWord_2955223) baseStart_2955223 baseEnd_2955223 := by
    simpa [prefixWord, tailWord_2955223, baseEnd_2955223] using wordTrace_append hprefix tailTrace_2955223
  have hstable : (prefixWord ++ tailWord_2955223).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2955223).length < 2 ^ (prefixWord ++ tailWord_2955223).sum := by decide
  have hdescent : baseEnd_2955223 < baseStart_2955223 := by decide
  rcases family_descends (prefixWord ++ tailWord_2955223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2955246 : List Nat := [4, 1, 2, 1, 3, 3, 1, 3, 1, 3]
def baseStart_2955246 : Nat := 118140960795 + 2955246 * 2 ^ 59
def prefixEnd_2955246 : Nat := 4983230072969 + 3 ^ 40 * 2955246 * 2
def baseEnd_2955246 : Nat := 1011641100184699880089385

theorem tailTrace_2955246 : CollatzResearch.WordTrace tailWord_2955246 prefixEnd_2955246 1011641100184699880089385 := by
  unfold tailWord_2955246
  simp only [CollatzResearch.WordTrace]
  refine ⟨13473334581456991584928699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 71857784434437288452953061 13473334581456991584928699)
  ·
    refine ⟨20210001872185487377393049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13473334581456991584928699 20210001872185487377393049)
    ·
      refine ⟨15157501404139115533044787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20210001872185487377393049 15157501404139115533044787)
      ·
        refine ⟨22736252106208673299567181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15157501404139115533044787 22736252106208673299567181)
        ·
          refine ⟨8526094539828252487337693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22736252106208673299567181 8526094539828252487337693)
          ·
            refine ⟨3197285452435594682751635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8526094539828252487337693 3197285452435594682751635)
            ·
              refine ⟨4795928178653392024127453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3197285452435594682751635 4795928178653392024127453)
              ·
                refine ⟨1798473066995022009047795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4795928178653392024127453 1798473066995022009047795)
                ·
                  refine ⟨2697709600492533013571693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1798473066995022009047795 2697709600492533013571693)
                  ·
                    refine ⟨1011641100184699880089385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2697709600492533013571693 1011641100184699880089385)
                    ·
                      rfl

theorem cell22_2955246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 3, 1, 3, 1, 3].length) (baseStart_2955246 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2955246 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2955246 prefixEnd_2955246 := by exact prefixLift 2955246
  have htrace : WordTrace (prefixWord ++ tailWord_2955246) baseStart_2955246 baseEnd_2955246 := by
    simpa [prefixWord, tailWord_2955246, baseEnd_2955246] using wordTrace_append hprefix tailTrace_2955246
  have hstable : (prefixWord ++ tailWord_2955246).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2955246).length < 2 ^ (prefixWord ++ tailWord_2955246).sum := by decide
  have hdescent : baseEnd_2955246 < baseStart_2955246 := by decide
  rcases family_descends (prefixWord ++ tailWord_2955246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2955283 : List Nat := [1, 1, 1, 2, 1, 4, 2, 1, 3, 6]
def baseStart_2955283 : Nat := 118140960795 + 2955283 * 2 ^ 59
def prefixEnd_2955283 : Nat := 4983230072969 + 3 ^ 40 * 2955283 * 2
def baseEnd_2955283 : Nat := 1011653766040844116914271

theorem tailTrace_2955283 : CollatzResearch.WordTrace tailWord_2955283 prefixEnd_2955283 1011653766040844116914271 := by
  unfold tailWord_2955283
  simp only [CollatzResearch.WordTrace]
  refine ⟨107788026152521887998526503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71858684101681258665684335 107788026152521887998526503)
  ·
    refine ⟨161682039228782831997789755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107788026152521887998526503 161682039228782831997789755)
    ·
      refine ⟨242523058843174247996684633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 161682039228782831997789755 242523058843174247996684633)
      ·
        refine ⟨181892294132380685997513475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 242523058843174247996684633 181892294132380685997513475)
        ·
          refine ⟨272838441198571028996270213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 181892294132380685997513475 272838441198571028996270213)
          ·
            refine ⟨51157207724732067936800665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 272838441198571028996270213 51157207724732067936800665)
            ·
              refine ⟨38367905793549050952600499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51157207724732067936800665 38367905793549050952600499)
              ·
                refine ⟨57551858690323576428900749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38367905793549050952600499 57551858690323576428900749)
                ·
                  refine ⟨21581947008871341160837781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 57551858690323576428900749 21581947008871341160837781)
                  ·
                    refine ⟨1011653766040844116914271, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21581947008871341160837781 1011653766040844116914271)
                    ·
                      rfl

theorem cell22_2955283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 2, 1, 3, 6].length) (baseStart_2955283 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2955283 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2955283 prefixEnd_2955283 := by exact prefixLift 2955283
  have htrace : WordTrace (prefixWord ++ tailWord_2955283) baseStart_2955283 baseEnd_2955283 := by
    simpa [prefixWord, tailWord_2955283, baseEnd_2955283] using wordTrace_append hprefix tailTrace_2955283
  have hstable : (prefixWord ++ tailWord_2955283).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2955283).length < 2 ^ (prefixWord ++ tailWord_2955283).sum := by decide
  have hdescent : baseEnd_2955283 < baseStart_2955283 := by decide
  rcases family_descends (prefixWord ++ tailWord_2955283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2955321 : List Nat := [1, 2, 1, 5, 3, 2, 2, 2, 4]
def baseStart_2955321 : Nat := 118140960795 + 2955321 * 2 ^ 59
def prefixEnd_2955321 : Nat := 4983230072969 + 3 ^ 40 * 2955321 * 2
def baseEnd_2955321 : Nat := 337222258072474894821385

theorem tailTrace_2955321 : CollatzResearch.WordTrace tailWord_2955321 prefixEnd_2955321 337222258072474894821385 := by
  unfold tailWord_2955321
  simp only [CollatzResearch.WordTrace]
  refine ⟨107789412126384220488409817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71859608084256146992273211 107789412126384220488409817)
  ·
    refine ⟨80842059094788165366307363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107789412126384220488409817 80842059094788165366307363)
    ·
      refine ⟨121263088642182248049461045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80842059094788165366307363 121263088642182248049461045)
      ·
        refine ⟨11368414560204585754636973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 121263088642182248049461045 11368414560204585754636973)
        ·
          refine ⟨4263155460076719657988865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11368414560204585754636973 4263155460076719657988865)
          ·
            refine ⟨3197366595057539743491649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4263155460076719657988865 3197366595057539743491649)
            ·
              refine ⟨2398024946293154807618737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3197366595057539743491649 2398024946293154807618737)
              ·
                refine ⟨1798518709719866105714053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2398024946293154807618737 1798518709719866105714053)
                ·
                  refine ⟨337222258072474894821385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1798518709719866105714053 337222258072474894821385)
                  ·
                    rfl

theorem cell22_2955321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 2, 2, 2, 4].length) (baseStart_2955321 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2955321 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2955321 prefixEnd_2955321 := by exact prefixLift 2955321
  have htrace : WordTrace (prefixWord ++ tailWord_2955321) baseStart_2955321 baseEnd_2955321 := by
    simpa [prefixWord, tailWord_2955321, baseEnd_2955321] using wordTrace_append hprefix tailTrace_2955321
  have hstable : (prefixWord ++ tailWord_2955321).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2955321).length < 2 ^ (prefixWord ++ tailWord_2955321).sum := by decide
  have hdescent : baseEnd_2955321 < baseStart_2955321 := by decide
  rcases family_descends (prefixWord ++ tailWord_2955321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2955364 : List Nat := [2, 3, 1, 1, 2, 1, 3, 5, 1, 3]
def baseStart_2955364 : Nat := 118140960795 + 2955364 * 2 ^ 59
def prefixEnd_2955364 : Nat := 4983230072969 + 3 ^ 40 * 2955364 * 2
def baseEnd_2955364 : Nat := 1011681493996186905639023

theorem tailTrace_2955364 : CollatzResearch.WordTrace tailWord_2955364 prefixEnd_2955364 1011681493996186905639023 := by
  unfold tailWord_2955364
  simp only [CollatzResearch.WordTrace]
  refine ⟨53895490232614219416112573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71860653643485625888150097 53895490232614219416112573)
  ·
    refine ⟨20210808837230332281042215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53895490232614219416112573 20210808837230332281042215)
    ·
      refine ⟨30316213255845498421563323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20210808837230332281042215 30316213255845498421563323)
      ·
        refine ⟨45474319883768247632344985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30316213255845498421563323 45474319883768247632344985)
        ·
          refine ⟨34105739912826185724258739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45474319883768247632344985 34105739912826185724258739)
          ·
            refine ⟨51158609869239278586388109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34105739912826185724258739 51158609869239278586388109)
            ·
              refine ⟨19184478700964729469895541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 51158609869239278586388109 19184478700964729469895541)
              ·
                refine ⟨1798544878215443387802707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 19184478700964729469895541 1798544878215443387802707)
                ·
                  refine ⟨2697817317323165081704061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1798544878215443387802707 2697817317323165081704061)
                  ·
                    refine ⟨1011681493996186905639023, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2697817317323165081704061 1011681493996186905639023)
                    ·
                      rfl

theorem cell22_2955364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 3, 5, 1, 3].length) (baseStart_2955364 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2955364 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2955364 prefixEnd_2955364 := by exact prefixLift 2955364
  have htrace : WordTrace (prefixWord ++ tailWord_2955364) baseStart_2955364 baseEnd_2955364 := by
    simpa [prefixWord, tailWord_2955364, baseEnd_2955364] using wordTrace_append hprefix tailTrace_2955364
  have hstable : (prefixWord ++ tailWord_2955364).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2955364).length < 2 ^ (prefixWord ++ tailWord_2955364).sum := by decide
  have hdescent : baseEnd_2955364 < baseStart_2955364 := by decide
  rcases family_descends (prefixWord ++ tailWord_2955364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2955375 : List Nat := [1, 1, 2, 1, 3, 4, 1, 2, 2, 5]
def baseStart_2955375 : Nat := 118140960795 + 2955375 * 2 ^ 59
def prefixEnd_2955375 : Nat := 4983230072969 + 3 ^ 40 * 2955375 * 2
def baseEnd_2955375 : Nat := 1011685259520986543613989

theorem tailTrace_2955375 : CollatzResearch.WordTrace tailWord_2955375 prefixEnd_2955375 1011685259520986543613989 := by
  unfold tailWord_2955375
  simp only [CollatzResearch.WordTrace]
  refine ⟨107791381668188587710875579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71860921112125725140583719 107791381668188587710875579)
  ·
    refine ⟨161687072502282881566313369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107791381668188587710875579 161687072502282881566313369)
    ·
      refine ⟨121265304376712161174735027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 161687072502282881566313369 121265304376712161174735027)
      ·
        refine ⟨181897956565068241762102541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121265304376712161174735027 181897956565068241762102541)
        ·
          refine ⟨68211733711900590660788453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 181897956565068241762102541 68211733711900590660788453)
          ·
            refine ⟨12789700070981360748897835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 68211733711900590660788453 12789700070981360748897835)
            ·
              refine ⟨19184550106472041123346753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12789700070981360748897835 19184550106472041123346753)
              ·
                refine ⟨14388412579854030842510065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19184550106472041123346753 14388412579854030842510065)
                ·
                  refine ⟨10791309434890523131882549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14388412579854030842510065 10791309434890523131882549)
                  ·
                    refine ⟨1011685259520986543613989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10791309434890523131882549 1011685259520986543613989)
                    ·
                      rfl

theorem cell22_2955375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 1, 2, 2, 5].length) (baseStart_2955375 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2955375 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2955375 prefixEnd_2955375 := by exact prefixLift 2955375
  have htrace : WordTrace (prefixWord ++ tailWord_2955375) baseStart_2955375 baseEnd_2955375 := by
    simpa [prefixWord, tailWord_2955375, baseEnd_2955375] using wordTrace_append hprefix tailTrace_2955375
  have hstable : (prefixWord ++ tailWord_2955375).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2955375).length < 2 ^ (prefixWord ++ tailWord_2955375).sum := by decide
  have hdescent : baseEnd_2955375 < baseStart_2955375 := by decide
  rcases family_descends (prefixWord ++ tailWord_2955375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2955450 : List Nat := [3, 1, 1, 1, 2, 2, 3, 9]
def baseStart_2955450 : Nat := 118140960795 + 2955450 * 2 ^ 59
def prefixEnd_2955450 : Nat := 4983230072969 + 3 ^ 40 * 2955450 * 2
def baseEnd_2955450 : Nat := 112412325950412371998751

theorem tailTrace_2955450 : CollatzResearch.WordTrace tailWord_2955450 prefixEnd_2955450 112412325950412371998751 := by
  unfold tailWord_2955450
  simp only [CollatzResearch.WordTrace]
  refine ⟨26948529285729218879963951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71862744761944583679903869 26948529285729218879963951)
  ·
    refine ⟨40422793928593828319945927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26948529285729218879963951 40422793928593828319945927)
    ·
      refine ⟨60634190892890742479918891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40422793928593828319945927 60634190892890742479918891)
      ·
        refine ⟨90951286339336113719878337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60634190892890742479918891 90951286339336113719878337)
        ·
          refine ⟨68213464754502085289908753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 90951286339336113719878337 68213464754502085289908753)
          ·
            refine ⟨51160098565876563967431565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 68213464754502085289908753 51160098565876563967431565)
            ·
              refine ⟨19185036962203711487786837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 51160098565876563967431565 19185036962203711487786837)
              ·
                refine ⟨112412325950412371998751, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 19185036962203711487786837 112412325950412371998751)
                ·
                  rfl

theorem cell22_2955450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 3, 9].length) (baseStart_2955450 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2955450 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2955450 prefixEnd_2955450 := by exact prefixLift 2955450
  have htrace : WordTrace (prefixWord ++ tailWord_2955450) baseStart_2955450 baseEnd_2955450 := by
    simpa [prefixWord, tailWord_2955450, baseEnd_2955450] using wordTrace_append hprefix tailTrace_2955450
  have hstable : (prefixWord ++ tailWord_2955450).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2955450).length < 2 ^ (prefixWord ++ tailWord_2955450).sum := by decide
  have hdescent : baseEnd_2955450 < baseStart_2955450 := by decide
  rcases family_descends (prefixWord ++ tailWord_2955450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2955458 : List Nat := [3, 5, 1, 1, 1, 1, 3, 2, 1, 4]
def baseStart_2955458 : Nat := 118140960795 + 2955458 * 2 ^ 59
def prefixEnd_2955458 : Nat := 4983230072969 + 3 ^ 40 * 2955458 * 2
def baseEnd_2955458 : Nat := 1011713672117201993788735

theorem tailTrace_2955458 : CollatzResearch.WordTrace tailWord_2955458 prefixEnd_2955458 1011713672117201993788735 := by
  unfold tailWord_2955458
  simp only [CollatzResearch.WordTrace]
  refine ⟨26948602231721973221536757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71862939284591928590764685 26948602231721973221536757)
  ·
    refine ⟨2526431459223934989519071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 26948602231721973221536757 2526431459223934989519071)
    ·
      refine ⟨3789647188835902484278607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2526431459223934989519071 3789647188835902484278607)
      ·
        refine ⟨5684470783253853726417911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3789647188835902484278607 5684470783253853726417911)
        ·
          refine ⟨8526706174880780589626867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5684470783253853726417911 8526706174880780589626867)
          ·
            refine ⟨12790059262321170884440301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8526706174880780589626867 12790059262321170884440301)
            ·
              refine ⟨4796272223370439081665113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12790059262321170884440301 4796272223370439081665113)
              ·
                refine ⟨3597204167527829311248835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4796272223370439081665113 3597204167527829311248835)
                ·
                  refine ⟨5395806251291743966873253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3597204167527829311248835 5395806251291743966873253)
                  ·
                    refine ⟨1011713672117201993788735, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5395806251291743966873253 1011713672117201993788735)
                    ·
                      rfl

theorem cell22_2955458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 3, 2, 1, 4].length) (baseStart_2955458 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2955458 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2955458 prefixEnd_2955458 := by exact prefixLift 2955458
  have htrace : WordTrace (prefixWord ++ tailWord_2955458) baseStart_2955458 baseEnd_2955458 := by
    simpa [prefixWord, tailWord_2955458, baseEnd_2955458] using wordTrace_append hprefix tailTrace_2955458
  have hstable : (prefixWord ++ tailWord_2955458).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2955458).length < 2 ^ (prefixWord ++ tailWord_2955458).sum := by decide
  have hdescent : baseEnd_2955458 < baseStart_2955458 := by decide
  rcases family_descends (prefixWord ++ tailWord_2955458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2955484 : List Nat := [2, 2, 5, 2, 1, 10]
def baseStart_2955484 : Nat := 118140960795 + 2955484 * 2 ^ 59
def prefixEnd_2955484 : Nat := 4983230072969 + 3 ^ 40 * 2955484 * 2
def baseEnd_2955484 : Nat := 12490402128994402378255

theorem tailTrace_2955484 : CollatzResearch.WordTrace tailWord_2955484 prefixEnd_2955484 12490402128994402378255 := by
  unfold tailWord_2955484
  simp only [CollatzResearch.WordTrace]
  refine ⟨53897678612396849663296753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71863571483195799551062337 53897678612396849663296753)
  ·
    refine ⟨40423258959297637247472565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53897678612396849663296753 40423258959297637247472565)
    ·
      refine ⟨3789680527434153491950553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 40423258959297637247472565 3789680527434153491950553)
      ·
        refine ⟨2842260395575615118962915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3789680527434153491950553 2842260395575615118962915)
        ·
          refine ⟨4263390593363422678444373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2842260395575615118962915 4263390593363422678444373)
          ·
            refine ⟨12490402128994402378255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 4263390593363422678444373 12490402128994402378255)
            ·
              rfl

theorem cell22_2955484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 10].length) (baseStart_2955484 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2955484 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2955484 prefixEnd_2955484 := by exact prefixLift 2955484
  have htrace : WordTrace (prefixWord ++ tailWord_2955484) baseStart_2955484 baseEnd_2955484 := by
    simpa [prefixWord, tailWord_2955484, baseEnd_2955484] using wordTrace_append hprefix tailTrace_2955484
  have hstable : (prefixWord ++ tailWord_2955484).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2955484).length < 2 ^ (prefixWord ++ tailWord_2955484).sum := by decide
  have hdescent : baseEnd_2955484 < baseStart_2955484 := by decide
  rcases family_descends (prefixWord ++ tailWord_2955484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2955490 : List Nat := [3, 3, 4, 1, 1, 1, 1, 4, 4]
def baseStart_2955490 : Nat := 118140960795 + 2955490 * 2 ^ 59
def prefixEnd_2955490 : Nat := 4983230072969 + 3 ^ 40 * 2955490 * 2
def baseEnd_2955490 : Nat := 337241542123721525662879

theorem tailTrace_2955490 : CollatzResearch.WordTrace tailWord_2955490 prefixEnd_2955490 337241542123721525662879 := by
  unfold tailWord_2955490
  simp only [CollatzResearch.WordTrace]
  refine ⟨26948894015692990587827981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71863717375181308234207949 26948894015692990587827981)
  ·
    refine ⟨10105835255884871470435493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26948894015692990587827981 10105835255884871470435493)
    ·
      refine ⟨1894844110478413400706655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10105835255884871470435493 1894844110478413400706655)
      ·
        refine ⟨2842266165717620101059983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1894844110478413400706655 2842266165717620101059983)
        ·
          refine ⟨4263399248576430151589975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2842266165717620101059983 4263399248576430151589975)
          ·
            refine ⟨6395098872864645227384963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4263399248576430151589975 6395098872864645227384963)
            ·
              refine ⟨9592648309296967841077445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6395098872864645227384963 9592648309296967841077445)
              ·
                refine ⟨1798621557993181470202021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9592648309296967841077445 1798621557993181470202021)
                ·
                  refine ⟨337241542123721525662879, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1798621557993181470202021 337241542123721525662879)
                  ·
                    rfl

theorem cell22_2955490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 1, 1, 4, 4].length) (baseStart_2955490 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2955490 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2955490 prefixEnd_2955490 := by exact prefixLift 2955490
  have htrace : WordTrace (prefixWord ++ tailWord_2955490) baseStart_2955490 baseEnd_2955490 := by
    simpa [prefixWord, tailWord_2955490, baseEnd_2955490] using wordTrace_append hprefix tailTrace_2955490
  have hstable : (prefixWord ++ tailWord_2955490).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2955490).length < 2 ^ (prefixWord ++ tailWord_2955490).sum := by decide
  have hdescent : baseEnd_2955490 < baseStart_2955490 := by decide
  rcases family_descends (prefixWord ++ tailWord_2955490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2955501 : List Nat := [1, 5, 1, 2, 4, 1, 1, 7]
def baseStart_2955501 : Nat := 118140960795 + 2955501 * 2 ^ 59
def prefixEnd_2955501 : Nat := 4983230072969 + 3 ^ 40 * 2955501 * 2
def baseEnd_2955501 : Nat := 112414265766218246107067

theorem tailTrace_2955501 : CollatzResearch.WordTrace tailWord_2955501 prefixEnd_2955501 112414265766218246107067 := by
  unfold tailWord_2955501
  simp only [CollatzResearch.WordTrace]
  refine ⟨107795977265732111229962357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71863984843821407486641571 107795977265732111229962357)
  ·
    refine ⟨10105872868662385427808971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 107795977265732111229962357 10105872868662385427808971)
    ·
      refine ⟨15158809302993578141713457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10105872868662385427808971 15158809302993578141713457)
      ·
        refine ⟨11369106977245183606285093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15158809302993578141713457 11369106977245183606285093)
        ·
          refine ⟨2131707558233471926178455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11369106977245183606285093 2131707558233471926178455)
          ·
            refine ⟨3197561337350207889267683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2131707558233471926178455 3197561337350207889267683)
            ·
              refine ⟨4796342006025311833901525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3197561337350207889267683 4796342006025311833901525)
              ·
                refine ⟨112414265766218246107067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4796342006025311833901525 112414265766218246107067)
                ·
                  rfl

theorem cell22_2955501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 4, 1, 1, 7].length) (baseStart_2955501 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2955501 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2955501 prefixEnd_2955501 := by exact prefixLift 2955501
  have htrace : WordTrace (prefixWord ++ tailWord_2955501) baseStart_2955501 baseEnd_2955501 := by
    simpa [prefixWord, tailWord_2955501, baseEnd_2955501] using wordTrace_append hprefix tailTrace_2955501
  have hstable : (prefixWord ++ tailWord_2955501).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2955501).length < 2 ^ (prefixWord ++ tailWord_2955501).sum := by decide
  have hdescent : baseEnd_2955501 < baseStart_2955501 := by decide
  rcases family_descends (prefixWord ++ tailWord_2955501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2955546 : List Nat := [3, 1, 1, 3, 4, 2, 1, 2, 5]
def baseStart_2955546 : Nat := 118140960795 + 2955546 * 2 ^ 59
def prefixEnd_2955546 : Nat := 4983230072969 + 3 ^ 40 * 2955546 * 2
def baseEnd_2955546 : Nat := 337247932105199699196155

theorem tailTrace_2955546 : CollatzResearch.WordTrace tailWord_2955546 prefixEnd_2955546 337247932105199699196155 := by
  unfold tailWord_2955546
  simp only [CollatzResearch.WordTrace]
  refine ⟨26949404637642270978837623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71865079033712722610233661 26949404637642270978837623)
  ·
    refine ⟨40424106956463406468256435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26949404637642270978837623 40424106956463406468256435)
    ·
      refine ⟨60636160434695109702384653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40424106956463406468256435 60636160434695109702384653)
      ·
        refine ⟨22738560163010666138394245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 60636160434695109702384653 22738560163010666138394245)
        ·
          refine ⟨4263480030564499900948921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22738560163010666138394245 4263480030564499900948921)
          ·
            refine ⟨3197610022923374925711691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4263480030564499900948921 3197610022923374925711691)
            ·
              refine ⟨4796415034385062388567537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3197610022923374925711691 4796415034385062388567537)
              ·
                refine ⟨3597311275788796791425653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4796415034385062388567537 3597311275788796791425653)
                ·
                  refine ⟨337247932105199699196155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3597311275788796791425653 337247932105199699196155)
                  ·
                    rfl

theorem cell22_2955546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 2, 1, 2, 5].length) (baseStart_2955546 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2955546 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2955546 prefixEnd_2955546 := by exact prefixLift 2955546
  have htrace : WordTrace (prefixWord ++ tailWord_2955546) baseStart_2955546 baseEnd_2955546 := by
    simpa [prefixWord, tailWord_2955546, baseEnd_2955546] using wordTrace_append hprefix tailTrace_2955546
  have hstable : (prefixWord ++ tailWord_2955546).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2955546).length < 2 ^ (prefixWord ++ tailWord_2955546).sum := by decide
  have hdescent : baseEnd_2955546 < baseStart_2955546 := by decide
  rcases family_descends (prefixWord ++ tailWord_2955546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2955550 : List Nat := [4, 3, 2, 1, 1, 1, 2, 4, 1, 3]
def baseStart_2955550 : Nat := 118140960795 + 2955550 * 2 ^ 59
def prefixEnd_2955550 : Nat := 4983230072969 + 3 ^ 40 * 2955550 * 2
def baseEnd_2955550 : Nat := 1011745165597344420488453

theorem tailTrace_2955550 : CollatzResearch.WordTrace tailWord_2955550 prefixEnd_2955550 1011745165597344420488453 := by
  unfold tailWord_2955550
  simp only [CollatzResearch.WordTrace]
  refine ⟨13474720555319324074812013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 71865176295036395065664069 13474720555319324074812013)
  ·
    refine ⟨5053020208244746528054505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13474720555319324074812013 5053020208244746528054505)
    ·
      refine ⟨3789765156183559896040879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5053020208244746528054505 3789765156183559896040879)
      ·
        refine ⟨5684647734275339844061319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3789765156183559896040879 5684647734275339844061319)
        ·
          refine ⟨8526971601413009766091979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5684647734275339844061319 8526971601413009766091979)
          ·
            refine ⟨12790457402119514649137969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8526971601413009766091979 12790457402119514649137969)
            ·
              refine ⟨9592843051589635986853477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12790457402119514649137969 9592843051589635986853477)
              ·
                refine ⟨1798658072173056747535027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9592843051589635986853477 1798658072173056747535027)
                ·
                  refine ⟨2697987108259585121302541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1798658072173056747535027 2697987108259585121302541)
                  ·
                    refine ⟨1011745165597344420488453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2697987108259585121302541 1011745165597344420488453)
                    ·
                      rfl

theorem cell22_2955550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 2, 4, 1, 3].length) (baseStart_2955550 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2955550 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2955550 prefixEnd_2955550 := by exact prefixLift 2955550
  have htrace : WordTrace (prefixWord ++ tailWord_2955550) baseStart_2955550 baseEnd_2955550 := by
    simpa [prefixWord, tailWord_2955550, baseEnd_2955550] using wordTrace_append hprefix tailTrace_2955550
  have hstable : (prefixWord ++ tailWord_2955550).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2955550).length < 2 ^ (prefixWord ++ tailWord_2955550).sum := by decide
  have hdescent : baseEnd_2955550 < baseStart_2955550 := by decide
  rcases family_descends (prefixWord ++ tailWord_2955550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2955587 : List Nat := [1, 1, 1, 3, 1, 3, 4, 1, 1, 6]
def baseStart_2955587 : Nat := 118140960795 + 2955587 * 2 ^ 59
def prefixEnd_2955587 : Nat := 4983230072969 + 3 ^ 40 * 2955587 * 2
def baseEnd_2955587 : Nat := 1011757831453488657313339

theorem tailTrace_2955587 : CollatzResearch.WordTrace tailWord_2955587 prefixEnd_2955587 1011757831453488657313339 := by
  unfold tailWord_2955587
  simp only [CollatzResearch.WordTrace]
  refine ⟨107799113943420547917593015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71866075962280365278395343 107799113943420547917593015)
  ·
    refine ⟨161698670915130821876389523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107799113943420547917593015 161698670915130821876389523)
    ·
      refine ⟨242548006372696232814584285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 161698670915130821876389523 242548006372696232814584285)
      ·
        refine ⟨90955502389761087305469107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 242548006372696232814584285 90955502389761087305469107)
        ·
          refine ⟨136433253584641630958203661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90955502389761087305469107 136433253584641630958203661)
          ·
            refine ⟨51162470094240611609326373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 136433253584641630958203661 51162470094240611609326373)
            ·
              refine ⟨9592963142670114676748695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 51162470094240611609326373 9592963142670114676748695)
              ·
                refine ⟨14389444714005172015123043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9592963142670114676748695 14389444714005172015123043)
                ·
                  refine ⟨21584167071007758022684565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14389444714005172015123043 21584167071007758022684565)
                  ·
                    refine ⟨1011757831453488657313339, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21584167071007758022684565 1011757831453488657313339)
                    ·
                      rfl

theorem cell22_2955587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 4, 1, 1, 6].length) (baseStart_2955587 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2955587 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2955587 prefixEnd_2955587 := by exact prefixLift 2955587
  have htrace : WordTrace (prefixWord ++ tailWord_2955587) baseStart_2955587 baseEnd_2955587 := by
    simpa [prefixWord, tailWord_2955587, baseEnd_2955587] using wordTrace_append hprefix tailTrace_2955587
  have hstable : (prefixWord ++ tailWord_2955587).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2955587).length < 2 ^ (prefixWord ++ tailWord_2955587).sum := by decide
  have hdescent : baseEnd_2955587 < baseStart_2955587 := by decide
  rcases family_descends (prefixWord ++ tailWord_2955587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2955602 : List Nat := [3, 2, 2, 1, 1, 1, 12]
def baseStart_2955602 : Nat := 118140960795 + 2955602 * 2 ^ 59
def prefixEnd_2955602 : Nat := 4983230072969 + 3 ^ 40 * 2955602 * 2
def baseEnd_2955602 : Nat := 37472702454075319192159

theorem tailTrace_2955602 : CollatzResearch.WordTrace tailWord_2955602 prefixEnd_2955602 37472702454075319192159 := by
  unfold tailWord_2955602
  simp only [CollatzResearch.WordTrace]
  refine ⟨26949915259591551369847265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71866440692244136986259373 26949915259591551369847265)
  ·
    refine ⟨20212436444693663527385449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26949915259591551369847265 20212436444693663527385449)
    ·
      refine ⟨15159327333520247645539087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20212436444693663527385449 15159327333520247645539087)
      ·
        refine ⟨22738991000280371468308631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15159327333520247645539087 22738991000280371468308631)
        ·
          refine ⟨34108486500420557202462947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22738991000280371468308631 34108486500420557202462947)
          ·
            refine ⟨51162729750630835803694421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34108486500420557202462947 51162729750630835803694421)
            ·
              refine ⟨37472702454075319192159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 51162729750630835803694421 37472702454075319192159)
              ·
                rfl

theorem cell22_2955602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 12].length) (baseStart_2955602 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2955602 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2955602 prefixEnd_2955602 := by exact prefixLift 2955602
  have htrace : WordTrace (prefixWord ++ tailWord_2955602) baseStart_2955602 baseEnd_2955602 := by
    simpa [prefixWord, tailWord_2955602, baseEnd_2955602] using wordTrace_append hprefix tailTrace_2955602
  have hstable : (prefixWord ++ tailWord_2955602).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2955602).length < 2 ^ (prefixWord ++ tailWord_2955602).sum := by decide
  have hdescent : baseEnd_2955602 < baseStart_2955602 := by decide
  rcases family_descends (prefixWord ++ tailWord_2955602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2955604 : List Nat := [2, 4, 1, 1, 2, 2, 1, 1, 4, 4]
def baseStart_2955604 : Nat := 118140960795 + 2955604 * 2 ^ 59
def prefixEnd_2955604 : Nat := 4983230072969 + 3 ^ 40 * 2955604 * 2
def baseEnd_2955604 : Nat := 1011763650900906279638287

theorem tailTrace_2955604 : CollatzResearch.WordTrace tailWord_2955604 prefixEnd_2955604 1011763650900906279638287 := by
  unfold tailWord_2955604
  simp only [CollatzResearch.WordTrace]
  refine ⟨53899866992179479910480933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71866489322905973213974577 53899866992179479910480933)
  ·
    refine ⟨10106225061033652483215175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 53899866992179479910480933 10106225061033652483215175)
    ·
      refine ⟨15159337591550478724822763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10106225061033652483215175 15159337591550478724822763)
      ·
        refine ⟨22739006387325718087234145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15159337591550478724822763 22739006387325718087234145)
        ·
          refine ⟨17054254790494288565425609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22739006387325718087234145 17054254790494288565425609)
          ·
            refine ⟨12790691092870716424069207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17054254790494288565425609 12790691092870716424069207)
            ·
              refine ⟨19186036639306074636103811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12790691092870716424069207 19186036639306074636103811)
              ·
                refine ⟨28779054958959111954155717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19186036639306074636103811 28779054958959111954155717)
                ·
                  refine ⟨5396072804804833491404197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28779054958959111954155717 5396072804804833491404197)
                  ·
                    refine ⟨1011763650900906279638287, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5396072804804833491404197 1011763650900906279638287)
                    ·
                      rfl

theorem cell22_2955604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 1, 1, 4, 4].length) (baseStart_2955604 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2955604 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2955604 prefixEnd_2955604 := by exact prefixLift 2955604
  have htrace : WordTrace (prefixWord ++ tailWord_2955604) baseStart_2955604 baseEnd_2955604 := by
    simpa [prefixWord, tailWord_2955604, baseEnd_2955604] using wordTrace_append hprefix tailTrace_2955604
  have hstable : (prefixWord ++ tailWord_2955604).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2955604).length < 2 ^ (prefixWord ++ tailWord_2955604).sum := by decide
  have hdescent : baseEnd_2955604 < baseStart_2955604 := by decide
  rcases family_descends (prefixWord ++ tailWord_2955604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2955614 : List Nat := [4, 4, 2, 1, 1, 2, 2, 1, 5]
def baseStart_2955614 : Nat := 118140960795 + 2955614 * 2 ^ 59
def prefixEnd_2955614 : Nat := 4983230072969 + 3 ^ 40 * 2955614 * 2
def baseEnd_2955614 : Nat := 337255691368423195629419

theorem tailTrace_2955614 : CollatzResearch.WordTrace tailWord_2955614 prefixEnd_2955614 337255691368423195629419 := by
  unfold tailWord_2955614
  simp only [CollatzResearch.WordTrace]
  refine ⟨13475012339290341441103237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 71866732476215154352550597 13475012339290341441103237)
  ·
    refine ⟨2526564813616939020206857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13475012339290341441103237 2526564813616939020206857)
    ·
      refine ⟨1894923610212704265155143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2526564813616939020206857 1894923610212704265155143)
      ·
        refine ⟨2842385415319056397732715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1894923610212704265155143 2842385415319056397732715)
        ·
          refine ⟨4263578122978584596599073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2842385415319056397732715 4263578122978584596599073)
          ·
            refine ⟨3197683592233938447449305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4263578122978584596599073 3197683592233938447449305)
            ·
              refine ⟨2398262694175453835586979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3197683592233938447449305 2398262694175453835586979)
              ·
                refine ⟨3597394041263180753380469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2398262694175453835586979 3597394041263180753380469)
                ·
                  refine ⟨337255691368423195629419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3597394041263180753380469 337255691368423195629419)
                  ·
                    rfl

theorem cell22_2955614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 2, 2, 1, 5].length) (baseStart_2955614 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2955614 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2955614 prefixEnd_2955614 := by exact prefixLift 2955614
  have htrace : WordTrace (prefixWord ++ tailWord_2955614) baseStart_2955614 baseEnd_2955614 := by
    simpa [prefixWord, tailWord_2955614, baseEnd_2955614] using wordTrace_append hprefix tailTrace_2955614
  have hstable : (prefixWord ++ tailWord_2955614).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2955614).length < 2 ^ (prefixWord ++ tailWord_2955614).sum := by decide
  have hdescent : baseEnd_2955614 < baseStart_2955614 := by decide
  rcases family_descends (prefixWord ++ tailWord_2955614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2955623 : List Nat := [1, 1, 5, 1, 3, 1, 4, 1, 2, 3]
def baseStart_2955623 : Nat := 118140960795 + 2955623 * 2 ^ 59
def prefixEnd_2955623 : Nat := 4983230072969 + 3 ^ 40 * 2955623 * 2
def baseEnd_2955623 : Nat := 1011770154989196563413229

theorem tailTrace_2955623 : CollatzResearch.WordTrace tailWord_2955623 prefixEnd_2955623 1011770154989196563413229 := by
  unfold tailWord_2955623
  simp only [CollatzResearch.WordTrace]
  refine ⟨107800426971290126065903523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71866951314193417377269015 107800426971290126065903523)
  ·
    refine ⟨161700640456935189098855285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107800426971290126065903523 161700640456935189098855285)
    ·
      refine ⟨15159435042837673978017683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 161700640456935189098855285 15159435042837673978017683)
      ·
        refine ⟨22739152564256510967026525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15159435042837673978017683 22739152564256510967026525)
        ·
          refine ⟨8527182211596191612634947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22739152564256510967026525 8527182211596191612634947)
          ·
            refine ⟨12790773317394287418952421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8527182211596191612634947 12790773317394287418952421)
            ·
              refine ⟨2398269997011428891053579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12790773317394287418952421 2398269997011428891053579)
              ·
                refine ⟨3597404995517143336580369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2398269997011428891053579 3597404995517143336580369)
                ·
                  refine ⟨2698053746637857502435277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3597404995517143336580369 2698053746637857502435277)
                  ·
                    refine ⟨1011770154989196563413229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2698053746637857502435277 1011770154989196563413229)
                    ·
                      rfl

theorem cell22_2955623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 4, 1, 2, 3].length) (baseStart_2955623 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2955623 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2955623 prefixEnd_2955623 := by exact prefixLift 2955623
  have htrace : WordTrace (prefixWord ++ tailWord_2955623) baseStart_2955623 baseEnd_2955623 := by
    simpa [prefixWord, tailWord_2955623, baseEnd_2955623] using wordTrace_append hprefix tailTrace_2955623
  have hstable : (prefixWord ++ tailWord_2955623).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2955623).length < 2 ^ (prefixWord ++ tailWord_2955623).sum := by decide
  have hdescent : baseEnd_2955623 < baseStart_2955623 := by decide
  rcases family_descends (prefixWord ++ tailWord_2955623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2955679 : List Nat := [1, 1, 2, 5, 1, 1, 3, 1, 2, 5]
def baseStart_2955679 : Nat := 118140960795 + 2955679 * 2 ^ 59
def prefixEnd_2955679 : Nat := 4983230072969 + 3 ^ 40 * 2955679 * 2
def baseEnd_2955679 : Nat := 1011789324933631084013057

theorem tailTrace_2955679 : CollatzResearch.WordTrace tailWord_2955679 prefixEnd_2955679 1011789324933631084013057 := by
  unfold tailWord_2955679
  simp only [CollatzResearch.WordTrace]
  refine ⟨107802469459087247629942091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71868312972724831753294727 107802469459087247629942091)
  ·
    refine ⟨161703704188630871444913137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107802469459087247629942091 161703704188630871444913137)
    ·
      refine ⟨121277778141473153583684853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 161703704188630871444913137 121277778141473153583684853)
      ·
        refine ⟨11369791700763108148470455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 121277778141473153583684853 11369791700763108148470455)
        ·
          refine ⟨17054687551144662222705683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11369791700763108148470455 17054687551144662222705683)
          ·
            refine ⟨25582031326716993334058525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17054687551144662222705683 25582031326716993334058525)
            ·
              refine ⟨9593261747518872500271947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25582031326716993334058525 9593261747518872500271947)
              ·
                refine ⟨14389892621278308750407921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9593261747518872500271947 14389892621278308750407921)
                ·
                  refine ⟨10792419465958731562805941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14389892621278308750407921 10792419465958731562805941)
                  ·
                    refine ⟨1011789324933631084013057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10792419465958731562805941 1011789324933631084013057)
                    ·
                      rfl

theorem cell22_2955679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 3, 1, 2, 5].length) (baseStart_2955679 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2955679 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2955679 prefixEnd_2955679 := by exact prefixLift 2955679
  have htrace : WordTrace (prefixWord ++ tailWord_2955679) baseStart_2955679 baseEnd_2955679 := by
    simpa [prefixWord, tailWord_2955679, baseEnd_2955679] using wordTrace_append hprefix tailTrace_2955679
  have hstable : (prefixWord ++ tailWord_2955679).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2955679).length < 2 ^ (prefixWord ++ tailWord_2955679).sum := by decide
  have hdescent : baseEnd_2955679 < baseStart_2955679 := by decide
  rcases family_descends (prefixWord ++ tailWord_2955679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2955784 : List Nat := [2, 1, 3, 2, 1, 1, 1, 3, 2, 6]
def baseStart_2955784 : Nat := 118140960795 + 2955784 * 2 ^ 59
def prefixEnd_2955784 : Nat := 4983230072969 + 3 ^ 40 * 2955784 * 2
def baseEnd_2955784 : Nat := 1011825268579445810137735

theorem tailTrace_2955784 : CollatzResearch.WordTrace tailWord_2955784 prefixEnd_2955784 1011825268579445810137735 := by
  unfold tailWord_2955784
  simp only [CollatzResearch.WordTrace]
  refine ⟨53903149561853425281257203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71870866082471233708342937 53903149561853425281257203)
  ·
    refine ⟨80854724342780137921885805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53903149561853425281257203 80854724342780137921885805)
    ·
      refine ⟨30320521628542551720707177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 80854724342780137921885805 30320521628542551720707177)
      ·
        refine ⟨22740391221406913790530383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30320521628542551720707177 22740391221406913790530383)
        ·
          refine ⟨34110586832110370685795575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22740391221406913790530383 34110586832110370685795575)
          ·
            refine ⟨51165880248165556028693363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34110586832110370685795575 51165880248165556028693363)
            ·
              refine ⟨76748820372248334043040045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51165880248165556028693363 76748820372248334043040045)
              ·
                refine ⟨28780807639593125266140017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 76748820372248334043040045 28780807639593125266140017)
                ·
                  refine ⟨21585605729694843949605013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28780807639593125266140017 21585605729694843949605013)
                  ·
                    refine ⟨1011825268579445810137735, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21585605729694843949605013 1011825268579445810137735)
                    ·
                      rfl

theorem cell22_2955784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 3, 2, 6].length) (baseStart_2955784 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2955784 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2955784 prefixEnd_2955784 := by exact prefixLift 2955784
  have htrace : WordTrace (prefixWord ++ tailWord_2955784) baseStart_2955784 baseEnd_2955784 := by
    simpa [prefixWord, tailWord_2955784, baseEnd_2955784] using wordTrace_append hprefix tailTrace_2955784
  have hstable : (prefixWord ++ tailWord_2955784).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2955784).length < 2 ^ (prefixWord ++ tailWord_2955784).sum := by decide
  have hdescent : baseEnd_2955784 < baseStart_2955784 := by decide
  rcases family_descends (prefixWord ++ tailWord_2955784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2955837 : List Nat := [1, 4, 1, 3, 2, 1, 4, 2, 1, 3]
def baseStart_2955837 : Nat := 118140960795 + 2955837 * 2 ^ 59
def prefixEnd_2955837 : Nat := 4983230072969 + 3 ^ 40 * 2955837 * 2
def baseEnd_2955837 : Nat := 1011843411562571338562573

theorem tailTrace_2955837 : CollatzResearch.WordTrace tailWord_2955837 prefixEnd_2955837 1011843411562571338562573 := by
  unfold tailWord_2955837
  simp only [CollatzResearch.WordTrace]
  refine ⟨107808232192514840614193765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71872154795009893742795843 107808232192514840614193765)
  ·
    refine ⟨20214043536096532615161331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 107808232192514840614193765 20214043536096532615161331)
    ·
      refine ⟨30321065304144798922741997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20214043536096532615161331 30321065304144798922741997)
      ·
        refine ⟨11370399489054299596028249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30321065304144798922741997 11370399489054299596028249)
        ·
          refine ⟨8527799616790724697021187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11370399489054299596028249 8527799616790724697021187)
          ·
            refine ⟨12791699425186087045531781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8527799616790724697021187 12791699425186087045531781)
            ·
              refine ⟨2398443642222391321037209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12791699425186087045531781 2398443642222391321037209)
              ·
                refine ⟨1798832731666793490777907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2398443642222391321037209 1798832731666793490777907)
                ·
                  refine ⟨2698249097500190236166861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1798832731666793490777907 2698249097500190236166861)
                  ·
                    refine ⟨1011843411562571338562573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2698249097500190236166861 1011843411562571338562573)
                    ·
                      rfl

theorem cell22_2955837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 4, 2, 1, 3].length) (baseStart_2955837 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2955837 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2955837 prefixEnd_2955837 := by exact prefixLift 2955837
  have htrace : WordTrace (prefixWord ++ tailWord_2955837) baseStart_2955837 baseEnd_2955837 := by
    simpa [prefixWord, tailWord_2955837, baseEnd_2955837] using wordTrace_append hprefix tailTrace_2955837
  have hstable : (prefixWord ++ tailWord_2955837).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2955837).length < 2 ^ (prefixWord ++ tailWord_2955837).sum := by decide
  have hdescent : baseEnd_2955837 < baseStart_2955837 := by decide
  rcases family_descends (prefixWord ++ tailWord_2955837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2955876 : List Nat := [2, 3, 1, 1, 2, 2, 1, 4, 1, 5]
def baseStart_2955876 : Nat := 118140960795 + 2955876 * 2 ^ 59
def prefixEnd_2955876 : Nat := 4983230072969 + 3 ^ 40 * 2955876 * 2
def baseEnd_2955876 : Nat := 1011856762059588236837453

theorem tailTrace_2955876 : CollatzResearch.WordTrace tailWord_2955876 prefixEnd_2955876 1011856762059588236837453 := by
  unfold tailWord_2955876
  simp only [CollatzResearch.WordTrace]
  refine ⟨53904827319686775137431741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71873103092915700183242321 53904827319686775137431741)
  ·
    refine ⟨20214310244882540676536903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53904827319686775137431741 20214310244882540676536903)
    ·
      refine ⟨30321465367323811014805355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20214310244882540676536903 30321465367323811014805355)
      ·
        refine ⟨45482198050985716522208033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30321465367323811014805355 45482198050985716522208033)
        ·
          refine ⟨34111648538239287391656025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45482198050985716522208033 34111648538239287391656025)
          ·
            refine ⟨25583736403679465543742019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34111648538239287391656025 25583736403679465543742019)
            ·
              refine ⟨38375604605519198315613029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25583736403679465543742019 38375604605519198315613029)
              ·
                refine ⟨7195425863534849684177443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 38375604605519198315613029 7195425863534849684177443)
                ·
                  refine ⟨10793138795302274526266165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7195425863534849684177443 10793138795302274526266165)
                  ·
                    refine ⟨1011856762059588236837453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10793138795302274526266165 1011856762059588236837453)
                    ·
                      rfl

theorem cell22_2955876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 1, 4, 1, 5].length) (baseStart_2955876 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2955876 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2955876 prefixEnd_2955876 := by exact prefixLift 2955876
  have htrace : WordTrace (prefixWord ++ tailWord_2955876) baseStart_2955876 baseEnd_2955876 := by
    simpa [prefixWord, tailWord_2955876, baseEnd_2955876] using wordTrace_append hprefix tailTrace_2955876
  have hstable : (prefixWord ++ tailWord_2955876).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2955876).length < 2 ^ (prefixWord ++ tailWord_2955876).sum := by decide
  have hdescent : baseEnd_2955876 < baseStart_2955876 := by decide
  rcases family_descends (prefixWord ++ tailWord_2955876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2955880 : List Nat := [2, 1, 4, 3, 2, 1, 1, 3, 1, 4]
def baseStart_2955880 : Nat := 118140960795 + 2955880 * 2 ^ 59
def prefixEnd_2955880 : Nat := 4983230072969 + 3 ^ 40 * 2955880 * 2
def baseEnd_2955880 : Nat := 1011858131341333559737441

theorem tailTrace_2955880 : CollatzResearch.WordTrace tailWord_2955880 prefixEnd_2955880 1011858131341333559737441 := by
  unfold tailWord_2955880
  simp only [CollatzResearch.WordTrace]
  refine ⟨53904900265679529479004547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71873200354239372638672729 53904900265679529479004547)
  ·
    refine ⟨80857350398519294218506821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53904900265679529479004547 80857350398519294218506821)
    ·
      refine ⟨15160753199722367665970029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 80857350398519294218506821 15160753199722367665970029)
      ·
        refine ⟨5685282449895887874738761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15160753199722367665970029 5685282449895887874738761)
        ·
          refine ⟨4263961837421915906054071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5685282449895887874738761 4263961837421915906054071)
          ·
            refine ⟨6395942756132873859081107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4263961837421915906054071 6395942756132873859081107)
            ·
              refine ⟨9593914134199310788621661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6395942756132873859081107 9593914134199310788621661)
              ·
                refine ⟨3597717800324741545733123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9593914134199310788621661 3597717800324741545733123)
                ·
                  refine ⟨5396576700487112318599685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3597717800324741545733123 5396576700487112318599685)
                  ·
                    refine ⟨1011858131341333559737441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5396576700487112318599685 1011858131341333559737441)
                    ·
                      rfl

theorem cell22_2955880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 1, 1, 3, 1, 4].length) (baseStart_2955880 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2955880 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2955880 prefixEnd_2955880 := by exact prefixLift 2955880
  have htrace : WordTrace (prefixWord ++ tailWord_2955880) baseStart_2955880 baseEnd_2955880 := by
    simpa [prefixWord, tailWord_2955880, baseEnd_2955880] using wordTrace_append hprefix tailTrace_2955880
  have hstable : (prefixWord ++ tailWord_2955880).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2955880).length < 2 ^ (prefixWord ++ tailWord_2955880).sum := by decide
  have hdescent : baseEnd_2955880 < baseStart_2955880 := by decide
  rcases family_descends (prefixWord ++ tailWord_2955880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2955951 : List Nat := [1, 1, 2, 1, 2, 5, 2, 1, 7]
def baseStart_2955951 : Nat := 118140960795 + 2955951 * 2 ^ 59
def prefixEnd_2955951 : Nat := 4983230072969 + 3 ^ 40 * 2955951 * 2
def baseEnd_2955951 : Nat := 337294145364104347070741

theorem tailTrace_2955951 : CollatzResearch.WordTrace tailWord_2955951 prefixEnd_2955951 337294145364104347070741 := by
  unfold tailWord_2955951
  simp only [CollatzResearch.WordTrace]
  refine ⟨107812390114101838083843707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71874926742734558722562471 107812390114101838083843707)
  ·
    refine ⟨161718585171152757125765561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107812390114101838083843707 161718585171152757125765561)
    ·
      refine ⟨121288938878364567844324171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 161718585171152757125765561 121288938878364567844324171)
      ·
        refine ⟨181933408317546851766486257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121288938878364567844324171 181933408317546851766486257)
        ·
          refine ⟨136450056238160138824864693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 181933408317546851766486257 136450056238160138824864693)
          ·
            refine ⟨12792192772327513014831065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 136450056238160138824864693 12792192772327513014831065)
            ·
              refine ⟨9594144579245634761123299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12792192772327513014831065 9594144579245634761123299)
              ·
                refine ⟨14391216868868452141684949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9594144579245634761123299 14391216868868452141684949)
                ·
                  refine ⟨337294145364104347070741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14391216868868452141684949 337294145364104347070741)
                  ·
                    rfl

theorem cell22_2955951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 2, 1, 7].length) (baseStart_2955951 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2955951 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2955951 prefixEnd_2955951 := by exact prefixLift 2955951
  have htrace : WordTrace (prefixWord ++ tailWord_2955951) baseStart_2955951 baseEnd_2955951 := by
    simpa [prefixWord, tailWord_2955951, baseEnd_2955951] using wordTrace_append hprefix tailTrace_2955951
  have hstable : (prefixWord ++ tailWord_2955951).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2955951).length < 2 ^ (prefixWord ++ tailWord_2955951).sum := by decide
  have hdescent : baseEnd_2955951 < baseStart_2955951 := by decide
  rcases family_descends (prefixWord ++ tailWord_2955951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2955955 : List Nat := [1, 1, 1, 2, 3, 6, 1, 1, 3, 3]
def baseStart_2955955 : Nat := 118140960795 + 2955955 * 2 ^ 59
def prefixEnd_2955955 : Nat := 4983230072969 + 3 ^ 40 * 2955955 * 2
def baseEnd_2955955 : Nat := 1011883805374058364112211

theorem tailTrace_2955955 : CollatzResearch.WordTrace tailWord_2955955 prefixEnd_2955955 1011883805374058364112211 := by
  unfold tailWord_2955955
  simp only [CollatzResearch.WordTrace]
  refine ⟨107812536006087346766989319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71875024004058231177992879 107812536006087346766989319)
  ·
    refine ⟨161718804009131020150483979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107812536006087346766989319 161718804009131020150483979)
    ·
      refine ⟨242578206013696530225725969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 161718804009131020150483979 242578206013696530225725969)
      ·
        refine ⟨181933654510272397669294477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 242578206013696530225725969 181933654510272397669294477)
        ·
          refine ⟨68225120441352149125985429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 181933654510272397669294477 68225120441352149125985429)
          ·
            refine ⟨3198052520688381990280567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 68225120441352149125985429 3198052520688381990280567)
            ·
              refine ⟨4797078781032572985420851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3198052520688381990280567 4797078781032572985420851)
              ·
                refine ⟨7195618171548859478131277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4797078781032572985420851 7195618171548859478131277)
                ·
                  refine ⟨2698356814330822304299229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7195618171548859478131277 2698356814330822304299229)
                  ·
                    refine ⟨1011883805374058364112211, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2698356814330822304299229 1011883805374058364112211)
                    ·
                      rfl

theorem cell22_2955955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 6, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 6, 1, 1, 3, 3].length) (baseStart_2955955 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2955955 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2955955 prefixEnd_2955955 := by exact prefixLift 2955955
  have htrace : WordTrace (prefixWord ++ tailWord_2955955) baseStart_2955955 baseEnd_2955955 := by
    simpa [prefixWord, tailWord_2955955, baseEnd_2955955] using wordTrace_append hprefix tailTrace_2955955
  have hstable : (prefixWord ++ tailWord_2955955).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2955955).length < 2 ^ (prefixWord ++ tailWord_2955955).sum := by decide
  have hdescent : baseEnd_2955955 < baseStart_2955955 := by decide
  rcases family_descends (prefixWord ++ tailWord_2955955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2955968 : List Nat := [2, 1, 1, 2, 4, 3, 1, 3, 5]
def baseStart_2955968 : Nat := 118140960795 + 2955968 * 2 ^ 59
def prefixEnd_2955968 : Nat := 4983230072969 + 3 ^ 40 * 2955968 * 2
def baseEnd_2955968 : Nat := 337296085179910221179057

theorem tailTrace_2955968 : CollatzResearch.WordTrace tailWord_2955968 prefixEnd_2955968 337296085179910221179057 := by
  unfold tailWord_2955968
  simp only [CollatzResearch.WordTrace]
  refine ⟨53906505077520124993606279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71875340103360166658141705 53906505077520124993606279)
  ·
    refine ⟨80859757616280187490409419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53906505077520124993606279 80859757616280187490409419)
    ·
      refine ⟨121289636424420281235614129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80859757616280187490409419 121289636424420281235614129)
      ·
        refine ⟨90967227318315210926710597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 121289636424420281235614129 90967227318315210926710597)
        ·
          refine ⟨17056355122184102048758237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 90967227318315210926710597 17056355122184102048758237)
          ·
            refine ⟨6396133170819038268284339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17056355122184102048758237 6396133170819038268284339)
            ·
              refine ⟨9594199756228557402426509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6396133170819038268284339 9594199756228557402426509)
              ·
                refine ⟨3597824908585709025909941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9594199756228557402426509 3597824908585709025909941)
                ·
                  refine ⟨337296085179910221179057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3597824908585709025909941 337296085179910221179057)
                  ·
                    rfl

theorem cell22_2955968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 3, 1, 3, 5].length) (baseStart_2955968 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2955968 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2955968 prefixEnd_2955968 := by exact prefixLift 2955968
  have htrace : WordTrace (prefixWord ++ tailWord_2955968) baseStart_2955968 baseEnd_2955968 := by
    simpa [prefixWord, tailWord_2955968, baseEnd_2955968] using wordTrace_append hprefix tailTrace_2955968
  have hstable : (prefixWord ++ tailWord_2955968).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2955968).length < 2 ^ (prefixWord ++ tailWord_2955968).sum := by decide
  have hdescent : baseEnd_2955968 < baseStart_2955968 := by decide
  rcases family_descends (prefixWord ++ tailWord_2955968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2956011 : List Nat := [1, 1, 1, 1, 2, 4, 1, 1, 5, 5]
def baseStart_2956011 : Nat := 118140960795 + 2956011 * 2 ^ 59
def prefixEnd_2956011 : Nat := 4983230072969 + 3 ^ 40 * 2956011 * 2
def baseEnd_2956011 : Nat := 1011902975318492884712039

theorem tailTrace_2956011 : CollatzResearch.WordTrace tailWord_2956011 prefixEnd_2956011 1011902975318492884712039 := by
  unfold tailWord_2956011
  simp only [CollatzResearch.WordTrace]
  refine ⟨107814578493884468331027887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71876385662589645554018591 107814578493884468331027887)
  ·
    refine ⟨161721867740826702496541831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107814578493884468331027887 161721867740826702496541831)
    ·
      refine ⟨242582801611240053744812747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 161721867740826702496541831 242582801611240053744812747)
      ·
        refine ⟨363874202416860080617219121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 242582801611240053744812747 363874202416860080617219121)
        ·
          refine ⟨272905651812645060462914341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 363874202416860080617219121 272905651812645060462914341)
          ·
            refine ⟨51169809714870948836796439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 272905651812645060462914341 51169809714870948836796439)
            ·
              refine ⟨76754714572306423255194659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51169809714870948836796439 76754714572306423255194659)
              ·
                refine ⟨115132071858459634882791989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 76754714572306423255194659 115132071858459634882791989)
                ·
                  refine ⟨10793631736730590770261749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 115132071858459634882791989 10793631736730590770261749)
                  ·
                    refine ⟨1011902975318492884712039, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10793631736730590770261749 1011902975318492884712039)
                    ·
                      rfl

theorem cell22_2956011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 1, 5, 5].length) (baseStart_2956011 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2956011 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2956011 prefixEnd_2956011 := by exact prefixLift 2956011
  have htrace : WordTrace (prefixWord ++ tailWord_2956011) baseStart_2956011 baseEnd_2956011 := by
    simpa [prefixWord, tailWord_2956011, baseEnd_2956011] using wordTrace_append hprefix tailTrace_2956011
  have hstable : (prefixWord ++ tailWord_2956011).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2956011).length < 2 ^ (prefixWord ++ tailWord_2956011).sum := by decide
  have hdescent : baseEnd_2956011 < baseStart_2956011 := by decide
  rcases family_descends (prefixWord ++ tailWord_2956011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2956013 : List Nat := [1, 5, 1, 2, 1, 1, 2, 3, 6]
def baseStart_2956013 : Nat := 118140960795 + 2956013 * 2 ^ 59
def prefixEnd_2956013 : Nat := 4983230072969 + 3 ^ 40 * 2956013 * 2
def baseEnd_2956013 : Nat := 337301219986455182054011

theorem tailTrace_2956013 : CollatzResearch.WordTrace tailWord_2956013 prefixEnd_2956013 337301219986455182054011 := by
  unfold tailWord_2956013
  simp only [CollatzResearch.WordTrace]
  refine ⟨107814651439877222672600693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71876434293251481781733795 107814651439877222672600693)
  ·
    refine ⟨10107623572488489625556315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 107814651439877222672600693 10107623572488489625556315)
    ·
      refine ⟨15161435358732734438334473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10107623572488489625556315 15161435358732734438334473)
      ·
        refine ⟨11371076519049550828750855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15161435358732734438334473 11371076519049550828750855)
        ·
          refine ⟨17056614778574326243126283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11371076519049550828750855 17056614778574326243126283)
          ·
            refine ⟨25584922167861489364689425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17056614778574326243126283 25584922167861489364689425)
            ·
              refine ⟨19188691625896117023517069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25584922167861489364689425 19188691625896117023517069)
              ·
                refine ⟨7195759359711043883818901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19188691625896117023517069 7195759359711043883818901)
                ·
                  refine ⟨337301219986455182054011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7195759359711043883818901 337301219986455182054011)
                  ·
                    rfl

theorem cell22_2956013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 2, 3, 6].length) (baseStart_2956013 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2956013 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2956013 prefixEnd_2956013 := by exact prefixLift 2956013
  have htrace : WordTrace (prefixWord ++ tailWord_2956013) baseStart_2956013 baseEnd_2956013 := by
    simpa [prefixWord, tailWord_2956013, baseEnd_2956013] using wordTrace_append hprefix tailTrace_2956013
  have hstable : (prefixWord ++ tailWord_2956013).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2956013).length < 2 ^ (prefixWord ++ tailWord_2956013).sum := by decide
  have hdescent : baseEnd_2956013 < baseStart_2956013 := by decide
  rcases family_descends (prefixWord ++ tailWord_2956013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2956028 : List Nat := [2, 2, 2, 1, 3, 2, 1, 3, 1, 5]
def baseStart_2956028 : Nat := 118140960795 + 2956028 * 2 ^ 59
def prefixEnd_2956028 : Nat := 4983230072969 + 3 ^ 40 * 2956028 * 2
def baseEnd_2956028 : Nat := 1011908794765910507036987

theorem tailTrace_2956028 : CollatzResearch.WordTrace tailWord_2956028 prefixEnd_2956028 1011908794765910507036987 := by
  unfold tailWord_2956028
  simp only [CollatzResearch.WordTrace]
  refine ⟨53907599267411440117198369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71876799023215253489597825 53907599267411440117198369)
  ·
    refine ⟨40430699450558580087898777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53907599267411440117198369 40430699450558580087898777)
    ·
      refine ⟨30323024587918935065924083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40430699450558580087898777 30323024587918935065924083)
      ·
        refine ⟨45484536881878402598886125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30323024587918935065924083 45484536881878402598886125)
        ·
          refine ⟨17056701330704400974582297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45484536881878402598886125 17056701330704400974582297)
          ·
            refine ⟨12792525998028300730936723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17056701330704400974582297 12792525998028300730936723)
            ·
              refine ⟨19188788997042451096405085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12792525998028300730936723 19188788997042451096405085)
              ·
                refine ⟨7195795873890919161151907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19188788997042451096405085 7195795873890919161151907)
                ·
                  refine ⟨10793693810836378741727861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7195795873890919161151907 10793693810836378741727861)
                  ·
                    refine ⟨1011908794765910507036987, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10793693810836378741727861 1011908794765910507036987)
                    ·
                      rfl

theorem cell22_2956028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 1, 3, 1, 5].length) (baseStart_2956028 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2956028 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2956028 prefixEnd_2956028 := by exact prefixLift 2956028
  have htrace : WordTrace (prefixWord ++ tailWord_2956028) baseStart_2956028 baseEnd_2956028 := by
    simpa [prefixWord, tailWord_2956028, baseEnd_2956028] using wordTrace_append hprefix tailTrace_2956028
  have hstable : (prefixWord ++ tailWord_2956028).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2956028).length < 2 ^ (prefixWord ++ tailWord_2956028).sum := by decide
  have hdescent : baseEnd_2956028 < baseStart_2956028 := by decide
  rcases family_descends (prefixWord ++ tailWord_2956028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2956030 : List Nat := [4, 2, 2, 1, 2, 2, 1, 2, 6]
def baseStart_2956030 : Nat := 118140960795 + 2956030 * 2 ^ 59
def prefixEnd_2956030 : Nat := 4983230072969 + 3 ^ 40 * 2956030 * 2
def baseEnd_2956030 : Nat := 337303159802261056162327

theorem tailTrace_2956030 : CollatzResearch.WordTrace tailWord_2956030 prefixEnd_2956030 337303159802261056162327 := by
  unfold tailWord_2956030
  simp only [CollatzResearch.WordTrace]
  refine ⟨13476908935101954321996193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 71876847653877089717313029 13476908935101954321996193)
  ·
    refine ⟨10107681701326465741497145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13476908935101954321996193 10107681701326465741497145)
    ·
      refine ⟨7580761275994849306122859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10107681701326465741497145 7580761275994849306122859)
      ·
        refine ⟨11371141913992273959184289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7580761275994849306122859 11371141913992273959184289)
        ·
          refine ⟨8528356435494205469388217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11371141913992273959184289 8528356435494205469388217)
          ·
            refine ⟨6396267326620654102041163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8528356435494205469388217 6396267326620654102041163)
            ·
              refine ⟨9594400989930981153061745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6396267326620654102041163 9594400989930981153061745)
              ·
                refine ⟨7195800742448235864796309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9594400989930981153061745 7195800742448235864796309)
                ·
                  refine ⟨337303159802261056162327, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7195800742448235864796309 337303159802261056162327)
                  ·
                    rfl

theorem cell22_2956030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 2, 1, 2, 6].length) (baseStart_2956030 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2956030 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2956030 prefixEnd_2956030 := by exact prefixLift 2956030
  have htrace : WordTrace (prefixWord ++ tailWord_2956030) baseStart_2956030 baseEnd_2956030 := by
    simpa [prefixWord, tailWord_2956030, baseEnd_2956030] using wordTrace_append hprefix tailTrace_2956030
  have hstable : (prefixWord ++ tailWord_2956030).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2956030).length < 2 ^ (prefixWord ++ tailWord_2956030).sum := by decide
  have hdescent : baseEnd_2956030 < baseStart_2956030 := by decide
  rcases family_descends (prefixWord ++ tailWord_2956030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2956041 : List Nat := [1, 2, 1, 1, 3, 2, 2, 10]
def baseStart_2956041 : Nat := 118140960795 + 2956041 * 2 ^ 59
def prefixEnd_2956041 : Nat := 4983230072969 + 3 ^ 40 * 2956041 * 2
def baseEnd_2956041 : Nat := 112434804992398089606883

theorem tailTrace_2956041 : CollatzResearch.WordTrace tailWord_2956041 prefixEnd_2956041 112434804992398089606883 := by
  unfold tailWord_2956041
  simp only [CollatzResearch.WordTrace]
  refine ⟨107815672683775783454619977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71877115122517188969746651 107815672683775783454619977)
  ·
    refine ⟨80861754512831837590964983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107815672683775783454619977 80861754512831837590964983)
    ·
      refine ⟨121292631769247756386447475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80861754512831837590964983 121292631769247756386447475)
      ·
        refine ⟨181938947653871634579671213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121292631769247756386447475 181938947653871634579671213)
        ·
          refine ⟨68227105370201862967376705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 181938947653871634579671213 68227105370201862967376705)
          ·
            refine ⟨51170329027651397225532529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 68227105370201862967376705 51170329027651397225532529)
            ·
              refine ⟨38377746770738547919149397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51170329027651397225532529 38377746770738547919149397)
              ·
                refine ⟨112434804992398089606883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 38377746770738547919149397 112434804992398089606883)
                ·
                  rfl

theorem cell22_2956041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 2, 10].length) (baseStart_2956041 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2956041 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2956041 prefixEnd_2956041 := by exact prefixLift 2956041
  have htrace : WordTrace (prefixWord ++ tailWord_2956041) baseStart_2956041 baseEnd_2956041 := by
    simpa [prefixWord, tailWord_2956041, baseEnd_2956041] using wordTrace_append hprefix tailTrace_2956041
  have hstable : (prefixWord ++ tailWord_2956041).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2956041).length < 2 ^ (prefixWord ++ tailWord_2956041).sum := by decide
  have hdescent : baseEnd_2956041 < baseStart_2956041 := by decide
  rcases family_descends (prefixWord ++ tailWord_2956041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2956073 : List Nat := [1, 2, 1, 1, 1, 1, 1, 4, 7, 3]
def baseStart_2956073 : Nat := 118140960795 + 2956073 * 2 ^ 59
def prefixEnd_2956073 : Nat := 4983230072969 + 3 ^ 40 * 2956073 * 2
def baseEnd_2956073 : Nat := 1011924199185545389661849

theorem tailTrace_2956073 : CollatzResearch.WordTrace tailWord_2956073 prefixEnd_2956073 1011924199185545389661849 := by
  unfold tailWord_2956073
  simp only [CollatzResearch.WordTrace]
  refine ⟨107816839819659852919784873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71877893213106568613189915 107816839819659852919784873)
  ·
    refine ⟨80862629864744889689838655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107816839819659852919784873 80862629864744889689838655)
    ·
      refine ⟨121293944797117334534757983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80862629864744889689838655 121293944797117334534757983)
      ·
        refine ⟨181940917195676001802136975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121293944797117334534757983 181940917195676001802136975)
        ·
          refine ⟨272911375793514002703205463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 181940917195676001802136975 272911375793514002703205463)
          ·
            refine ⟨409367063690271004054808195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 272911375793514002703205463 409367063690271004054808195)
            ·
              refine ⟨614050595535406506082212293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 409367063690271004054808195 614050595535406506082212293)
              ·
                refine ⟨115134486662888719890414805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 614050595535406506082212293 115134486662888719890414805)
                ·
                  refine ⟨2698464531161454372431597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 115134486662888719890414805 2698464531161454372431597)
                  ·
                    refine ⟨1011924199185545389661849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2698464531161454372431597 1011924199185545389661849)
                    ·
                      rfl

theorem cell22_2956073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 4, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 4, 7, 3].length) (baseStart_2956073 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2956073 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2956073 prefixEnd_2956073 := by exact prefixLift 2956073
  have htrace : WordTrace (prefixWord ++ tailWord_2956073) baseStart_2956073 baseEnd_2956073 := by
    simpa [prefixWord, tailWord_2956073, baseEnd_2956073] using wordTrace_append hprefix tailTrace_2956073
  have hstable : (prefixWord ++ tailWord_2956073).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2956073).length < 2 ^ (prefixWord ++ tailWord_2956073).sum := by decide
  have hdescent : baseEnd_2956073 < baseStart_2956073 := by decide
  rcases family_descends (prefixWord ++ tailWord_2956073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2956124 : List Nat := [2, 2, 4, 2, 1, 3, 1, 1, 3, 3]
def baseStart_2956124 : Nat := 118140960795 + 2956124 * 2 ^ 59
def prefixEnd_2956124 : Nat := 4983230072969 + 3 ^ 40 * 2956124 * 2
def baseEnd_2956124 : Nat := 1011941657527798256636693

theorem tailTrace_2956124 : CollatzResearch.WordTrace tailWord_2956124 prefixEnd_2956124 1011941657527798256636693 := by
  unfold tailWord_2956124
  simp only [CollatzResearch.WordTrace]
  refine ⟨53909349971237544314945713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71879133294983392419927617 53909349971237544314945713)
  ·
    refine ⟨40432012478428158236209285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53909349971237544314945713 40432012478428158236209285)
    ·
      refine ⟨7581002339705279669289241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 40432012478428158236209285 7581002339705279669289241)
      ·
        refine ⟨5685751754778959751966931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7581002339705279669289241 5685751754778959751966931)
        ·
          refine ⟨8528627632168439627950397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5685751754778959751966931 8528627632168439627950397)
          ·
            refine ⟨3198235362063164860481399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8528627632168439627950397 3198235362063164860481399)
            ·
              refine ⟨4797353043094747290722099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3198235362063164860481399 4797353043094747290722099)
              ·
                refine ⟨7196029564642120936083149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4797353043094747290722099 7196029564642120936083149)
                ·
                  refine ⟨2698511086740795351031181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7196029564642120936083149 2698511086740795351031181)
                  ·
                    refine ⟨1011941657527798256636693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2698511086740795351031181 1011941657527798256636693)
                    ·
                      rfl

theorem cell22_2956124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 3, 1, 1, 3, 3].length) (baseStart_2956124 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2956124 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2956124 prefixEnd_2956124 := by exact prefixLift 2956124
  have htrace : WordTrace (prefixWord ++ tailWord_2956124) baseStart_2956124 baseEnd_2956124 := by
    simpa [prefixWord, tailWord_2956124, baseEnd_2956124] using wordTrace_append hprefix tailTrace_2956124
  have hstable : (prefixWord ++ tailWord_2956124).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2956124).length < 2 ^ (prefixWord ++ tailWord_2956124).sum := by decide
  have hdescent : baseEnd_2956124 < baseStart_2956124 := by decide
  rcases family_descends (prefixWord ++ tailWord_2956124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2956180 : List Nat := [2, 4, 2, 1, 1, 1, 1, 2, 3, 5]
def baseStart_2956180 : Nat := 118140960795 + 2956180 * 2 ^ 59
def prefixEnd_2956180 : Nat := 4983230072969 + 3 ^ 40 * 2956180 * 2
def baseEnd_2956180 : Nat := 1011960827472232777236521

theorem tailTrace_2956180 : CollatzResearch.WordTrace tailWord_2956180 prefixEnd_2956180 1011960827472232777236521 := by
  unfold tailWord_2956180
  simp only [CollatzResearch.WordTrace]
  refine ⟨53910371215136105096964997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71880494953514806795953329 53910371215136105096964997)
  ·
    refine ⟨10108194602838019705680937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 53910371215136105096964997 10108194602838019705680937)
    ·
      refine ⟨7581145952128514779260703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10108194602838019705680937 7581145952128514779260703)
      ·
        refine ⟨11371718928192772168891055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7581145952128514779260703 11371718928192772168891055)
        ·
          refine ⟨17057578392289158253336583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11371718928192772168891055 17057578392289158253336583)
          ·
            refine ⟨25586367588433737380004875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17057578392289158253336583 25586367588433737380004875)
            ·
              refine ⟨38379551382650606070007313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25586367588433737380004875 38379551382650606070007313)
              ·
                refine ⟨28784663536987954552505485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38379551382650606070007313 28784663536987954552505485)
                ·
                  refine ⟨10794248826370482957189557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28784663536987954552505485 10794248826370482957189557)
                  ·
                    refine ⟨1011960827472232777236521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10794248826370482957189557 1011960827472232777236521)
                    ·
                      rfl

theorem cell22_2956180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 1, 2, 3, 5].length) (baseStart_2956180 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2956180 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2956180 prefixEnd_2956180 := by exact prefixLift 2956180
  have htrace : WordTrace (prefixWord ++ tailWord_2956180) baseStart_2956180 baseEnd_2956180 := by
    simpa [prefixWord, tailWord_2956180, baseEnd_2956180] using wordTrace_append hprefix tailTrace_2956180
  have hstable : (prefixWord ++ tailWord_2956180).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2956180).length < 2 ^ (prefixWord ++ tailWord_2956180).sum := by decide
  have hdescent : baseEnd_2956180 < baseStart_2956180 := by decide
  rcases family_descends (prefixWord ++ tailWord_2956180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2956223 : List Nat := [1, 1, 2, 2, 2, 1, 2, 2, 1, 8]
def baseStart_2956223 : Nat := 118140960795 + 2956223 * 2 ^ 59
def prefixEnd_2956223 : Nat := 4983230072969 + 3 ^ 40 * 2956223 * 2
def baseEnd_2956223 : Nat := 1011975547250994998411389

theorem tailTrace_2956223 : CollatzResearch.WordTrace tailWord_2956223 prefixEnd_2956223 1011975547250994998411389 := by
  unfold tailWord_2956223
  simp only [CollatzResearch.WordTrace]
  refine ⟨107822310769116428537745323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71881540512744285691830215 107822310769116428537745323)
  ·
    refine ⟨161733466153674642806617985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107822310769116428537745323 161733466153674642806617985)
    ·
      refine ⟨121300099615255982104963489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 161733466153674642806617985 121300099615255982104963489)
      ·
        refine ⟨90975074711441986578722617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 121300099615255982104963489 90975074711441986578722617)
        ·
          refine ⟨68231306033581489934041963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 90975074711441986578722617 68231306033581489934041963)
          ·
            refine ⟨102346959050372234901062945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68231306033581489934041963 102346959050372234901062945)
            ·
              refine ⟨76760219287779176175797209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 102346959050372234901062945 76760219287779176175797209)
              ·
                refine ⟨57570164465834382131847907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 76760219287779176175797209 57570164465834382131847907)
                ·
                  refine ⟨86355246698751573197771861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 57570164465834382131847907 86355246698751573197771861)
                  ·
                    refine ⟨1011975547250994998411389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 86355246698751573197771861 1011975547250994998411389)
                    ·
                      rfl

theorem cell22_2956223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 2, 1, 8].length) (baseStart_2956223 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2956223 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2956223 prefixEnd_2956223 := by exact prefixLift 2956223
  have htrace : WordTrace (prefixWord ++ tailWord_2956223) baseStart_2956223 baseEnd_2956223 := by
    simpa [prefixWord, tailWord_2956223, baseEnd_2956223] using wordTrace_append hprefix tailTrace_2956223
  have hstable : (prefixWord ++ tailWord_2956223).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2956223).length < 2 ^ (prefixWord ++ tailWord_2956223).sum := by decide
  have hdescent : baseEnd_2956223 < baseStart_2956223 := by decide
  rcases family_descends (prefixWord ++ tailWord_2956223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2956261 : List Nat := [1, 3, 1, 6, 2, 1, 2, 6]
def baseStart_2956261 : Nat := 118140960795 + 2956261 * 2 ^ 59
def prefixEnd_2956261 : Nat := 4983230072969 + 3 ^ 40 * 2956261 * 2
def baseEnd_2956261 : Nat := 112443172825286173995697

theorem tailTrace_2956261 : CollatzResearch.WordTrace tailWord_2956261 prefixEnd_2956261 112443172825286173995697 := by
  unfold tailWord_2956261
  simp only [CollatzResearch.WordTrace]
  refine ⟨107823696742978761027628637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71882464495319174018419091 107823696742978761027628637)
  ·
    refine ⟨40433886278617035385360739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 107823696742978761027628637 40433886278617035385360739)
    ·
      refine ⟨60650829417925553078041109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40433886278617035385360739 60650829417925553078041109)
      ·
        refine ⟨2843007628965260300533177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 60650829417925553078041109 2843007628965260300533177)
        ·
          refine ⟨2132255721723945225399883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2843007628965260300533177 2132255721723945225399883)
          ·
            refine ⟨3198383582585917838099825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2132255721723945225399883 3198383582585917838099825)
            ·
              refine ⟨2398787686939438378574869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3198383582585917838099825 2398787686939438378574869)
              ·
                refine ⟨112443172825286173995697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2398787686939438378574869 112443172825286173995697)
                ·
                  rfl

theorem cell22_2956261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 2, 1, 2, 6].length) (baseStart_2956261 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2956261 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2956261 prefixEnd_2956261 := by exact prefixLift 2956261
  have htrace : WordTrace (prefixWord ++ tailWord_2956261) baseStart_2956261 baseEnd_2956261 := by
    simpa [prefixWord, tailWord_2956261, baseEnd_2956261] using wordTrace_append hprefix tailTrace_2956261
  have hstable : (prefixWord ++ tailWord_2956261).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2956261).length < 2 ^ (prefixWord ++ tailWord_2956261).sum := by decide
  have hdescent : baseEnd_2956261 < baseStart_2956261 := by decide
  rcases family_descends (prefixWord ++ tailWord_2956261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2956285 : List Nat := [1, 4, 1, 1, 1, 2, 1, 2, 5, 4]
def baseStart_2956285 : Nat := 118140960795 + 2956285 * 2 ^ 59
def prefixEnd_2956285 : Nat := 4983230072969 + 3 ^ 40 * 2956285 * 2
def baseEnd_2956285 : Nat := 1011996771118047503361199

theorem tailTrace_2956285 : CollatzResearch.WordTrace tailWord_2956285 prefixEnd_2956285 1011996771118047503361199 := by
  unfold tailWord_2956285
  simp only [CollatzResearch.WordTrace]
  refine ⟨107824572094891813126502309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71883048063261208751001539 107824572094891813126502309)
  ·
    refine ⟨20217107267792214961219183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 107824572094891813126502309 20217107267792214961219183)
    ·
      refine ⟨30325660901688322441828775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20217107267792214961219183 30325660901688322441828775)
      ·
        refine ⟨45488491352532483662743163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30325660901688322441828775 45488491352532483662743163)
        ·
          refine ⟨68232737028798725494114745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45488491352532483662743163 68232737028798725494114745)
          ·
            refine ⟨51174552771599044120586059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 68232737028798725494114745 51174552771599044120586059)
            ·
              refine ⟨76761829157398566180879089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51174552771599044120586059 76761829157398566180879089)
              ·
                refine ⟨57571371868048924635659317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 76761829157398566180879089 57571371868048924635659317)
                ·
                  refine ⟨5397316112629586684593061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 57571371868048924635659317 5397316112629586684593061)
                  ·
                    refine ⟨1011996771118047503361199, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5397316112629586684593061 1011996771118047503361199)
                    ·
                      rfl

theorem cell22_2956285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 2, 5, 4].length) (baseStart_2956285 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2956285 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2956285 prefixEnd_2956285 := by exact prefixLift 2956285
  have htrace : WordTrace (prefixWord ++ tailWord_2956285) baseStart_2956285 baseEnd_2956285 := by
    simpa [prefixWord, tailWord_2956285, baseEnd_2956285] using wordTrace_append hprefix tailTrace_2956285
  have hstable : (prefixWord ++ tailWord_2956285).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2956285).length < 2 ^ (prefixWord ++ tailWord_2956285).sum := by decide
  have hdescent : baseEnd_2956285 < baseStart_2956285 := by decide
  rcases family_descends (prefixWord ++ tailWord_2956285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2956319 : List Nat := [1, 1, 2, 4, 1, 5, 1, 2, 1, 4]
def baseStart_2956319 : Nat := 118140960795 + 2956319 * 2 ^ 59
def prefixEnd_2956319 : Nat := 4983230072969 + 3 ^ 40 * 2956319 * 2
def baseEnd_2956319 : Nat := 1012008410012882748011095

theorem tailTrace_2956319 : CollatzResearch.WordTrace tailWord_2956319 prefixEnd_2956319 1012008410012882748011095 := by
  unfold tailWord_2956319
  simp only [CollatzResearch.WordTrace]
  refine ⟨107825812176768636933240011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71883874784512424622160007 107825812176768636933240011)
  ·
    refine ⟨161738718265152955399860017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107825812176768636933240011 161738718265152955399860017)
    ·
      refine ⟨121304038698864716549895013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 161738718265152955399860017 121304038698864716549895013)
      ·
        refine ⟨22744507256037134353105315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 121304038698864716549895013 22744507256037134353105315)
        ·
          refine ⟨34116760884055701529657973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22744507256037134353105315 34116760884055701529657973)
          ·
            refine ⟨3198446332880222018405435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 34116760884055701529657973 3198446332880222018405435)
            ·
              refine ⟨4797669499320333027608153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3198446332880222018405435 4797669499320333027608153)
              ·
                refine ⟨3598252124490249770706115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4797669499320333027608153 3598252124490249770706115)
                ·
                  refine ⟨5397378186735374656059173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3598252124490249770706115 5397378186735374656059173)
                  ·
                    refine ⟨1012008410012882748011095, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5397378186735374656059173 1012008410012882748011095)
                    ·
                      rfl

theorem cell22_2956319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 5, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 5, 1, 2, 1, 4].length) (baseStart_2956319 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2956319 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2956319 prefixEnd_2956319 := by exact prefixLift 2956319
  have htrace : WordTrace (prefixWord ++ tailWord_2956319) baseStart_2956319 baseEnd_2956319 := by
    simpa [prefixWord, tailWord_2956319, baseEnd_2956319] using wordTrace_append hprefix tailTrace_2956319
  have hstable : (prefixWord ++ tailWord_2956319).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2956319).length < 2 ^ (prefixWord ++ tailWord_2956319).sum := by decide
  have hdescent : baseEnd_2956319 < baseStart_2956319 := by decide
  rcases family_descends (prefixWord ++ tailWord_2956319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2956334 : List Nat := [4, 1, 3, 1, 1, 1, 2, 5, 4]
def baseStart_2956334 : Nat := 118140960795 + 2956334 * 2 ^ 59
def prefixEnd_2956334 : Nat := 4983230072969 + 3 ^ 40 * 2956334 * 2
def baseEnd_2956334 : Nat := 337337848273142569628683

theorem tailTrace_2956334 : CollatzResearch.WordTrace tailWord_2956334 prefixEnd_2956334 337337848273142569628683 := by
  unfold tailWord_2956334
  simp only [CollatzResearch.WordTrace]
  refine ⟨13478294908964286811879507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 71884239514476196330024037 13478294908964286811879507)
  ·
    refine ⟨20217442363446430217819261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13478294908964286811879507 20217442363446430217819261)
    ·
      refine ⟨7581540886292411331682223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20217442363446430217819261 7581540886292411331682223)
      ·
        refine ⟨11372311329438616997523335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7581540886292411331682223 11372311329438616997523335)
        ·
          refine ⟨17058466994157925496285003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11372311329438616997523335 17058466994157925496285003)
          ·
            refine ⟨25587700491236888244427505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17058466994157925496285003 25587700491236888244427505)
            ·
              refine ⟨19190775368427666183320629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25587700491236888244427505 19190775368427666183320629)
              ·
                refine ⟨1799135190790093704686309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 19190775368427666183320629 1799135190790093704686309)
                ·
                  refine ⟨337337848273142569628683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1799135190790093704686309 337337848273142569628683)
                  ·
                    rfl

theorem cell22_2956334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 2, 5, 4].length) (baseStart_2956334 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2956334 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2956334 prefixEnd_2956334 := by exact prefixLift 2956334
  have htrace : WordTrace (prefixWord ++ tailWord_2956334) baseStart_2956334 baseEnd_2956334 := by
    simpa [prefixWord, tailWord_2956334, baseEnd_2956334] using wordTrace_append hprefix tailTrace_2956334
  have hstable : (prefixWord ++ tailWord_2956334).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2956334).length < 2 ^ (prefixWord ++ tailWord_2956334).sum := by decide
  have hdescent : baseEnd_2956334 < baseStart_2956334 := by decide
  rcases family_descends (prefixWord ++ tailWord_2956334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2956345 : List Nat := [1, 2, 1, 5, 2, 11]
def baseStart_2956345 : Nat := 118140960795 + 2956345 * 2 ^ 59
def prefixEnd_2956345 : Nat := 4983230072969 + 3 ^ 40 * 2956345 * 2
def baseEnd_2956345 : Nat := 12494040868447251195815

theorem tailTrace_2956345 : CollatzResearch.WordTrace tailWord_2956345 prefixEnd_2956345 12494040868447251195815 := by
  unfold tailWord_2956345
  simp only [CollatzResearch.WordTrace]
  refine ⟨107826760474674443373686489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71884506983116295582457659 107826760474674443373686489)
  ·
    refine ⟨80870070356005832530264867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107826760474674443373686489 80870070356005832530264867)
    ·
      refine ⟨121305105534008748795397301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80870070356005832530264867 121305105534008748795397301)
      ·
        refine ⟨11372353643813320199568497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 121305105534008748795397301 11372353643813320199568497)
        ·
          refine ⟨8529265232859990149676373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11372353643813320199568497 8529265232859990149676373)
          ·
            refine ⟨12494040868447251195815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 8529265232859990149676373 12494040868447251195815)
            ·
              rfl

theorem cell22_2956345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 11].length) (baseStart_2956345 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2956345 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2956345 prefixEnd_2956345 := by exact prefixLift 2956345
  have htrace : WordTrace (prefixWord ++ tailWord_2956345) baseStart_2956345 baseEnd_2956345 := by
    simpa [prefixWord, tailWord_2956345, baseEnd_2956345] using wordTrace_append hprefix tailTrace_2956345
  have hstable : (prefixWord ++ tailWord_2956345).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2956345).length < 2 ^ (prefixWord ++ tailWord_2956345).sum := by decide
  have hdescent : baseEnd_2956345 < baseStart_2956345 := by decide
  rcases family_descends (prefixWord ++ tailWord_2956345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2956349 : List Nat := [1, 4, 1, 3, 1, 2, 1, 4, 2, 3]
def baseStart_2956349 : Nat := 118140960795 + 2956349 * 2 ^ 59
def prefixEnd_2956349 : Nat := 4983230072969 + 3 ^ 40 * 2956349 * 2
def baseEnd_2956349 : Nat := 1012018679625972669761003

theorem tailTrace_2956349 : CollatzResearch.WordTrace tailWord_2956349 prefixEnd_2956349 1012018679625972669761003 := by
  unfold tailWord_2956349
  simp only [CollatzResearch.WordTrace]
  refine ⟨107826906366659952056832101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71884604244439968037888067 107826906366659952056832101)
  ·
    refine ⟨20217544943748741010656019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 107826906366659952056832101 20217544943748741010656019)
    ·
      refine ⟨30326317415623111515984029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20217544943748741010656019 30326317415623111515984029)
      ·
        refine ⟨11372369030858666818494011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30326317415623111515984029 11372369030858666818494011)
        ·
          refine ⟨17058553546288000227741017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11372369030858666818494011 17058553546288000227741017)
          ·
            refine ⟨12793915159716000170805763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17058553546288000227741017 12793915159716000170805763)
            ·
              refine ⟨19190872739574000256208645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12793915159716000170805763 19190872739574000256208645)
              ·
                refine ⟨3598288638670125048039121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19190872739574000256208645 3598288638670125048039121)
                ·
                  refine ⟨2698716479002593786029341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3598288638670125048039121 2698716479002593786029341)
                  ·
                    refine ⟨1012018679625972669761003, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2698716479002593786029341 1012018679625972669761003)
                    ·
                      rfl

theorem cell22_2956349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 1, 4, 2, 3].length) (baseStart_2956349 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2956349 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2956349 prefixEnd_2956349 := by exact prefixLift 2956349
  have htrace : WordTrace (prefixWord ++ tailWord_2956349) baseStart_2956349 baseEnd_2956349 := by
    simpa [prefixWord, tailWord_2956349, baseEnd_2956349] using wordTrace_append hprefix tailTrace_2956349
  have hstable : (prefixWord ++ tailWord_2956349).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2956349).length < 2 ^ (prefixWord ++ tailWord_2956349).sum := by decide
  have hdescent : baseEnd_2956349 < baseStart_2956349 := by decide
  rcases family_descends (prefixWord ++ tailWord_2956349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2956375 : List Nat := [1, 1, 3, 2, 2, 1, 1, 1, 4, 6]
def baseStart_2956375 : Nat := 118140960795 + 2956375 * 2 ^ 59
def prefixEnd_2956375 : Nat := 4983230072969 + 3 ^ 40 * 2956375 * 2
def baseEnd_2956375 : Nat := 1012027579957317268610923

theorem tailTrace_2956375 : CollatzResearch.WordTrace tailWord_2956375 prefixEnd_2956375 1012027579957317268610923 := by
  unfold tailWord_2956375
  simp only [CollatzResearch.WordTrace]
  refine ⟨107827854664565758497278579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71885236443043838998185719 107827854664565758497278579)
  ·
    refine ⟨161741781996848637745917869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107827854664565758497278579 161741781996848637745917869)
    ·
      refine ⟨60653168248818239154719201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 161741781996848637745917869 60653168248818239154719201)
      ·
        refine ⟨45489876186613679366039401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60653168248818239154719201 45489876186613679366039401)
        ·
          refine ⟨34117407139960259524529551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45489876186613679366039401 34117407139960259524529551)
          ·
            refine ⟨51176110709940389286794327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34117407139960259524529551 51176110709940389286794327)
            ·
              refine ⟨76764166064910583930191491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51176110709940389286794327 76764166064910583930191491)
              ·
                refine ⟨115146249097365875895287237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 76764166064910583930191491 115146249097365875895287237)
                ·
                  refine ⟨21589921705756101730366357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 115146249097365875895287237 21589921705756101730366357)
                  ·
                    refine ⟨1012027579957317268610923, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21589921705756101730366357 1012027579957317268610923)
                    ·
                      rfl

theorem cell22_2956375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 1, 4, 6].length) (baseStart_2956375 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2956375 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2956375 prefixEnd_2956375 := by exact prefixLift 2956375
  have htrace : WordTrace (prefixWord ++ tailWord_2956375) baseStart_2956375 baseEnd_2956375 := by
    simpa [prefixWord, tailWord_2956375, baseEnd_2956375] using wordTrace_append hprefix tailTrace_2956375
  have hstable : (prefixWord ++ tailWord_2956375).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2956375).length < 2 ^ (prefixWord ++ tailWord_2956375).sum := by decide
  have hdescent : baseEnd_2956375 < baseStart_2956375 := by decide
  rcases family_descends (prefixWord ++ tailWord_2956375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2956514 : List Nat := [3, 3, 4, 12]
def baseStart_2956514 : Nat := 118140960795 + 2956514 * 2 ^ 59
def prefixEnd_2956514 : Nat := 4983230072969 + 3 ^ 40 * 2956514 * 2
def baseEnd_2956514 : Nat := 1388306121396388531393

theorem tailTrace_2956514 : CollatzResearch.WordTrace tailWord_2956514 prefixEnd_2956514 1388306121396388531393 := by
  unfold tailWord_2956514
  simp only [CollatzResearch.WordTrace]
  refine ⟨26958231102765546309147149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71888616274041456824392397 26958231102765546309147149)
  ·
    refine ⟨10109336663537079865930181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26958231102765546309147149 10109336663537079865930181)
    ·
      refine ⟨1895500624413202474861909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10109336663537079865930181 1895500624413202474861909)
      ·
        refine ⟨1388306121396388531393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 12 1895500624413202474861909 1388306121396388531393)
        ·
          rfl

theorem cell22_2956514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 12].length) (baseStart_2956514 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2956514 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2956514 prefixEnd_2956514 := by exact prefixLift 2956514
  have htrace : WordTrace (prefixWord ++ tailWord_2956514) baseStart_2956514 baseEnd_2956514 := by
    simpa [prefixWord, tailWord_2956514, baseEnd_2956514] using wordTrace_append hprefix tailTrace_2956514
  have hstable : (prefixWord ++ tailWord_2956514).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2956514).length < 2 ^ (prefixWord ++ tailWord_2956514).sum := by decide
  have hdescent : baseEnd_2956514 < baseStart_2956514 := by decide
  rcases family_descends (prefixWord ++ tailWord_2956514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2956529 : List Nat := [1, 2, 2, 2, 2, 1, 1, 5, 3, 3]
def baseStart_2956529 : Nat := 118140960795 + 2956529 * 2 ^ 59
def prefixEnd_2956529 : Nat := 4983230072969 + 3 ^ 40 * 2956529 * 2
def baseEnd_2956529 : Nat := 1012080297304512200260451

theorem tailTrace_2956529 : CollatzResearch.WordTrace tailWord_2956529 prefixEnd_2956529 1012080297304512200260451 := by
  unfold tailWord_2956529
  simp only [CollatzResearch.WordTrace]
  refine ⟨107833471506007842798384641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71888981004005228532256427 107833471506007842798384641)
  ·
    refine ⟨80875103629505882098788481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107833471506007842798384641 80875103629505882098788481)
    ·
      refine ⟨60656327722129411574091361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80875103629505882098788481 60656327722129411574091361)
      ·
        refine ⟨45492245791597058680568521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60656327722129411574091361 45492245791597058680568521)
        ·
          refine ⟨34119184343697794010426391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45492245791597058680568521 34119184343697794010426391)
          ·
            refine ⟨51178776515546691015639587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34119184343697794010426391 51178776515546691015639587)
            ·
              refine ⟨76768164773320036523459381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51178776515546691015639587 76768164773320036523459381)
              ·
                refine ⟨7197015447498753424074317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 76768164773320036523459381 7197015447498753424074317)
                ·
                  refine ⟨2698880792812032534027869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7197015447498753424074317 2698880792812032534027869)
                  ·
                    refine ⟨1012080297304512200260451, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2698880792812032534027869 1012080297304512200260451)
                    ·
                      rfl

theorem cell22_2956529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 5, 3, 3].length) (baseStart_2956529 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2956529 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2956529 prefixEnd_2956529 := by exact prefixLift 2956529
  have htrace : WordTrace (prefixWord ++ tailWord_2956529) baseStart_2956529 baseEnd_2956529 := by
    simpa [prefixWord, tailWord_2956529, baseEnd_2956529] using wordTrace_append hprefix tailTrace_2956529
  have hstable : (prefixWord ++ tailWord_2956529).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2956529).length < 2 ^ (prefixWord ++ tailWord_2956529).sum := by decide
  have hdescent : baseEnd_2956529 < baseStart_2956529 := by decide
  rcases family_descends (prefixWord ++ tailWord_2956529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2956604 : List Nat := [2, 2, 2, 2, 1, 3, 2, 2, 6]
def baseStart_2956604 : Nat := 118140960795 + 2956604 * 2 ^ 59
def prefixEnd_2956604 : Nat := 4983230072969 + 3 ^ 40 * 2956604 * 2
def baseEnd_2956604 : Nat := 337368657112412334878407

theorem tailTrace_2956604 : CollatzResearch.WordTrace tailWord_2956604 prefixEnd_2956604 337368657112412334878407 := by
  unfold tailWord_2956604
  simp only [CollatzResearch.WordTrace]
  refine ⟨53918103490368065303682433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71890804653824087071576577 53918103490368065303682433)
  ·
    refine ⟨40438577617776048977761825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53918103490368065303682433 40438577617776048977761825)
    ·
      refine ⟨30328933213332036733321369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40438577617776048977761825 30328933213332036733321369)
      ·
        refine ⟨22746699909999027549991027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30328933213332036733321369 22746699909999027549991027)
        ·
          refine ⟨34120049864998541324986541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22746699909999027549991027 34120049864998541324986541)
          ·
            refine ⟨12795018699374452996869953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34120049864998541324986541 12795018699374452996869953)
            ·
              refine ⟨9596264024530839747652465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12795018699374452996869953 9596264024530839747652465)
              ·
                refine ⟨7197198018398129810739349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9596264024530839747652465 7197198018398129810739349)
                ·
                  refine ⟨337368657112412334878407, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7197198018398129810739349 337368657112412334878407)
                  ·
                    rfl

theorem cell22_2956604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 2, 2, 6].length) (baseStart_2956604 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2956604 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2956604 prefixEnd_2956604 := by exact prefixLift 2956604
  have htrace : WordTrace (prefixWord ++ tailWord_2956604) baseStart_2956604 baseEnd_2956604 := by
    simpa [prefixWord, tailWord_2956604, baseEnd_2956604] using wordTrace_append hprefix tailTrace_2956604
  have hstable : (prefixWord ++ tailWord_2956604).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2956604).length < 2 ^ (prefixWord ++ tailWord_2956604).sum := by decide
  have hdescent : baseEnd_2956604 < baseStart_2956604 := by decide
  rcases family_descends (prefixWord ++ tailWord_2956604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2956634 : List Nat := [3, 1, 1, 2, 1, 2, 3, 1, 4, 4]
def baseStart_2956634 : Nat := 118140960795 + 2956634 * 2 ^ 59
def prefixEnd_2956634 : Nat := 4983230072969 + 3 ^ 40 * 2956634 * 2
def baseEnd_2956634 : Nat := 1012116240950326926385129

theorem tailTrace_2956634 : CollatzResearch.WordTrace tailWord_2956634 prefixEnd_2956634 1012116240950326926385129 := by
  unfold tailWord_2956634
  simp only [CollatzResearch.WordTrace]
  refine ⟨26959325292656861432739239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71891534113751630487304637 26959325292656861432739239)
  ·
    refine ⟨40438987938985292149108859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26959325292656861432739239 40438987938985292149108859)
    ·
      refine ⟨60658481908477938223663289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40438987938985292149108859 60658481908477938223663289)
      ·
        refine ⟨45493861431358453667747467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60658481908477938223663289 45493861431358453667747467)
        ·
          refine ⟨68240792147037680501621201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45493861431358453667747467 68240792147037680501621201)
          ·
            refine ⟨51180594110278260376215901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 68240792147037680501621201 51180594110278260376215901)
            ·
              refine ⟨19192722791354347641080963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 51180594110278260376215901 19192722791354347641080963)
              ·
                refine ⟨28789084187031521461621445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19192722791354347641080963 28789084187031521461621445)
                ·
                  refine ⟨5397953285068410274054021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28789084187031521461621445 5397953285068410274054021)
                  ·
                    refine ⟨1012116240950326926385129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5397953285068410274054021 1012116240950326926385129)
                    ·
                      rfl

theorem cell22_2956634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 3, 1, 4, 4].length) (baseStart_2956634 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2956634 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2956634 prefixEnd_2956634 := by exact prefixLift 2956634
  have htrace : WordTrace (prefixWord ++ tailWord_2956634) baseStart_2956634 baseEnd_2956634 := by
    simpa [prefixWord, tailWord_2956634, baseEnd_2956634] using wordTrace_append hprefix tailTrace_2956634
  have hstable : (prefixWord ++ tailWord_2956634).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2956634).length < 2 ^ (prefixWord ++ tailWord_2956634).sum := by decide
  have hdescent : baseEnd_2956634 < baseStart_2956634 := by decide
  rcases family_descends (prefixWord ++ tailWord_2956634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2956653 : List Nat := [1, 5, 1, 1, 1, 4, 1, 3, 2, 3]
def baseStart_2956653 : Nat := 118140960795 + 2956653 * 2 ^ 59
def prefixEnd_2956653 : Nat := 4983230072969 + 3 ^ 40 * 2956653 * 2
def baseEnd_2956653 : Nat := 1012122745038617210160071

theorem tailTrace_2956653 : CollatzResearch.WordTrace tailWord_2956653 prefixEnd_2956653 1012122745038617210160071 := by
  unfold tailWord_2956653
  simp only [CollatzResearch.WordTrace]
  refine ⟨107837994157558611975898613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71891996105039074650599075 107837994157558611975898613)
  ·
    refine ⟨10109811952271119872740495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 107837994157558611975898613 10109811952271119872740495)
    ·
      refine ⟨15164717928406679809110743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10109811952271119872740495 15164717928406679809110743)
      ·
        refine ⟨22747076892610019713666115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15164717928406679809110743 22747076892610019713666115)
        ·
          refine ⟨34120615338915029570499173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22747076892610019713666115 34120615338915029570499173)
          ·
            refine ⟨6397615376046568044468595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 34120615338915029570499173 6397615376046568044468595)
            ·
              refine ⟨9596423064069852066702893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6397615376046568044468595 9596423064069852066702893)
              ·
                refine ⟨3598658649026194525013585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9596423064069852066702893 3598658649026194525013585)
                ·
                  refine ⟨2698993986769645893760189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3598658649026194525013585 2698993986769645893760189)
                  ·
                    refine ⟨1012122745038617210160071, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2698993986769645893760189 1012122745038617210160071)
                    ·
                      rfl

theorem cell22_2956653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 4, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 4, 1, 3, 2, 3].length) (baseStart_2956653 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2956653 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2956653 prefixEnd_2956653 := by exact prefixLift 2956653
  have htrace : WordTrace (prefixWord ++ tailWord_2956653) baseStart_2956653 baseEnd_2956653 := by
    simpa [prefixWord, tailWord_2956653, baseEnd_2956653] using wordTrace_append hprefix tailTrace_2956653
  have hstable : (prefixWord ++ tailWord_2956653).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2956653).length < 2 ^ (prefixWord ++ tailWord_2956653).sum := by decide
  have hdescent : baseEnd_2956653 < baseStart_2956653 := by decide
  rcases family_descends (prefixWord ++ tailWord_2956653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2956670 : List Nat := [4, 2, 3, 2, 1, 1, 1, 2, 1, 5]
def baseStart_2956670 : Nat := 118140960795 + 2956670 * 2 ^ 59
def prefixEnd_2956670 : Nat := 4983230072969 + 3 ^ 40 * 2956670 * 2
def baseEnd_2956670 : Nat := 1012128564486034832485019

theorem tailTrace_2956670 : CollatzResearch.WordTrace tailWord_2956670 prefixEnd_2956670 1012128564486034832485019 := by
  unfold tailWord_2956670
  simp only [CollatzResearch.WordTrace]
  refine ⟨13479826774812127984908433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 71892409465664682586178309 13479826774812127984908433)
  ·
    refine ⟨10109870081109095988681325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13479826774812127984908433 10109870081109095988681325)
    ·
      refine ⟨3791201280415910995755497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10109870081109095988681325 3791201280415910995755497)
      ·
        refine ⟨2843400960311933246816623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3791201280415910995755497 2843400960311933246816623)
        ·
          refine ⟨4265101440467899870224935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2843400960311933246816623 4265101440467899870224935)
          ·
            refine ⟨6397652160701849805337403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4265101440467899870224935 6397652160701849805337403)
            ·
              refine ⟨9596478241052774708006105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6397652160701849805337403 9596478241052774708006105)
              ·
                refine ⟨7197358680789581031004579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9596478241052774708006105 7197358680789581031004579)
                ·
                  refine ⟨10796038021184371546506869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7197358680789581031004579 10796038021184371546506869)
                  ·
                    refine ⟨1012128564486034832485019, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10796038021184371546506869 1012128564486034832485019)
                    ·
                      rfl

theorem cell22_2956670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 1, 1, 2, 1, 5].length) (baseStart_2956670 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2956670 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2956670 prefixEnd_2956670 := by exact prefixLift 2956670
  have htrace : WordTrace (prefixWord ++ tailWord_2956670) baseStart_2956670 baseEnd_2956670 := by
    simpa [prefixWord, tailWord_2956670, baseEnd_2956670] using wordTrace_append hprefix tailTrace_2956670
  have hstable : (prefixWord ++ tailWord_2956670).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2956670).length < 2 ^ (prefixWord ++ tailWord_2956670).sum := by decide
  have hdescent : baseEnd_2956670 < baseStart_2956670 := by decide
  rcases family_descends (prefixWord ++ tailWord_2956670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2956700 : List Nat := [2, 2, 3, 4, 2, 1, 1, 7]
def baseStart_2956700 : Nat := 118140960795 + 2956700 * 2 ^ 59
def prefixEnd_2956700 : Nat := 4983230072969 + 3 ^ 40 * 2956700 * 2
def baseEnd_2956700 : Nat := 112459870455458306026103

theorem tailTrace_2956700 : CollatzResearch.WordTrace tailWord_2956700 prefixEnd_2956700 112459870455458306026103 := by
  unfold tailWord_2956700
  simp only [CollatzResearch.WordTrace]
  refine ⟨53919854194194169501429777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71893138925592226001906369 53919854194194169501429777)
  ·
    refine ⟨40439890645645627126072333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53919854194194169501429777 40439890645645627126072333)
    ·
      refine ⟨15164958992117110172277125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40439890645645627126072333 15164958992117110172277125)
      ·
        refine ⟨2843429811021958157301961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15164958992117110172277125 2843429811021958157301961)
        ·
          refine ⟨2132572358266468617976471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2843429811021958157301961 2132572358266468617976471)
          ·
            refine ⟨3198858537399702926964707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2132572358266468617976471 3198858537399702926964707)
            ·
              refine ⟨4798287806099554390447061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3198858537399702926964707 4798287806099554390447061)
              ·
                refine ⟨112459870455458306026103, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4798287806099554390447061 112459870455458306026103)
                ·
                  rfl

theorem cell22_2956700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 2, 1, 1, 7].length) (baseStart_2956700 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2956700 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2956700 prefixEnd_2956700 := by exact prefixLift 2956700
  have htrace : WordTrace (prefixWord ++ tailWord_2956700) baseStart_2956700 baseEnd_2956700 := by
    simpa [prefixWord, tailWord_2956700, baseEnd_2956700] using wordTrace_append hprefix tailTrace_2956700
  have hstable : (prefixWord ++ tailWord_2956700).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2956700).length < 2 ^ (prefixWord ++ tailWord_2956700).sum := by decide
  have hdescent : baseEnd_2956700 < baseStart_2956700 := by decide
  rcases family_descends (prefixWord ++ tailWord_2956700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2956711 : List Nat := [1, 1, 6, 1, 1, 1, 1, 5, 5]
def baseStart_2956711 : Nat := 118140960795 + 2956711 * 2 ^ 59
def prefixEnd_2956711 : Nat := 4983230072969 + 3 ^ 40 * 2956711 * 2
def baseEnd_2956711 : Nat := 337380866541308130736631

theorem tailTrace_2956711 : CollatzResearch.WordTrace tailWord_2956711 prefixEnd_2956711 337380866541308130736631 := by
  unfold tailWord_2956711
  simp only [CollatzResearch.WordTrace]
  refine ⟨107840109591348487881509987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71893406394232325254339991 107840109591348487881509987)
  ·
    refine ⟨161760164387022731822264981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107840109591348487881509987 161760164387022731822264981)
    ·
      refine ⟨7582507705641690554168671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 161760164387022731822264981 7582507705641690554168671)
      ·
        refine ⟨11373761558462535831253007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7582507705641690554168671 11373761558462535831253007)
        ·
          refine ⟨17060642337693803746879511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11373761558462535831253007 17060642337693803746879511)
          ·
            refine ⟨25590963506540705620319267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17060642337693803746879511 25590963506540705620319267)
            ·
              refine ⟨38386445259811058430478901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25590963506540705620319267 38386445259811058430478901)
              ·
                refine ⟨3598729243107286727857397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 38386445259811058430478901 3598729243107286727857397)
                ·
                  refine ⟨337380866541308130736631, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3598729243107286727857397 337380866541308130736631)
                  ·
                    rfl

theorem cell22_2956711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 1, 5, 5].length) (baseStart_2956711 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2956711 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2956711 prefixEnd_2956711 := by exact prefixLift 2956711
  have htrace : WordTrace (prefixWord ++ tailWord_2956711) baseStart_2956711 baseEnd_2956711 := by
    simpa [prefixWord, tailWord_2956711, baseEnd_2956711] using wordTrace_append hprefix tailTrace_2956711
  have hstable : (prefixWord ++ tailWord_2956711).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2956711).length < 2 ^ (prefixWord ++ tailWord_2956711).sum := by decide
  have hdescent : baseEnd_2956711 < baseStart_2956711 := by decide
  rcases family_descends (prefixWord ++ tailWord_2956711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2956732 : List Nat := [2, 2, 2, 4, 2, 1, 2, 3, 1, 3]
def baseStart_2956732 : Nat := 118140960795 + 2956732 * 2 ^ 59
def prefixEnd_2956732 : Nat := 4983230072969 + 3 ^ 40 * 2956732 * 2
def baseEnd_2956732 : Nat := 1012149788353087337434829

theorem tailTrace_2956732 : CollatzResearch.WordTrace tailWord_2956732 prefixEnd_2956732 1012149788353087337434829 := by
  unfold tailWord_2956732
  simp only [CollatzResearch.WordTrace]
  refine ⟨53920437762136204234012225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71893917016181605645349633 53920437762136204234012225)
  ·
    refine ⟨40440328321602153175509169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53920437762136204234012225 40440328321602153175509169)
    ·
      refine ⟨30330246241201614881631877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40440328321602153175509169 30330246241201614881631877)
      ·
        refine ⟨5686921170225302790305977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 30330246241201614881631877 5686921170225302790305977)
        ·
          refine ⟨4265190877668977092729483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5686921170225302790305977 4265190877668977092729483)
          ·
            refine ⟨6397786316503465639094225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4265190877668977092729483 6397786316503465639094225)
            ·
              refine ⟨4798339737377599229320669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6397786316503465639094225 4798339737377599229320669)
              ·
                refine ⟨1799377401516599710995251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4798339737377599229320669 1799377401516599710995251)
                ·
                  refine ⟨2699066102274899566492877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1799377401516599710995251 2699066102274899566492877)
                  ·
                    refine ⟨1012149788353087337434829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2699066102274899566492877 1012149788353087337434829)
                    ·
                      rfl

theorem cell22_2956732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 1, 2, 3, 1, 3].length) (baseStart_2956732 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2956732 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2956732 prefixEnd_2956732 := by exact prefixLift 2956732
  have htrace : WordTrace (prefixWord ++ tailWord_2956732) baseStart_2956732 baseEnd_2956732 := by
    simpa [prefixWord, tailWord_2956732, baseEnd_2956732] using wordTrace_append hprefix tailTrace_2956732
  have hstable : (prefixWord ++ tailWord_2956732).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2956732).length < 2 ^ (prefixWord ++ tailWord_2956732).sum := by decide
  have hdescent : baseEnd_2956732 < baseStart_2956732 := by decide
  rcases family_descends (prefixWord ++ tailWord_2956732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2956738 : List Nat := [3, 5, 2, 1, 2, 1, 1, 2, 2, 3]
def baseStart_2956738 : Nat := 118140960795 + 2956738 * 2 ^ 59
def prefixEnd_2956738 : Nat := 4983230072969 + 3 ^ 40 * 2956738 * 2
def baseEnd_2956738 : Nat := 1012151842275705321784811

theorem tailTrace_2956738 : CollatzResearch.WordTrace tailWord_2956738 prefixEnd_2956738 1012151842275705321784811 := by
  unfold tailWord_2956738
  simp only [CollatzResearch.WordTrace]
  refine ⟨26960273590562667873185717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71894062908167114328495245 26960273590562667873185717)
  ·
    refine ⟨2527525649115250113111161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 26960273590562667873185717 2527525649115250113111161)
    ·
      refine ⟨1895644236836437584833371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2527525649115250113111161 1895644236836437584833371)
      ·
        refine ⟨2843466355254656377250057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1895644236836437584833371 2843466355254656377250057)
        ·
          refine ⟨2132599766440992282937543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2843466355254656377250057 2132599766440992282937543)
          ·
            refine ⟨3198899649661488424406315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2132599766440992282937543 3198899649661488424406315)
            ·
              refine ⟨4798349474492232636609473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3198899649661488424406315 4798349474492232636609473)
              ·
                refine ⟨3598762105869174477457105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4798349474492232636609473 3598762105869174477457105)
                ·
                  refine ⟨2699071579401880858092829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3598762105869174477457105 2699071579401880858092829)
                  ·
                    refine ⟨1012151842275705321784811, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2699071579401880858092829 1012151842275705321784811)
                    ·
                      rfl

theorem cell22_2956738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 2, 1, 1, 2, 2, 3].length) (baseStart_2956738 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2956738 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2956738 prefixEnd_2956738 := by exact prefixLift 2956738
  have htrace : WordTrace (prefixWord ++ tailWord_2956738) baseStart_2956738 baseEnd_2956738 := by
    simpa [prefixWord, tailWord_2956738, baseEnd_2956738] using wordTrace_append hprefix tailTrace_2956738
  have hstable : (prefixWord ++ tailWord_2956738).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2956738).length < 2 ^ (prefixWord ++ tailWord_2956738).sum := by decide
  have hdescent : baseEnd_2956738 < baseStart_2956738 := by decide
  rcases family_descends (prefixWord ++ tailWord_2956738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2956790 : List Nat := [5, 1, 1, 1, 2, 2, 3, 3, 4]
def baseStart_2956790 : Nat := 118140960795 + 2956790 * 2 ^ 59
def prefixEnd_2956790 : Nat := 4983230072969 + 3 ^ 40 * 2956790 * 2
def baseEnd_2956790 : Nat := 337389880979464839828217

theorem tailTrace_2956790 : CollatzResearch.WordTrace tailWord_2956790 prefixEnd_2956790 337389880979464839828217 := by
  unfold tailWord_2956790
  simp only [CollatzResearch.WordTrace]
  refine ⟨6740186934878892773352239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 71895327305374856249090549 6740186934878892773352239)
  ·
    refine ⟨10110280402318339160028359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6740186934878892773352239 10110280402318339160028359)
    ·
      refine ⟨15165420603477508740042539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10110280402318339160028359 15165420603477508740042539)
      ·
        refine ⟨22748130905216263110063809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15165420603477508740042539 22748130905216263110063809)
        ·
          refine ⟨17061098178912197332547857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22748130905216263110063809 17061098178912197332547857)
          ·
            refine ⟨12795823634184147999410893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17061098178912197332547857 12795823634184147999410893)
            ·
              refine ⟨4798433862819055499779085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12795823634184147999410893 4798433862819055499779085)
              ·
                refine ⟨1799412698557145812417157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4798433862819055499779085 1799412698557145812417157)
                ·
                  refine ⟨337389880979464839828217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1799412698557145812417157 337389880979464839828217)
                  ·
                    rfl

theorem cell22_2956790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 3, 3, 4].length) (baseStart_2956790 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2956790 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2956790 prefixEnd_2956790 := by exact prefixLift 2956790
  have htrace : WordTrace (prefixWord ++ tailWord_2956790) baseStart_2956790 baseEnd_2956790 := by
    simpa [prefixWord, tailWord_2956790, baseEnd_2956790] using wordTrace_append hprefix tailTrace_2956790
  have hstable : (prefixWord ++ tailWord_2956790).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2956790).length < 2 ^ (prefixWord ++ tailWord_2956790).sum := by decide
  have hdescent : baseEnd_2956790 < baseStart_2956790 := by decide
  rcases family_descends (prefixWord ++ tailWord_2956790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2956850 : List Nat := [3, 2, 1, 1, 2, 1, 1, 7, 1, 3]
def baseStart_2956850 : Nat := 118140960795 + 2956850 * 2 ^ 59
def prefixEnd_2956850 : Nat := 4983230072969 + 3 ^ 40 * 2956850 * 2
def baseEnd_2956850 : Nat := 1012190182164574362984467

theorem tailTrace_2956850 : CollatzResearch.WordTrace tailWord_2956850 prefixEnd_2956850 1012190182164574362984467 := by
  unfold tailWord_2956850
  simp only [CollatzResearch.WordTrace]
  refine ⟨26961294834461228655205001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71896786225229943080546669 26961294834461228655205001)
  ·
    refine ⟨20220971125845921491403751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26961294834461228655205001 20220971125845921491403751)
    ·
      refine ⟨30331456688768882237105627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20220971125845921491403751 30331456688768882237105627)
      ·
        refine ⟨45497185033153323355658441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30331456688768882237105627 45497185033153323355658441)
        ·
          refine ⟨34122888774864992516743831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45497185033153323355658441 34122888774864992516743831)
          ·
            refine ⟨51184333162297488775115747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34122888774864992516743831 51184333162297488775115747)
            ·
              refine ⟨76776499743446233162673621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51184333162297488775115747 76776499743446233162673621)
              ·
                refine ⟨1799449212737021089750163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 76776499743446233162673621 1799449212737021089750163)
                ·
                  refine ⟨2699173819105531634625245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1799449212737021089750163 2699173819105531634625245)
                  ·
                    refine ⟨1012190182164574362984467, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2699173819105531634625245 1012190182164574362984467)
                    ·
                      rfl

theorem cell22_2956850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 7, 1, 3].length) (baseStart_2956850 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2956850 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2956850 prefixEnd_2956850 := by exact prefixLift 2956850
  have htrace : WordTrace (prefixWord ++ tailWord_2956850) baseStart_2956850 baseEnd_2956850 := by
    simpa [prefixWord, tailWord_2956850, baseEnd_2956850] using wordTrace_append hprefix tailTrace_2956850
  have hstable : (prefixWord ++ tailWord_2956850).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2956850).length < 2 ^ (prefixWord ++ tailWord_2956850).sum := by decide
  have hdescent : baseEnd_2956850 < baseStart_2956850 := by decide
  rcases family_descends (prefixWord ++ tailWord_2956850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2956863 : List Nat := [1, 1, 2, 2, 3, 4, 2, 2, 5]
def baseStart_2956863 : Nat := 118140960795 + 2956863 * 2 ^ 59
def prefixEnd_2956863 : Nat := 4983230072969 + 3 ^ 40 * 2956863 * 2
def baseEnd_2956863 : Nat := 337398210776748887469809

theorem tailTrace_2956863 : CollatzResearch.WordTrace tailWord_2956863 prefixEnd_2956863 337398210776748887469809 := by
  unfold tailWord_2956863
  simp only [CollatzResearch.WordTrace]
  refine ⟨107845653486797817841043243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71897102324531878560695495 107845653486797817841043243)
  ·
    refine ⟨161768480230196726761564865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107845653486797817841043243 161768480230196726761564865)
    ·
      refine ⟨121326360172647545071173649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 161768480230196726761564865 121326360172647545071173649)
      ·
        refine ⟨90994770129485658803380237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 121326360172647545071173649 90994770129485658803380237)
        ·
          refine ⟨34123038798557122051267589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 90994770129485658803380237 34123038798557122051267589)
          ·
            refine ⟨6398069774729460384612673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 34123038798557122051267589 6398069774729460384612673)
            ·
              refine ⟨4798552331047095288459505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6398069774729460384612673 4798552331047095288459505)
              ·
                refine ⟨3598914248285321466344629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4798552331047095288459505 3598914248285321466344629)
                ·
                  refine ⟨337398210776748887469809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3598914248285321466344629 337398210776748887469809)
                  ·
                    rfl

theorem cell22_2956863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 4, 2, 2, 5].length) (baseStart_2956863 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2956863 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2956863 prefixEnd_2956863 := by exact prefixLift 2956863
  have htrace : WordTrace (prefixWord ++ tailWord_2956863) baseStart_2956863 baseEnd_2956863 := by
    simpa [prefixWord, tailWord_2956863, baseEnd_2956863] using wordTrace_append hprefix tailTrace_2956863
  have hstable : (prefixWord ++ tailWord_2956863).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2956863).length < 2 ^ (prefixWord ++ tailWord_2956863).sum := by decide
  have hdescent : baseEnd_2956863 < baseStart_2956863 := by decide
  rcases family_descends (prefixWord ++ tailWord_2956863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2956923 : List Nat := [1, 1, 1, 1, 1, 4, 5, 1, 4, 3]
def baseStart_2956923 : Nat := 118140960795 + 2956923 * 2 ^ 59
def prefixEnd_2956923 : Nat := 4983230072969 + 3 ^ 40 * 2956923 * 2
def baseEnd_2956923 : Nat := 1012215171556426505909243

theorem tailTrace_2956923 : CollatzResearch.WordTrace tailWord_2956923 prefixEnd_2956923 1012215171556426505909243 := by
  unfold tailWord_2956923
  simp only [CollatzResearch.WordTrace]
  refine ⟨107847841866580448088227423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71898561244386965392151615 107847841866580448088227423)
  ·
    refine ⟨161771762799870672132341135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107847841866580448088227423 161771762799870672132341135)
    ·
      refine ⟨242657644199806008198511703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 161771762799870672132341135 242657644199806008198511703)
      ·
        refine ⟨363986466299709012297767555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 242657644199806008198511703 363986466299709012297767555)
        ·
          refine ⟨545979699449563518446651333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 363986466299709012297767555 545979699449563518446651333)
          ·
            refine ⟨102371193646793159708747125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 545979699449563518446651333 102371193646793159708747125)
            ·
              refine ⟨9597299404386858722695043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 102371193646793159708747125 9597299404386858722695043)
              ·
                refine ⟨14395949106580288084042565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9597299404386858722695043 14395949106580288084042565)
                ·
                  refine ⟨2699240457483804015757981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14395949106580288084042565 2699240457483804015757981)
                  ·
                    refine ⟨1012215171556426505909243, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2699240457483804015757981 1012215171556426505909243)
                    ·
                      rfl

theorem cell22_2956923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 5, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 5, 1, 4, 3].length) (baseStart_2956923 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2956923 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2956923 prefixEnd_2956923 := by exact prefixLift 2956923
  have htrace : WordTrace (prefixWord ++ tailWord_2956923) baseStart_2956923 baseEnd_2956923 := by
    simpa [prefixWord, tailWord_2956923, baseEnd_2956923] using wordTrace_append hprefix tailTrace_2956923
  have hstable : (prefixWord ++ tailWord_2956923).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2956923).length < 2 ^ (prefixWord ++ tailWord_2956923).sum := by decide
  have hdescent : baseEnd_2956923 < baseStart_2956923 := by decide
  rcases family_descends (prefixWord ++ tailWord_2956923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2956925 : List Nat := [1, 4, 1, 1, 4, 1, 2, 4, 4]
def baseStart_2956925 : Nat := 118140960795 + 2956925 * 2 ^ 59
def prefixEnd_2956925 : Nat := 4983230072969 + 3 ^ 40 * 2956925 * 2
def baseEnd_2956925 : Nat := 337405285399099722453079

theorem tailTrace_2956925 : CollatzResearch.WordTrace tailWord_2956925 prefixEnd_2956925 337405285399099722453079 := by
  unfold tailWord_2956925
  simp only [CollatzResearch.WordTrace]
  refine ⟨107847914812573202429800229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71898609875048801619866819 107847914812573202429800229)
  ·
    refine ⟨20221484027357475455587543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 107847914812573202429800229 20221484027357475455587543)
    ·
      refine ⟨30332226041036213183381315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20221484027357475455587543 30332226041036213183381315)
      ·
        refine ⟨45498339061554319775071973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30332226041036213183381315 45498339061554319775071973)
        ·
          refine ⟨8530938574041434957825995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 45498339061554319775071973 8530938574041434957825995)
          ·
            refine ⟨12796407861062152436738993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8530938574041434957825995 12796407861062152436738993)
            ·
              refine ⟨9597305895796614327554245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12796407861062152436738993 9597305895796614327554245)
              ·
                refine ⟨1799494855461865186416421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9597305895796614327554245 1799494855461865186416421)
                ·
                  refine ⟨337405285399099722453079, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1799494855461865186416421 337405285399099722453079)
                  ·
                    rfl

theorem cell22_2956925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 2, 4, 4].length) (baseStart_2956925 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2956925 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2956925 prefixEnd_2956925 := by exact prefixLift 2956925
  have htrace : WordTrace (prefixWord ++ tailWord_2956925) baseStart_2956925 baseEnd_2956925 := by
    simpa [prefixWord, tailWord_2956925, baseEnd_2956925] using wordTrace_append hprefix tailTrace_2956925
  have hstable : (prefixWord ++ tailWord_2956925).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2956925).length < 2 ^ (prefixWord ++ tailWord_2956925).sum := by decide
  have hdescent : baseEnd_2956925 < baseStart_2956925 := by decide
  rcases family_descends (prefixWord ++ tailWord_2956925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2956938 : List Nat := [3, 1, 2, 3, 2, 1, 1, 2, 1, 6]
def baseStart_2956938 : Nat := 118140960795 + 2956938 * 2 ^ 59
def prefixEnd_2956938 : Nat := 4983230072969 + 3 ^ 40 * 2956938 * 2
def baseEnd_2956938 : Nat := 1012220306362971466784197

theorem tailTrace_2956938 : CollatzResearch.WordTrace tailWord_2956938 prefixEnd_2956938 1012220306362971466784197 := by
  unfold tailWord_2956938
  simp only [CollatzResearch.WordTrace]
  refine ⟨26962097240381526412505867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71898925974350737100015645 26962097240381526412505867)
  ·
    refine ⟨40443145860572289618758801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26962097240381526412505867 40443145860572289618758801)
    ·
      refine ⟨30332359395429217214069101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40443145860572289618758801 30332359395429217214069101)
      ·
        refine ⟨11374634773285956455275913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30332359395429217214069101 11374634773285956455275913)
        ·
          refine ⟨8530976079964467341456935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11374634773285956455275913 8530976079964467341456935)
          ·
            refine ⟨12796464119946701012185403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8530976079964467341456935 12796464119946701012185403)
            ·
              refine ⟨19194696179920051518278105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12796464119946701012185403 19194696179920051518278105)
              ·
                refine ⟨14396022134940038638708579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19194696179920051518278105 14396022134940038638708579)
                ·
                  refine ⟨21594033202410057958062869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14396022134940038638708579 21594033202410057958062869)
                  ·
                    refine ⟨1012220306362971466784197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21594033202410057958062869 1012220306362971466784197)
                    ·
                      rfl

theorem cell22_2956938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 1, 2, 1, 6].length) (baseStart_2956938 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2956938 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2956938 prefixEnd_2956938 := by exact prefixLift 2956938
  have htrace : WordTrace (prefixWord ++ tailWord_2956938) baseStart_2956938 baseEnd_2956938 := by
    simpa [prefixWord, tailWord_2956938, baseEnd_2956938] using wordTrace_append hprefix tailTrace_2956938
  have hstable : (prefixWord ++ tailWord_2956938).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2956938).length < 2 ^ (prefixWord ++ tailWord_2956938).sum := by decide
  have hdescent : baseEnd_2956938 < baseStart_2956938 := by decide
  rcases family_descends (prefixWord ++ tailWord_2956938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2956959 : List Nat := [1, 1, 2, 7, 1, 2, 1, 3, 4]
def baseStart_2956959 : Nat := 118140960795 + 2956959 * 2 ^ 59
def prefixEnd_2956959 : Nat := 4983230072969 + 3 ^ 40 * 2956959 * 2
def baseEnd_2956959 : Nat := 337409165030711470669711

theorem tailTrace_2956959 : CollatzResearch.WordTrace tailWord_2956959 prefixEnd_2956959 337409165030711470669711 := by
  unfold tailWord_2956959
  simp only [CollatzResearch.WordTrace]
  refine ⟨107849154894450026236537931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71899436596300017491025287 107849154894450026236537931)
  ·
    refine ⟨161773732341675039354806897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107849154894450026236537931 161773732341675039354806897)
    ·
      refine ⟨121330299256256279516105173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 161773732341675039354806897 121330299256256279516105173)
      ·
        refine ⟨2843678888818506551158715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 121330299256256279516105173 2843678888818506551158715)
        ·
          refine ⟨4265518333227759826738073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2843678888818506551158715 4265518333227759826738073)
          ·
            refine ⟨3199138749920819870053555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4265518333227759826738073 3199138749920819870053555)
            ·
              refine ⟨4798708124881229805080333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3199138749920819870053555 4798708124881229805080333)
              ·
                refine ⟨1799515546830461176905125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4798708124881229805080333 1799515546830461176905125)
                ·
                  refine ⟨337409165030711470669711, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1799515546830461176905125 337409165030711470669711)
                  ·
                    rfl

theorem cell22_2956959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 2, 1, 3, 4].length) (baseStart_2956959 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2956959 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2956959 prefixEnd_2956959 := by exact prefixLift 2956959
  have htrace : WordTrace (prefixWord ++ tailWord_2956959) baseStart_2956959 baseEnd_2956959 := by
    simpa [prefixWord, tailWord_2956959, baseEnd_2956959] using wordTrace_append hprefix tailTrace_2956959
  have hstable : (prefixWord ++ tailWord_2956959).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2956959).length < 2 ^ (prefixWord ++ tailWord_2956959).sum := by decide
  have hdescent : baseEnd_2956959 < baseStart_2956959 := by decide
  rcases family_descends (prefixWord ++ tailWord_2956959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2956985 : List Nat := [1, 2, 1, 4, 1, 1, 5, 1, 3, 3]
def baseStart_2956985 : Nat := 118140960795 + 2956985 * 2 ^ 59
def prefixEnd_2956985 : Nat := 4983230072969 + 3 ^ 40 * 2956985 * 2
def baseEnd_2956985 : Nat := 1012236395423479010859053

theorem tailTrace_2956985 : CollatzResearch.WordTrace tailWord_2956985 prefixEnd_2956985 1012236395423479010859053 := by
  unfold tailWord_2956985
  simp only [CollatzResearch.WordTrace]
  refine ⟨107850103192355832676984409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71900068794903888451322939 107850103192355832676984409)
  ·
    refine ⟨80887577394266874507738307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107850103192355832676984409 80887577394266874507738307)
    ·
      refine ⟨121331366091400311761607461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80887577394266874507738307 121331366091400311761607461)
      ·
        refine ⟨22749631142137558455301399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 121331366091400311761607461 22749631142137558455301399)
        ·
          refine ⟨34124446713206337682952099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22749631142137558455301399 34124446713206337682952099)
          ·
            refine ⟨51186670069809506524428149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34124446713206337682952099 51186670069809506524428149)
            ·
              refine ⟨4798750319044641236665139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 51186670069809506524428149 4798750319044641236665139)
              ·
                refine ⟨7198125478566961854997709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4798750319044641236665139 7198125478566961854997709)
                ·
                  refine ⟨2699297054462610695624141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7198125478566961854997709 2699297054462610695624141)
                  ·
                    refine ⟨1012236395423479010859053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2699297054462610695624141 1012236395423479010859053)
                    ·
                      rfl

theorem cell22_2956985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 5, 1, 3, 3].length) (baseStart_2956985 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2956985 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2956985 prefixEnd_2956985 := by exact prefixLift 2956985
  have htrace : WordTrace (prefixWord ++ tailWord_2956985) baseStart_2956985 baseEnd_2956985 := by
    simpa [prefixWord, tailWord_2956985, baseEnd_2956985] using wordTrace_append hprefix tailTrace_2956985
  have hstable : (prefixWord ++ tailWord_2956985).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2956985).length < 2 ^ (prefixWord ++ tailWord_2956985).sum := by decide
  have hdescent : baseEnd_2956985 < baseStart_2956985 := by decide
  rcases family_descends (prefixWord ++ tailWord_2956985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2957060 : List Nat := [2, 3, 2, 2, 1, 3, 1, 2, 6]
def baseStart_2957060 : Nat := 118140960795 + 2957060 * 2 ^ 59
def prefixEnd_2957060 : Nat := 4983230072969 + 3 ^ 40 * 2957060 * 2
def baseEnd_2957060 : Nat := 337420689818734605077941

theorem tailTrace_2957060 : CollatzResearch.WordTrace tailWord_2957060 prefixEnd_2957060 337420689818734605077941 := by
  unfold tailWord_2957060
  simp only [CollatzResearch.WordTrace]
  refine ⟨53926419333542060242982317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71901892444722746990643089 53926419333542060242982317)
  ·
    refine ⟨20222407250078272591118369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53926419333542060242982317 20222407250078272591118369)
    ·
      refine ⟨15166805437558704443338777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20222407250078272591118369 15166805437558704443338777)
      ·
        refine ⟨11375104078169028332504083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15166805437558704443338777 11375104078169028332504083)
        ·
          refine ⟨17062656117253542498756125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11375104078169028332504083 17062656117253542498756125)
          ·
            refine ⟨6398496043970078437033547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17062656117253542498756125 6398496043970078437033547)
            ·
              refine ⟨9597744065955117655550321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6398496043970078437033547 9597744065955117655550321)
              ·
                refine ⟨7198308049466338241662741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9597744065955117655550321 7198308049466338241662741)
                ·
                  refine ⟨337420689818734605077941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7198308049466338241662741 337420689818734605077941)
                  ·
                    rfl

theorem cell22_2957060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 3, 1, 2, 6].length) (baseStart_2957060 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2957060 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2957060 prefixEnd_2957060 := by exact prefixLift 2957060
  have htrace : WordTrace (prefixWord ++ tailWord_2957060) baseStart_2957060 baseEnd_2957060 := by
    simpa [prefixWord, tailWord_2957060, baseEnd_2957060] using wordTrace_append hprefix tailTrace_2957060
  have hstable : (prefixWord ++ tailWord_2957060).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2957060).length < 2 ^ (prefixWord ++ tailWord_2957060).sum := by decide
  have hdescent : baseEnd_2957060 < baseStart_2957060 := by decide
  rcases family_descends (prefixWord ++ tailWord_2957060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2957077 : List Nat := [1, 3, 2, 1, 2, 4, 2, 3, 4]
def baseStart_2957077 : Nat := 118140960795 + 2957077 * 2 ^ 59
def prefixEnd_2957077 : Nat := 4983230072969 + 3 ^ 40 * 2957077 * 2
def baseEnd_2957077 : Nat := 337422629634540479186257

theorem tailTrace_2957077 : CollatzResearch.WordTrace tailWord_2957077 prefixEnd_2957077 337422629634540479186257 := by
  unfold tailWord_2957077
  simp only [CollatzResearch.WordTrace]
  refine ⟨107853458708022532389333485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71902305805348354926222323 107853458708022532389333485)
  ·
    refine ⟨40445047015508449646000057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 107853458708022532389333485 40445047015508449646000057)
    ·
      refine ⟨30333785261631337234500043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40445047015508449646000057 30333785261631337234500043)
      ·
        refine ⟨45500677892447005851750065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30333785261631337234500043 45500677892447005851750065)
        ·
          refine ⟨34125508419335254388812549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45500677892447005851750065 34125508419335254388812549)
          ·
            refine ⟨6398532828625360197902353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 34125508419335254388812549 6398532828625360197902353)
            ·
              refine ⟨4798899621469020148426765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6398532828625360197902353 4798899621469020148426765)
              ·
                refine ⟨1799587358050882555660037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4798899621469020148426765 1799587358050882555660037)
                ·
                  refine ⟨337422629634540479186257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1799587358050882555660037 337422629634540479186257)
                  ·
                    rfl

theorem cell22_2957077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 4, 2, 3, 4].length) (baseStart_2957077 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2957077 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2957077 prefixEnd_2957077 := by exact prefixLift 2957077
  have htrace : WordTrace (prefixWord ++ tailWord_2957077) baseStart_2957077 baseEnd_2957077 := by
    simpa [prefixWord, tailWord_2957077, baseEnd_2957077] using wordTrace_append hprefix tailTrace_2957077
  have hstable : (prefixWord ++ tailWord_2957077).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2957077).length < 2 ^ (prefixWord ++ tailWord_2957077).sum := by decide
  have hdescent : baseEnd_2957077 < baseStart_2957077 := by decide
  rcases family_descends (prefixWord ++ tailWord_2957077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2957079 : List Nat := [1, 1, 3, 4, 2, 3, 2, 1, 1, 4]
def baseStart_2957079 : Nat := 118140960795 + 2957079 * 2 ^ 59
def prefixEnd_2957079 : Nat := 4983230072969 + 3 ^ 40 * 2957079 * 2
def baseEnd_2957079 : Nat := 1012268573544494099008765

theorem tailTrace_2957079 : CollatzResearch.WordTrace tailWord_2957079 prefixEnd_2957079 1012268573544494099008765 := by
  unfold tailWord_2957079
  simp only [CollatzResearch.WordTrace]
  refine ⟨107853531654015286730906291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71902354436010191153937527 107853531654015286730906291)
  ·
    refine ⟨161780297481022930096359437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107853531654015286730906291 161780297481022930096359437)
    ·
      refine ⟨60667611555383598786134789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 161780297481022930096359437 60667611555383598786134789)
      ·
        refine ⟨11375177166634424772400273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 60667611555383598786134789 11375177166634424772400273)
        ·
          refine ⟨8531382874975818579300205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11375177166634424772400273 8531382874975818579300205)
          ·
            refine ⟨3199268578115931967237577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8531382874975818579300205 3199268578115931967237577)
            ·
              refine ⟨2399451433586948975428183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3199268578115931967237577 2399451433586948975428183)
              ·
                refine ⟨3599177150380423463142275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2399451433586948975428183 3599177150380423463142275)
                ·
                  refine ⟨5398765725570635194713413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3599177150380423463142275 5398765725570635194713413)
                  ·
                    refine ⟨1012268573544494099008765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5398765725570635194713413 1012268573544494099008765)
                    ·
                      rfl

theorem cell22_2957079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 3, 2, 1, 1, 4].length) (baseStart_2957079 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2957079 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2957079 prefixEnd_2957079 := by exact prefixLift 2957079
  have htrace : WordTrace (prefixWord ++ tailWord_2957079) baseStart_2957079 baseEnd_2957079 := by
    simpa [prefixWord, tailWord_2957079, baseEnd_2957079] using wordTrace_append hprefix tailTrace_2957079
  have hstable : (prefixWord ++ tailWord_2957079).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2957079).length < 2 ^ (prefixWord ++ tailWord_2957079).sum := by decide
  have hdescent : baseEnd_2957079 < baseStart_2957079 := by decide
  rcases family_descends (prefixWord ++ tailWord_2957079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2957088 : List Nat := [2, 1, 1, 5, 1, 1, 11]
def baseStart_2957088 : Nat := 118140960795 + 2957088 * 2 ^ 59
def prefixEnd_2957088 : Nat := 4983230072969 + 3 ^ 40 * 2957088 * 2
def baseEnd_2957088 : Nat := 37491542756608187982731

theorem tailTrace_2957088 : CollatzResearch.WordTrace tailWord_2957088 prefixEnd_2957088 37491542756608187982731 := by
  unfold tailWord_2957088
  simp only [CollatzResearch.WordTrace]
  refine ⟨53926929955491340633991959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71902573273988454178655945 53926929955491340633991959)
  ·
    refine ⟨80890394933237010950987939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53926929955491340633991959 80890394933237010950987939)
    ·
      refine ⟨121335592399855516426481909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80890394933237010950987939 121335592399855516426481909)
      ·
        refine ⟨11375211787486454664982679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 121335592399855516426481909 11375211787486454664982679)
        ·
          refine ⟨17062817681229681997474019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11375211787486454664982679 17062817681229681997474019)
          ·
            refine ⟨25594226521844522996211029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17062817681229681997474019 25594226521844522996211029)
            ·
              refine ⟨37491542756608187982731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 25594226521844522996211029 37491542756608187982731)
              ·
                rfl

theorem cell22_2957088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 11].length) (baseStart_2957088 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2957088 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2957088 prefixEnd_2957088 := by exact prefixLift 2957088
  have htrace : WordTrace (prefixWord ++ tailWord_2957088) baseStart_2957088 baseEnd_2957088 := by
    simpa [prefixWord, tailWord_2957088, baseEnd_2957088] using wordTrace_append hprefix tailTrace_2957088
  have hstable : (prefixWord ++ tailWord_2957088).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2957088).length < 2 ^ (prefixWord ++ tailWord_2957088).sum := by decide
  have hdescent : baseEnd_2957088 < baseStart_2957088 := by decide
  rcases family_descends (prefixWord ++ tailWord_2957088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2957090 : List Nat := [3, 3, 1, 1, 2, 1, 2, 1, 4, 4]
def baseStart_2957090 : Nat := 118140960795 + 2957090 * 2 ^ 59
def prefixEnd_2957090 : Nat := 4983230072969 + 3 ^ 40 * 2957090 * 2
def baseEnd_2957090 : Nat := 1012272339069293736983731

theorem tailTrace_2957090 : CollatzResearch.WordTrace tailWord_2957090 prefixEnd_2957090 1012272339069293736983731 := by
  unfold tailWord_2957090
  simp only [CollatzResearch.WordTrace]
  refine ⟨26963483214243858902389181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71902621904650290406371149 26963483214243858902389181)
  ·
    refine ⟨10111306205341447088395943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26963483214243858902389181 10111306205341447088395943)
    ·
      refine ⟨15166959308012170632593915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10111306205341447088395943 15166959308012170632593915)
      ·
        refine ⟨22750438962018255948890873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15166959308012170632593915 22750438962018255948890873)
        ·
          refine ⟨17062829221513691961668155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22750438962018255948890873 17062829221513691961668155)
          ·
            refine ⟨25594243832270537942502233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17062829221513691961668155 25594243832270537942502233)
            ·
              refine ⟨19195682874202903456876675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25594243832270537942502233 19195682874202903456876675)
              ·
                refine ⟨28793524311304355185315013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19195682874202903456876675 28793524311304355185315013)
                ·
                  refine ⟨5398785808369566597246565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28793524311304355185315013 5398785808369566597246565)
                  ·
                    refine ⟨1012272339069293736983731, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5398785808369566597246565 1012272339069293736983731)
                    ·
                      rfl

theorem cell22_2957090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 2, 1, 4, 4].length) (baseStart_2957090 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2957090 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2957090 prefixEnd_2957090 := by exact prefixLift 2957090
  have htrace : WordTrace (prefixWord ++ tailWord_2957090) baseStart_2957090 baseEnd_2957090 := by
    simpa [prefixWord, tailWord_2957090, baseEnd_2957090] using wordTrace_append hprefix tailTrace_2957090
  have hstable : (prefixWord ++ tailWord_2957090).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2957090).length < 2 ^ (prefixWord ++ tailWord_2957090).sum := by decide
  have hdescent : baseEnd_2957090 < baseStart_2957090 := by decide
  rcases family_descends (prefixWord ++ tailWord_2957090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2957092 : List Nat := [2, 3, 1, 3, 2, 2, 1, 1, 4, 3]
def baseStart_2957092 : Nat := 118140960795 + 2957092 * 2 ^ 59
def prefixEnd_2957092 : Nat := 4983230072969 + 3 ^ 40 * 2957092 * 2
def baseEnd_2957092 : Nat := 1012273023710166398433725

theorem tailTrace_2957092 : CollatzResearch.WordTrace tailWord_2957092 prefixEnd_2957092 1012273023710166398433725 := by
  unfold tailWord_2957092
  simp only [CollatzResearch.WordTrace]
  refine ⟨53927002901484094975564765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71902670535312126634086353 53927002901484094975564765)
  ·
    refine ⟨20222626088056535615836787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53927002901484094975564765 20222626088056535615836787)
    ·
      refine ⟨30333939132084803423755181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20222626088056535615836787 30333939132084803423755181)
      ·
        refine ⟨11375227174531801283908193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30333939132084803423755181 11375227174531801283908193)
        ·
          refine ⟨8531420380898850962931145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11375227174531801283908193 8531420380898850962931145)
          ·
            refine ⟨6398565285674138222198359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8531420380898850962931145 6398565285674138222198359)
            ·
              refine ⟨9597847928511207333297539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6398565285674138222198359 9597847928511207333297539)
              ·
                refine ⟨14396771892766810999946309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9597847928511207333297539 14396771892766810999946309)
                ·
                  refine ⟨2699394729893777062489933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14396771892766810999946309 2699394729893777062489933)
                  ·
                    refine ⟨1012273023710166398433725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2699394729893777062489933 1012273023710166398433725)
                    ·
                      rfl

theorem cell22_2957092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 2, 1, 1, 4, 3].length) (baseStart_2957092 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2957092 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2957092 prefixEnd_2957092 := by exact prefixLift 2957092
  have htrace : WordTrace (prefixWord ++ tailWord_2957092) baseStart_2957092 baseEnd_2957092 := by
    simpa [prefixWord, tailWord_2957092, baseEnd_2957092] using wordTrace_append hprefix tailTrace_2957092
  have hstable : (prefixWord ++ tailWord_2957092).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2957092).length < 2 ^ (prefixWord ++ tailWord_2957092).sum := by decide
  have hdescent : baseEnd_2957092 < baseStart_2957092 := by decide
  rcases family_descends (prefixWord ++ tailWord_2957092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2957109 : List Nat := [1, 3, 3, 1, 5, 1, 1, 1, 1, 5]
def baseStart_2957109 : Nat := 118140960795 + 2957109 * 2 ^ 59
def prefixEnd_2957109 : Nat := 4983230072969 + 3 ^ 40 * 2957109 * 2
def baseEnd_2957109 : Nat := 1012278843157584020758673

theorem tailTrace_2957109 : CollatzResearch.WordTrace tailWord_2957109 prefixEnd_2957109 1012278843157584020758673 := by
  unfold tailWord_2957109
  simp only [CollatzResearch.WordTrace]
  refine ⟨107854625843906601854498381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71903083895937734569665587 107854625843906601854498381)
  ·
    refine ⟨40445484691464975695436893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 107854625843906601854498381 40445484691464975695436893)
    ·
      refine ⟨15167056759299365885788835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40445484691464975695436893 15167056759299365885788835)
      ·
        refine ⟨22750585138949048828683253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15167056759299365885788835 22750585138949048828683253)
        ·
          refine ⟨2132867356776473327689055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 22750585138949048828683253 2132867356776473327689055)
          ·
            refine ⟨3199301035164709991533583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2132867356776473327689055 3199301035164709991533583)
            ·
              refine ⟨4798951552747064987300375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3199301035164709991533583 4798951552747064987300375)
              ·
                refine ⟨7198427329120597480950563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4798951552747064987300375 7198427329120597480950563)
                ·
                  refine ⟨10797640993680896221425845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7198427329120597480950563 10797640993680896221425845)
                  ·
                    refine ⟨1012278843157584020758673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10797640993680896221425845 1012278843157584020758673)
                    ·
                      rfl

theorem cell22_2957109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 5, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 5, 1, 1, 1, 1, 5].length) (baseStart_2957109 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2957109 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2957109 prefixEnd_2957109 := by exact prefixLift 2957109
  have htrace : WordTrace (prefixWord ++ tailWord_2957109) baseStart_2957109 baseEnd_2957109 := by
    simpa [prefixWord, tailWord_2957109, baseEnd_2957109] using wordTrace_append hprefix tailTrace_2957109
  have hstable : (prefixWord ++ tailWord_2957109).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2957109).length < 2 ^ (prefixWord ++ tailWord_2957109).sum := by decide
  have hdescent : baseEnd_2957109 < baseStart_2957109 := by decide
  rcases family_descends (prefixWord ++ tailWord_2957109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2957154 : List Nat := [3, 3, 2, 1, 2, 1, 3, 1, 3, 3]
def baseStart_2957154 : Nat := 118140960795 + 2957154 * 2 ^ 59
def prefixEnd_2957154 : Nat := 4983230072969 + 3 ^ 40 * 2957154 * 2
def baseEnd_2957154 : Nat := 1012294247577218903383535

theorem tailTrace_2957154 : CollatzResearch.WordTrace tailWord_2957154 prefixEnd_2957154 1012294247577218903383535 := by
  unfold tailWord_2957154
  simp only [CollatzResearch.WordTrace]
  refine ⟨26964066782185893634971629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71904178085829049693257677 26964066782185893634971629)
  ·
    refine ⟨10111525043319710113114361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26964066782185893634971629 10111525043319710113114361)
    ·
      refine ⟨7583643782489782584835771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10111525043319710113114361 7583643782489782584835771)
      ·
        refine ⟨11375465673734673877253657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7583643782489782584835771 11375465673734673877253657)
        ·
          refine ⟨8531599255301005407940243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11375465673734673877253657 8531599255301005407940243)
          ·
            refine ⟨12797398882951508111910365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8531599255301005407940243 12797398882951508111910365)
            ·
              refine ⟨4799024581106815541966387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12797398882951508111910365 4799024581106815541966387)
              ·
                refine ⟨7198536871660223312949581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4799024581106815541966387 7198536871660223312949581)
                ·
                  refine ⟨2699451326872583742356093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7198536871660223312949581 2699451326872583742356093)
                  ·
                    refine ⟨1012294247577218903383535, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2699451326872583742356093 1012294247577218903383535)
                    ·
                      rfl

theorem cell22_2957154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 3, 1, 3, 3].length) (baseStart_2957154 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2957154 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2957154 prefixEnd_2957154 := by exact prefixLift 2957154
  have htrace : WordTrace (prefixWord ++ tailWord_2957154) baseStart_2957154 baseEnd_2957154 := by
    simpa [prefixWord, tailWord_2957154, baseEnd_2957154] using wordTrace_append hprefix tailTrace_2957154
  have hstable : (prefixWord ++ tailWord_2957154).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2957154).length < 2 ^ (prefixWord ++ tailWord_2957154).sum := by decide
  have hdescent : baseEnd_2957154 < baseStart_2957154 := by decide
  rcases family_descends (prefixWord ++ tailWord_2957154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2957163 : List Nat := [1, 1, 1, 1, 2, 2, 3, 1, 2, 8]
def baseStart_2957163 : Nat := 118140960795 + 2957163 * 2 ^ 59
def prefixEnd_2957163 : Nat := 4983230072969 + 3 ^ 40 * 2957163 * 2
def baseEnd_2957163 : Nat := 1012297328461145879908507

theorem tailTrace_2957163 : CollatzResearch.WordTrace tailWord_2957163 prefixEnd_2957163 1012297328461145879908507 := by
  unfold tailWord_2957163
  simp only [CollatzResearch.WordTrace]
  refine ⟨107856595385710969076964143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71904396923807312717976095 107856595385710969076964143)
  ·
    refine ⟨161784893078566453615446215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107856595385710969076964143 161784893078566453615446215)
    ·
      refine ⟨242677339617849680423169323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 161784893078566453615446215 242677339617849680423169323)
      ·
        refine ⟨364016009426774520634753985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 242677339617849680423169323 364016009426774520634753985)
        ·
          refine ⟨273012007070080890476065489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 364016009426774520634753985 273012007070080890476065489)
          ·
            refine ⟨204759005302560667857049117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 273012007070080890476065489 204759005302560667857049117)
            ·
              refine ⟨76784626988460250446393419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 204759005302560667857049117 76784626988460250446393419)
              ·
                refine ⟨115176940482690375669590129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 76784626988460250446393419 115176940482690375669590129)
                ·
                  refine ⟨86382705362017781752192597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 115176940482690375669590129 86382705362017781752192597)
                  ·
                    refine ⟨1012297328461145879908507, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 86382705362017781752192597 1012297328461145879908507)
                    ·
                      rfl

theorem cell22_2957163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 1, 2, 8].length) (baseStart_2957163 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2957163 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2957163 prefixEnd_2957163 := by exact prefixLift 2957163
  have htrace : WordTrace (prefixWord ++ tailWord_2957163) baseStart_2957163 baseEnd_2957163 := by
    simpa [prefixWord, tailWord_2957163, baseEnd_2957163] using wordTrace_append hprefix tailTrace_2957163
  have hstable : (prefixWord ++ tailWord_2957163).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2957163).length < 2 ^ (prefixWord ++ tailWord_2957163).sum := by decide
  have hdescent : baseEnd_2957163 < baseStart_2957163 := by decide
  rcases family_descends (prefixWord ++ tailWord_2957163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2957165 : List Nat := [1, 5, 1, 1, 1, 1, 2, 3, 2, 5]
def baseStart_2957165 : Nat := 118140960795 + 2957165 * 2 ^ 59
def prefixEnd_2957165 : Nat := 4983230072969 + 3 ^ 40 * 2957165 * 2
def baseEnd_2957165 : Nat := 1012298013102018541358501

theorem tailTrace_2957165 : CollatzResearch.WordTrace tailWord_2957165 prefixEnd_2957165 1012298013102018541358501 := by
  unfold tailWord_2957165
  simp only [CollatzResearch.WordTrace]
  refine ⟨107856668331703723418536949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71904445554469148945691299 107856668331703723418536949)
  ·
    refine ⟨10111562656097224070487839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 107856668331703723418536949 10111562656097224070487839)
    ·
      refine ⟨15167343984145836105731759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10111562656097224070487839 15167343984145836105731759)
      ·
        refine ⟨22751015976218754158597639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15167343984145836105731759 22751015976218754158597639)
        ·
          refine ⟨34126523964328131237896459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22751015976218754158597639 34126523964328131237896459)
          ·
            refine ⟨51189785946492196856844689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34126523964328131237896459 51189785946492196856844689)
            ·
              refine ⟨38392339459869147642633517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51189785946492196856844689 38392339459869147642633517)
              ·
                refine ⟨14397127297450930365987569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38392339459869147642633517 14397127297450930365987569)
                ·
                  refine ⟨10797845473088197774490677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14397127297450930365987569 10797845473088197774490677)
                  ·
                    refine ⟨1012298013102018541358501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10797845473088197774490677 1012298013102018541358501)
                    ·
                      rfl

theorem cell22_2957165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 2, 3, 2, 5].length) (baseStart_2957165 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2957165 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2957165 prefixEnd_2957165 := by exact prefixLift 2957165
  have htrace : WordTrace (prefixWord ++ tailWord_2957165) baseStart_2957165 baseEnd_2957165 := by
    simpa [prefixWord, tailWord_2957165, baseEnd_2957165] using wordTrace_append hprefix tailTrace_2957165
  have hstable : (prefixWord ++ tailWord_2957165).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2957165).length < 2 ^ (prefixWord ++ tailWord_2957165).sum := by decide
  have hdescent : baseEnd_2957165 < baseStart_2957165 := by decide
  rcases family_descends (prefixWord ++ tailWord_2957165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2957349 : List Nat := [1, 3, 1, 2, 2, 3, 3, 2, 1, 4]
def baseStart_2957349 : Nat := 118140960795 + 2957349 * 2 ^ 59
def prefixEnd_2957349 : Nat := 4983230072969 + 3 ^ 40 * 2957349 * 2
def baseEnd_2957349 : Nat := 1012361000062303394757937

theorem tailTrace_2957349 : CollatzResearch.WordTrace tailWord_2957349 prefixEnd_2957349 1012361000062303394757937 := by
  unfold tailWord_2957349
  simp only [CollatzResearch.WordTrace]
  refine ⟨107863379363037122843235101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71908919575358081895490067 107863379363037122843235101)
  ·
    refine ⟨40448767261138921066213163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 107863379363037122843235101 40448767261138921066213163)
    ·
      refine ⟨60673150891708381599319745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40448767261138921066213163 60673150891708381599319745)
      ·
        refine ⟨45504863168781286199489809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60673150891708381599319745 45504863168781286199489809)
        ·
          refine ⟨34128647376585964649617357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45504863168781286199489809 34128647376585964649617357)
          ·
            refine ⟨12798242766219736743606509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34128647376585964649617357 12798242766219736743606509)
            ·
              refine ⟨4799341037332401278852441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12798242766219736743606509 4799341037332401278852441)
              ·
                refine ⟨3599505777999300959139331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4799341037332401278852441 3599505777999300959139331)
                ·
                  refine ⟨5399258666998951438708997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3599505777999300959139331 5399258666998951438708997)
                  ·
                    refine ⟨1012361000062303394757937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5399258666998951438708997 1012361000062303394757937)
                    ·
                      rfl

theorem cell22_2957349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 3, 2, 1, 4].length) (baseStart_2957349 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2957349 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2957349 prefixEnd_2957349 := by exact prefixLift 2957349
  have htrace : WordTrace (prefixWord ++ tailWord_2957349) baseStart_2957349 baseEnd_2957349 := by
    simpa [prefixWord, tailWord_2957349, baseEnd_2957349] using wordTrace_append hprefix tailTrace_2957349
  have hstable : (prefixWord ++ tailWord_2957349).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2957349).length < 2 ^ (prefixWord ++ tailWord_2957349).sum := by decide
  have hdescent : baseEnd_2957349 < baseStart_2957349 := by decide
  rcases family_descends (prefixWord ++ tailWord_2957349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2957362 : List Nat := [3, 2, 1, 1, 2, 3, 1, 1, 3, 5]
def baseStart_2957362 : Nat := 118140960795 + 2957362 * 2 ^ 59
def prefixEnd_2957362 : Nat := 4983230072969 + 3 ^ 40 * 2957362 * 2
def baseEnd_2957362 : Nat := 1012365450227975694182897

theorem tailTrace_2957362 : CollatzResearch.WordTrace tailWord_2957362 prefixEnd_2957362 1012365450227975694182897 := by
  unfold tailWord_2957362
  simp only [CollatzResearch.WordTrace]
  refine ⟨26965963377997506515864585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71909235674660017375638893 26965963377997506515864585)
  ·
    refine ⟨20224472533498129886898439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26965963377997506515864585 20224472533498129886898439)
    ·
      refine ⟨30336708800247194830347659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20224472533498129886898439 30336708800247194830347659)
      ·
        refine ⟨45505063200370792245521489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30336708800247194830347659 45505063200370792245521489)
        ·
          refine ⟨34128797400278094184141117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45505063200370792245521489 34128797400278094184141117)
          ·
            refine ⟨12798299025104285319052919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34128797400278094184141117 12798299025104285319052919)
            ·
              refine ⟨19197448537656427978579379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12798299025104285319052919 19197448537656427978579379)
              ·
                refine ⟨28796172806484641967869069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19197448537656427978579379 28796172806484641967869069)
                ·
                  refine ⟨10798564802431740737950901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28796172806484641967869069 10798564802431740737950901)
                  ·
                    refine ⟨1012365450227975694182897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10798564802431740737950901 1012365450227975694182897)
                    ·
                      rfl

theorem cell22_2957362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 1, 1, 3, 5].length) (baseStart_2957362 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2957362 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2957362 prefixEnd_2957362 := by exact prefixLift 2957362
  have htrace : WordTrace (prefixWord ++ tailWord_2957362) baseStart_2957362 baseEnd_2957362 := by
    simpa [prefixWord, tailWord_2957362, baseEnd_2957362] using wordTrace_append hprefix tailTrace_2957362
  have hstable : (prefixWord ++ tailWord_2957362).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2957362).length < 2 ^ (prefixWord ++ tailWord_2957362).sum := by decide
  have hdescent : baseEnd_2957362 < baseStart_2957362 := by decide
  rcases family_descends (prefixWord ++ tailWord_2957362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2957460 : List Nat := [2, 4, 2, 3, 2, 1, 2, 6]
def baseStart_2957460 : Nat := 118140960795 + 2957460 * 2 ^ 59
def prefixEnd_2957460 : Nat := 4983230072969 + 3 ^ 40 * 2957460 * 2
def baseEnd_2957460 : Nat := 112488777514526233914733

theorem tailTrace_2957460 : CollatzResearch.WordTrace tailWord_2957460 prefixEnd_2957460 112488777514526233914733 := by
  unfold tailWord_2957460
  simp only [CollatzResearch.WordTrace]
  refine ⟨53933713932817494400262917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71911618577089992533683889 53933713932817494400262917)
  ·
    refine ⟨10112571362403280200049297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 53933713932817494400262917 10112571362403280200049297)
    ·
      refine ⟨7584428521802460150036973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10112571362403280200049297 7584428521802460150036973)
      ·
        refine ⟨2844160695675922556263865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7584428521802460150036973 2844160695675922556263865)
        ·
          refine ⟨2133120521756941917197899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2844160695675922556263865 2133120521756941917197899)
          ·
            refine ⟨3199680782635412875796849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2133120521756941917197899 3199680782635412875796849)
            ·
              refine ⟨2399760586976559656847637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3199680782635412875796849 2399760586976559656847637)
              ·
                refine ⟨112488777514526233914733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2399760586976559656847637 112488777514526233914733)
                ·
                  rfl

theorem cell22_2957460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 2, 1, 2, 6].length) (baseStart_2957460 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2957460 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2957460 prefixEnd_2957460 := by exact prefixLift 2957460
  have htrace : WordTrace (prefixWord ++ tailWord_2957460) baseStart_2957460 baseEnd_2957460 := by
    simpa [prefixWord, tailWord_2957460, baseEnd_2957460] using wordTrace_append hprefix tailTrace_2957460
  have hstable : (prefixWord ++ tailWord_2957460).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2957460).length < 2 ^ (prefixWord ++ tailWord_2957460).sum := by decide
  have hdescent : baseEnd_2957460 < baseStart_2957460 := by decide
  rcases family_descends (prefixWord ++ tailWord_2957460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2957505 : List Nat := [1, 2, 6, 1, 2, 2, 2, 1, 5]
def baseStart_2957505 : Nat := 118140960795 + 2957505 * 2 ^ 59
def prefixEnd_2957505 : Nat := 4983230072969 + 3 ^ 40 * 2957505 * 2
def baseEnd_2957505 : Nat := 337471467350123662619153

theorem tailTrace_2957505 : CollatzResearch.WordTrace tailWord_2957505 prefixEnd_2957505 337471467350123662619153 := by
  unfold tailWord_2957505
  simp only [CollatzResearch.WordTrace]
  refine ⟨107869069150471961485913969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71912712766981307657275979 107869069150471961485913969)
  ·
    refine ⟨80901801862853971114435477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107869069150471961485913969 80901801862853971114435477)
    ·
      refine ⟨3792271962321279895989163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 80901801862853971114435477 3792271962321279895989163)
      ·
        refine ⟨5688407943481919843983745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3792271962321279895989163 5688407943481919843983745)
        ·
          refine ⟨4266305957611439882987809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5688407943481919843983745 4266305957611439882987809)
          ·
            refine ⟨3199729468208579912240857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4266305957611439882987809 3199729468208579912240857)
            ·
              refine ⟨2399797101156434934180643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3199729468208579912240857 2399797101156434934180643)
              ·
                refine ⟨3599695651734652401270965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2399797101156434934180643 3599695651734652401270965)
                ·
                  refine ⟨337471467350123662619153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3599695651734652401270965 337471467350123662619153)
                  ·
                    rfl

theorem cell22_2957505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 2, 2, 1, 5].length) (baseStart_2957505 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2957505 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2957505 prefixEnd_2957505 := by exact prefixLift 2957505
  have htrace : WordTrace (prefixWord ++ tailWord_2957505) baseStart_2957505 baseEnd_2957505 := by
    simpa [prefixWord, tailWord_2957505, baseEnd_2957505] using wordTrace_append hprefix tailTrace_2957505
  have hstable : (prefixWord ++ tailWord_2957505).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2957505).length < 2 ^ (prefixWord ++ tailWord_2957505).sum := by decide
  have hdescent : baseEnd_2957505 < baseStart_2957505 := by decide
  rcases family_descends (prefixWord ++ tailWord_2957505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2957514 : List Nat := [3, 1, 2, 1, 3, 1, 2, 3, 1, 5]
def baseStart_2957514 : Nat := 118140960795 + 2957514 * 2 ^ 59
def prefixEnd_2957514 : Nat := 4983230072969 + 3 ^ 40 * 2957514 * 2
def baseEnd_2957514 : Nat := 1012417482934297964382431

theorem tailTrace_2957514 : CollatzResearch.WordTrace tailWord_2957514 prefixEnd_2957514 1012417482934297964382431 := by
  unfold tailWord_2957514
  simp only [CollatzResearch.WordTrace]
  refine ⟨26967349351859839005747899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71912931604959570681994397 26967349351859839005747899)
  ·
    refine ⟨40451024027789758508621849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26967349351859839005747899 40451024027789758508621849)
    ·
      refine ⟨30338268020842318881466387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40451024027789758508621849 30338268020842318881466387)
      ·
        refine ⟨45507402031263478322199581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30338268020842318881466387 45507402031263478322199581)
        ·
          refine ⟨17065275761723804370824843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45507402031263478322199581 17065275761723804370824843)
          ·
            refine ⟨25597913642585706556237265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17065275761723804370824843 25597913642585706556237265)
            ·
              refine ⟨19198435231939279917177949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25597913642585706556237265 19198435231939279917177949)
              ·
                refine ⟨7199413211977229968941731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19198435231939279917177949 7199413211977229968941731)
                ·
                  refine ⟨10799119817965844953412597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7199413211977229968941731 10799119817965844953412597)
                  ·
                    refine ⟨1012417482934297964382431, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10799119817965844953412597 1012417482934297964382431)
                    ·
                      rfl

theorem cell22_2957514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 2, 3, 1, 5].length) (baseStart_2957514 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2957514 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2957514 prefixEnd_2957514 := by exact prefixLift 2957514
  have htrace : WordTrace (prefixWord ++ tailWord_2957514) baseStart_2957514 baseEnd_2957514 := by
    simpa [prefixWord, tailWord_2957514, baseEnd_2957514] using wordTrace_append hprefix tailTrace_2957514
  have hstable : (prefixWord ++ tailWord_2957514).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2957514).length < 2 ^ (prefixWord ++ tailWord_2957514).sum := by decide
  have hdescent : baseEnd_2957514 < baseStart_2957514 := by decide
  rcases family_descends (prefixWord ++ tailWord_2957514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2957518 : List Nat := [4, 1, 1, 1, 4, 3, 1, 2, 1, 4]
def baseStart_2957518 : Nat := 118140960795 + 2957518 * 2 ^ 59
def prefixEnd_2957518 : Nat := 4983230072969 + 3 ^ 40 * 2957518 * 2
def baseEnd_2957518 : Nat := 1012418852216043287282419

theorem tailTrace_2957518 : CollatzResearch.WordTrace tailWord_2957518 prefixEnd_2957518 1012418852216043287282419 := by
  unfold tailWord_2957518
  simp only [CollatzResearch.WordTrace]
  refine ⟨13483692912428108088267151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 71913028866283243137424805 13483692912428108088267151)
  ·
    refine ⟨20225539368642162132400727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13483692912428108088267151 20225539368642162132400727)
    ·
      refine ⟨30338309052963243198601091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20225539368642162132400727 30338309052963243198601091)
      ·
        refine ⟨45507463579444864797901637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30338309052963243198601091 45507463579444864797901637)
        ·
          refine ⟨8532649421145912149606557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 45507463579444864797901637 8532649421145912149606557)
          ·
            refine ⟨3199743532929717056102459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8532649421145912149606557 3199743532929717056102459)
            ·
              refine ⟨4799615299394575584153689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3199743532929717056102459 4799615299394575584153689)
              ·
                refine ⟨3599711474545931688115267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4799615299394575584153689 3599711474545931688115267)
                ·
                  refine ⟨5399567211818897532172901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3599711474545931688115267 5399567211818897532172901)
                  ·
                    refine ⟨1012418852216043287282419, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5399567211818897532172901 1012418852216043287282419)
                    ·
                      rfl

theorem cell22_2957518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 3, 1, 2, 1, 4].length) (baseStart_2957518 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2957518 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2957518 prefixEnd_2957518 := by exact prefixLift 2957518
  have htrace : WordTrace (prefixWord ++ tailWord_2957518) baseStart_2957518 baseEnd_2957518 := by
    simpa [prefixWord, tailWord_2957518, baseEnd_2957518] using wordTrace_append hprefix tailTrace_2957518
  have hstable : (prefixWord ++ tailWord_2957518).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2957518).length < 2 ^ (prefixWord ++ tailWord_2957518).sum := by decide
  have hdescent : baseEnd_2957518 < baseStart_2957518 := by decide
  rcases family_descends (prefixWord ++ tailWord_2957518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2957529 : List Nat := [1, 2, 1, 2, 3, 1, 3, 3, 2, 4]
def baseStart_2957529 : Nat := 118140960795 + 2957529 * 2 ^ 59
def prefixEnd_2957529 : Nat := 4983230072969 + 3 ^ 40 * 2957529 * 2
def baseEnd_2957529 : Nat := 1012422617740842925257385

theorem tailTrace_2957529 : CollatzResearch.WordTrace tailWord_2957529 prefixEnd_2957529 1012422617740842925257385 := by
  unfold tailWord_2957529
  simp only [CollatzResearch.WordTrace]
  refine ⟨107869944502385013584787641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71913296334923342389858427 107869944502385013584787641)
  ·
    refine ⟨80902458376788760188590731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107869944502385013584787641 80902458376788760188590731)
    ·
      refine ⟨121353687565183140282886097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80902458376788760188590731 121353687565183140282886097)
      ·
        refine ⟨91015265673887355212164573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 121353687565183140282886097 91015265673887355212164573)
        ·
          refine ⟨34130724627707758204561715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 91015265673887355212164573 34130724627707758204561715)
          ·
            refine ⟨51196086941561637306842573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34130724627707758204561715 51196086941561637306842573)
            ·
              refine ⟨19198532603085613990065965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 51196086941561637306842573 19198532603085613990065965)
              ·
                refine ⟨7199449726157105246274737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19198532603085613990065965 7199449726157105246274737)
                ·
                  refine ⟨5399587294617828934706053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7199449726157105246274737 5399587294617828934706053)
                  ·
                    refine ⟨1012422617740842925257385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5399587294617828934706053 1012422617740842925257385)
                    ·
                      rfl

theorem cell22_2957529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 3, 3, 2, 4].length) (baseStart_2957529 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2957529 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2957529 prefixEnd_2957529 := by exact prefixLift 2957529
  have htrace : WordTrace (prefixWord ++ tailWord_2957529) baseStart_2957529 baseEnd_2957529 := by
    simpa [prefixWord, tailWord_2957529, baseEnd_2957529] using wordTrace_append hprefix tailTrace_2957529
  have hstable : (prefixWord ++ tailWord_2957529).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2957529).length < 2 ^ (prefixWord ++ tailWord_2957529).sum := by decide
  have hdescent : baseEnd_2957529 < baseStart_2957529 := by decide
  rcases family_descends (prefixWord ++ tailWord_2957529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2957576 : List Nat := [2, 1, 3, 2, 3, 1, 1, 1, 5, 3]
def baseStart_2957576 : Nat := 118140960795 + 2957576 * 2 ^ 59
def prefixEnd_2957576 : Nat := 4983230072969 + 3 ^ 40 * 2957576 * 2
def baseEnd_2957576 : Nat := 1012438706801350469332241

theorem tailTrace_2957576 : CollatzResearch.WordTrace tailWord_2957576 prefixEnd_2957576 1012438706801350469332241 := by
  unfold tailWord_2957576
  simp only [CollatzResearch.WordTrace]
  refine ⟨53935829366607370305874291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71914439155476493741165721 53935829366607370305874291)
  ·
    refine ⟨80903744049911055458811437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53935829366607370305874291 80903744049911055458811437)
    ·
      refine ⟨30338904018716645797054289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 80903744049911055458811437 30338904018716645797054289)
      ·
        refine ⟨22754178014037484347790717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30338904018716645797054289 22754178014037484347790717)
        ·
          refine ⟨8532816755264056630421519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22754178014037484347790717 8532816755264056630421519)
          ·
            refine ⟨12799225132896084945632279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8532816755264056630421519 12799225132896084945632279)
            ·
              refine ⟨19198837699344127418448419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12799225132896084945632279 19198837699344127418448419)
              ·
                refine ⟨28798256549016191127672629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19198837699344127418448419 28798256549016191127672629)
                ·
                  refine ⟨2699836551470267918219309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 28798256549016191127672629 2699836551470267918219309)
                  ·
                    refine ⟨1012438706801350469332241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2699836551470267918219309 1012438706801350469332241)
                    ·
                      rfl

theorem cell22_2957576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 1, 1, 5, 3].length) (baseStart_2957576 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2957576 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2957576 prefixEnd_2957576 := by exact prefixLift 2957576
  have htrace : WordTrace (prefixWord ++ tailWord_2957576) baseStart_2957576 baseEnd_2957576 := by
    simpa [prefixWord, tailWord_2957576, baseEnd_2957576] using wordTrace_append hprefix tailTrace_2957576
  have hstable : (prefixWord ++ tailWord_2957576).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2957576).length < 2 ^ (prefixWord ++ tailWord_2957576).sum := by decide
  have hdescent : baseEnd_2957576 < baseStart_2957576 := by decide
  rcases family_descends (prefixWord ++ tailWord_2957576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2957610 : List Nat := [3, 1, 4, 2, 2, 1, 2, 1, 3, 3]
def baseStart_2957610 : Nat := 118140960795 + 2957610 * 2 ^ 59
def prefixEnd_2957610 : Nat := 4983230072969 + 3 ^ 40 * 2957610 * 2
def baseEnd_2957610 : Nat := 1012450345696185713982137

theorem tailTrace_2957610 : CollatzResearch.WordTrace tailWord_2957610 prefixEnd_2957610 1012450345696185713982137 := by
  unfold tailWord_2957610
  simp only [CollatzResearch.WordTrace]
  refine ⟨26968224703772891104621571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71915265876727709612324189 26968224703772891104621571)
  ·
    refine ⟨40452337055659336656932357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26968224703772891104621571 40452337055659336656932357)
    ·
      refine ⟨7584813197936125623174817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 40452337055659336656932357 7584813197936125623174817)
      ·
        refine ⟨5688609898452094217381113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7584813197936125623174817 5688609898452094217381113)
        ·
          refine ⟨4266457423839070663035835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5688609898452094217381113 4266457423839070663035835)
          ·
            refine ⟨6399686135758605994553753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4266457423839070663035835 6399686135758605994553753)
            ·
              refine ⟨4799764601818954495915315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6399686135758605994553753 4799764601818954495915315)
              ·
                refine ⟨7199646902728431743872973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4799764601818954495915315 7199646902728431743872973)
                ·
                  refine ⟨2699867588523161903952365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7199646902728431743872973 2699867588523161903952365)
                  ·
                    refine ⟨1012450345696185713982137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2699867588523161903952365 1012450345696185713982137)
                    ·
                      rfl

theorem cell22_2957610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 1, 2, 1, 3, 3].length) (baseStart_2957610 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2957610 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2957610 prefixEnd_2957610 := by exact prefixLift 2957610
  have htrace : WordTrace (prefixWord ++ tailWord_2957610) baseStart_2957610 baseEnd_2957610 := by
    simpa [prefixWord, tailWord_2957610, baseEnd_2957610] using wordTrace_append hprefix tailTrace_2957610
  have hstable : (prefixWord ++ tailWord_2957610).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2957610).length < 2 ^ (prefixWord ++ tailWord_2957610).sum := by decide
  have hdescent : baseEnd_2957610 < baseStart_2957610 := by decide
  rcases family_descends (prefixWord ++ tailWord_2957610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2957651 : List Nat := [1, 1, 1, 2, 1, 1, 4, 7, 4]
def baseStart_2957651 : Nat := 118140960795 + 2957651 * 2 ^ 59
def prefixEnd_2957651 : Nat := 4983230072969 + 3 ^ 40 * 2957651 * 2
def baseEnd_2957651 : Nat := 337488126944691757902337

theorem tailTrace_2957651 : CollatzResearch.WordTrace tailWord_2957651 prefixEnd_2957651 337488126944691757902337 := by
  unfold tailWord_2957651
  simp only [CollatzResearch.WordTrace]
  refine ⟨107874394207943028420728807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71916262805295352280485871 107874394207943028420728807)
  ·
    refine ⟨161811591311914542631093211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107874394207943028420728807 161811591311914542631093211)
    ·
      refine ⟨242717386967871813946639817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 161811591311914542631093211 242717386967871813946639817)
      ·
        refine ⟨182038040225903860459979863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 242717386967871813946639817 182038040225903860459979863)
        ·
          refine ⟨273057060338855790689969795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 182038040225903860459979863 273057060338855790689969795)
          ·
            refine ⟨409585590508283686034954693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 273057060338855790689969795 409585590508283686034954693)
            ·
              refine ⟨76797298220303191131554005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 409585590508283686034954693 76797298220303191131554005)
              ·
                refine ⟨1799936677038356042145797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 76797298220303191131554005 1799936677038356042145797)
                ·
                  refine ⟨337488126944691757902337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1799936677038356042145797 337488126944691757902337)
                  ·
                    rfl

theorem cell22_2957651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 7, 4].length) (baseStart_2957651 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2957651 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2957651 prefixEnd_2957651 := by exact prefixLift 2957651
  have htrace : WordTrace (prefixWord ++ tailWord_2957651) baseStart_2957651 baseEnd_2957651 := by
    simpa [prefixWord, tailWord_2957651, baseEnd_2957651] using wordTrace_append hprefix tailTrace_2957651
  have hstable : (prefixWord ++ tailWord_2957651).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2957651).length < 2 ^ (prefixWord ++ tailWord_2957651).sum := by decide
  have hdescent : baseEnd_2957651 < baseStart_2957651 := by decide
  rcases family_descends (prefixWord ++ tailWord_2957651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2957801 : List Nat := [1, 2, 1, 1, 1, 2, 1, 7, 1, 5]
def baseStart_2957801 : Nat := 118140960795 + 2957801 * 2 ^ 59
def prefixEnd_2957801 : Nat := 4983230072969 + 3 ^ 40 * 2957801 * 2
def baseEnd_2957801 : Nat := 1012515728899524882456551

theorem tailTrace_2957801 : CollatzResearch.WordTrace tailWord_2957801 prefixEnd_2957801 1012515728899524882456551 := by
  unfold tailWord_2957801
  simp only [CollatzResearch.WordTrace]
  refine ⟨107879865157399604038689257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71919910104933069359126171 107879865157399604038689257)
  ·
    refine ⟨80909898868049703029016943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107879865157399604038689257 80909898868049703029016943)
    ·
      refine ⟨121364848302074554543525415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80909898868049703029016943 121364848302074554543525415)
      ·
        refine ⟨182047272453111831815288123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121364848302074554543525415 182047272453111831815288123)
        ·
          refine ⟨273070908679667747722932185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 182047272453111831815288123 273070908679667747722932185)
          ·
            refine ⟨204803181509750810792199139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 273070908679667747722932185 204803181509750810792199139)
            ·
              refine ⟨307204772264626216188298709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 204803181509750810792199139 307204772264626216188298709)
              ·
                refine ⟨7200111849952176941913251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 307204772264626216188298709 7200111849952176941913251)
                ·
                  refine ⟨10800167774928265412869877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7200111849952176941913251 10800167774928265412869877)
                  ·
                    refine ⟨1012515728899524882456551, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10800167774928265412869877 1012515728899524882456551)
                    ·
                      rfl

theorem cell22_2957801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 7, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 7, 1, 5].length) (baseStart_2957801 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2957801 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2957801 prefixEnd_2957801 := by exact prefixLift 2957801
  have htrace : WordTrace (prefixWord ++ tailWord_2957801) baseStart_2957801 baseEnd_2957801 := by
    simpa [prefixWord, tailWord_2957801, baseEnd_2957801] using wordTrace_append hprefix tailTrace_2957801
  have hstable : (prefixWord ++ tailWord_2957801).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2957801).length < 2 ^ (prefixWord ++ tailWord_2957801).sum := by decide
  have hdescent : baseEnd_2957801 < baseStart_2957801 := by decide
  rcases family_descends (prefixWord ++ tailWord_2957801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2957805 : List Nat := [1, 5, 1, 3, 1, 1, 1, 4, 1, 4]
def baseStart_2957805 : Nat := 118140960795 + 2957805 * 2 ^ 59
def prefixEnd_2957805 : Nat := 4983230072969 + 3 ^ 40 * 2957805 * 2
def baseEnd_2957805 : Nat := 1012517098181270205356539

theorem tailTrace_2957805 : CollatzResearch.WordTrace tailWord_2957805 prefixEnd_2957805 1012517098181270205356539 := by
  unfold tailWord_2957805
  simp only [CollatzResearch.WordTrace]
  refine ⟨107880011049385112721834869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71920007366256741814556579 107880011049385112721834869)
  ·
    refine ⟨10113751035879854317672019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 107880011049385112721834869 10113751035879854317672019)
    ·
      refine ⟨15170626553819781476508029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10113751035879854317672019 15170626553819781476508029)
      ·
        refine ⟨5688984957682418053690511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15170626553819781476508029 5688984957682418053690511)
        ·
          refine ⟨8533477436523627080535767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5688984957682418053690511 8533477436523627080535767)
          ·
            refine ⟨12800216154785440620803651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8533477436523627080535767 12800216154785440620803651)
            ·
              refine ⟨19200324232178160931205477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12800216154785440620803651 19200324232178160931205477)
              ·
                refine ⟨3600060793533405174601027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19200324232178160931205477 3600060793533405174601027)
                ·
                  refine ⟨5400091190300107761901541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3600060793533405174601027 5400091190300107761901541)
                  ·
                    refine ⟨1012517098181270205356539, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5400091190300107761901541 1012517098181270205356539)
                    ·
                      rfl

theorem cell22_2957805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 1, 4, 1, 4].length) (baseStart_2957805 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2957805 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2957805 prefixEnd_2957805 := by exact prefixLift 2957805
  have htrace : WordTrace (prefixWord ++ tailWord_2957805) baseStart_2957805 baseEnd_2957805 := by
    simpa [prefixWord, tailWord_2957805, baseEnd_2957805] using wordTrace_append hprefix tailTrace_2957805
  have hstable : (prefixWord ++ tailWord_2957805).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2957805).length < 2 ^ (prefixWord ++ tailWord_2957805).sum := by decide
  have hdescent : baseEnd_2957805 < baseStart_2957805 := by decide
  rcases family_descends (prefixWord ++ tailWord_2957805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2957816 : List Nat := [2, 1, 2, 1, 1, 4, 1, 3, 1, 6]
def baseStart_2957816 : Nat := 118140960795 + 2957816 * 2 ^ 59
def prefixEnd_2957816 : Nat := 4983230072969 + 3 ^ 40 * 2957816 * 2
def baseEnd_2957816 : Nat := 1012520863706069843331505

theorem tailTrace_2957816 : CollatzResearch.WordTrace tailWord_2957816 prefixEnd_2957816 1012520863706069843331505 := by
  unfold tailWord_2957816
  simp only [CollatzResearch.WordTrace]
  refine ⟨53940206126172630800242651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71920274834896841066990201 53940206126172630800242651)
  ·
    refine ⟨80910309189258946200363977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53940206126172630800242651 80910309189258946200363977)
    ·
      refine ⟨60682731891944209650272983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80910309189258946200363977 60682731891944209650272983)
      ·
        refine ⟨91024097837916314475409475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60682731891944209650272983 91024097837916314475409475)
        ·
          refine ⟨136536146756874471713114213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91024097837916314475409475 136536146756874471713114213)
          ·
            refine ⟨25600527516913963446208915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 136536146756874471713114213 25600527516913963446208915)
            ·
              refine ⟨38400791275370945169313373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25600527516913963446208915 38400791275370945169313373)
              ·
                refine ⟨14400296728264104438492515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38400791275370945169313373 14400296728264104438492515)
                ·
                  refine ⟨21600445092396156657738773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14400296728264104438492515 21600445092396156657738773)
                  ·
                    refine ⟨1012520863706069843331505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21600445092396156657738773 1012520863706069843331505)
                    ·
                      rfl

theorem cell22_2957816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 1, 3, 1, 6].length) (baseStart_2957816 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2957816 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2957816 prefixEnd_2957816 := by exact prefixLift 2957816
  have htrace : WordTrace (prefixWord ++ tailWord_2957816) baseStart_2957816 baseEnd_2957816 := by
    simpa [prefixWord, tailWord_2957816, baseEnd_2957816] using wordTrace_append hprefix tailTrace_2957816
  have hstable : (prefixWord ++ tailWord_2957816).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2957816).length < 2 ^ (prefixWord ++ tailWord_2957816).sum := by decide
  have hdescent : baseEnd_2957816 < baseStart_2957816 := by decide
  rcases family_descends (prefixWord ++ tailWord_2957816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2957837 : List Nat := [1, 7, 1, 1, 1, 1, 3, 1, 6]
def baseStart_2957837 : Nat := 118140960795 + 2957837 * 2 ^ 59
def prefixEnd_2957837 : Nat := 4983230072969 + 3 ^ 40 * 2957837 * 2
def baseEnd_2957837 : Nat := 337509350811744262852147

theorem tailTrace_2957837 : CollatzResearch.WordTrace tailWord_2957837 prefixEnd_2957837 337509350811744262852147 := by
  unfold tailWord_2957837
  simp only [CollatzResearch.WordTrace]
  refine ⟨107881178185269182186999765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71920785456846121457999843 107881178185269182186999765)
  ·
    refine ⟨2528465113717246457507807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 107881178185269182186999765 2528465113717246457507807)
    ·
      refine ⟨3792697670575869686261711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2528465113717246457507807 3792697670575869686261711)
      ·
        refine ⟨5689046505863804529392567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3792697670575869686261711 5689046505863804529392567)
        ·
          refine ⟨8533569758795706794088851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5689046505863804529392567 8533569758795706794088851)
          ·
            refine ⟨12800354638193560191133277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8533569758795706794088851 12800354638193560191133277)
            ·
              refine ⟨4800132989322585071674979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12800354638193560191133277 4800132989322585071674979)
              ·
                refine ⟨7200199483983877607512469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4800132989322585071674979 7200199483983877607512469)
                ·
                  refine ⟨337509350811744262852147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7200199483983877607512469 337509350811744262852147)
                  ·
                    rfl

theorem cell22_2957837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 3, 1, 6].length) (baseStart_2957837 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2957837 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2957837 prefixEnd_2957837 := by exact prefixLift 2957837
  have htrace : WordTrace (prefixWord ++ tailWord_2957837) baseStart_2957837 baseEnd_2957837 := by
    simpa [prefixWord, tailWord_2957837, baseEnd_2957837] using wordTrace_append hprefix tailTrace_2957837
  have hstable : (prefixWord ++ tailWord_2957837).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2957837).length < 2 ^ (prefixWord ++ tailWord_2957837).sum := by decide
  have hdescent : baseEnd_2957837 < baseStart_2957837 := by decide
  rcases family_descends (prefixWord ++ tailWord_2957837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2957848 : List Nat := [2, 1, 2, 3, 3, 2, 2, 7]
def baseStart_2957848 : Nat := 118140960795 + 2957848 * 2 ^ 59
def prefixEnd_2957848 : Nat := 4983230072969 + 3 ^ 40 * 2957848 * 2
def baseEnd_2957848 : Nat := 112503535328892491836823

theorem tailTrace_2957848 : CollatzResearch.WordTrace tailWord_2957848 prefixEnd_2957848 112503535328892491836823 := by
  unfold tailWord_2957848
  simp only [CollatzResearch.WordTrace]
  refine ⟨53940789694114665532825099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71921052925486220710433465 53940789694114665532825099)
  ·
    refine ⟨80911184541171998299237649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53940789694114665532825099 80911184541171998299237649)
    ·
      refine ⟨60683388405878998724428237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80911184541171998299237649 60683388405878998724428237)
      ·
        refine ⟨22756270652204624521660589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 60683388405878998724428237 22756270652204624521660589)
        ·
          refine ⟨8533601494576734195622721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22756270652204624521660589 8533601494576734195622721)
          ·
            refine ⟨6400201120932550646717041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8533601494576734195622721 6400201120932550646717041)
            ·
              refine ⟨4800150840699412985037781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6400201120932550646717041 4800150840699412985037781)
              ·
                refine ⟨112503535328892491836823, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4800150840699412985037781 112503535328892491836823)
                ·
                  rfl

theorem cell22_2957848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 2, 2, 7].length) (baseStart_2957848 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2957848 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2957848 prefixEnd_2957848 := by exact prefixLift 2957848
  have htrace : WordTrace (prefixWord ++ tailWord_2957848) baseStart_2957848 baseEnd_2957848 := by
    simpa [prefixWord, tailWord_2957848, baseEnd_2957848] using wordTrace_append hprefix tailTrace_2957848
  have hstable : (prefixWord ++ tailWord_2957848).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2957848).length < 2 ^ (prefixWord ++ tailWord_2957848).sum := by decide
  have hdescent : baseEnd_2957848 < baseStart_2957848 := by decide
  rcases family_descends (prefixWord ++ tailWord_2957848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2957852 : List Nat := [2, 2, 3, 1, 2, 2, 4, 1, 2, 3]
def baseStart_2957852 : Nat := 118140960795 + 2957852 * 2 ^ 59
def prefixEnd_2957852 : Nat := 4983230072969 + 3 ^ 40 * 2957852 * 2
def baseEnd_2957852 : Nat := 1012533187241777749431395

theorem tailTrace_2957852 : CollatzResearch.WordTrace tailWord_2957852 prefixEnd_2957852 1012533187241777749431395 := by
  unfold tailWord_2957852
  simp only [CollatzResearch.WordTrace]
  refine ⟨53940862640107419874397905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71921150186809893165863873 53940862640107419874397905)
  ·
    refine ⟨40455646980080564905798429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53940862640107419874397905 40455646980080564905798429)
    ·
      refine ⟨15170867617530211839674411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40455646980080564905798429 15170867617530211839674411)
      ·
        refine ⟨22756301426295317759511617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15170867617530211839674411 22756301426295317759511617)
        ·
          refine ⟨17067226069721488319633713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22756301426295317759511617 17067226069721488319633713)
          ·
            refine ⟨12800419552291116239725285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17067226069721488319633713 12800419552291116239725285)
            ·
              refine ⟨2400078666054584294948491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12800419552291116239725285 2400078666054584294948491)
              ·
                refine ⟨3600117999081876442422737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2400078666054584294948491 3600117999081876442422737)
                ·
                  refine ⟨2700088499311407331817053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3600117999081876442422737 2700088499311407331817053)
                  ·
                    refine ⟨1012533187241777749431395, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2700088499311407331817053 1012533187241777749431395)
                    ·
                      rfl

theorem cell22_2957852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 4, 1, 2, 3].length) (baseStart_2957852 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2957852 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2957852 prefixEnd_2957852 := by exact prefixLift 2957852
  have htrace : WordTrace (prefixWord ++ tailWord_2957852) baseStart_2957852 baseEnd_2957852 := by
    simpa [prefixWord, tailWord_2957852, baseEnd_2957852] using wordTrace_append hprefix tailTrace_2957852
  have hstable : (prefixWord ++ tailWord_2957852).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2957852).length < 2 ^ (prefixWord ++ tailWord_2957852).sum := by decide
  have hdescent : baseEnd_2957852 < baseStart_2957852 := by decide
  rcases family_descends (prefixWord ++ tailWord_2957852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2957869 : List Nat := [1, 5, 4, 1, 1, 1, 1, 2, 1, 5]
def baseStart_2957869 : Nat := 118140960795 + 2957869 * 2 ^ 59
def prefixEnd_2957869 : Nat := 4983230072969 + 3 ^ 40 * 2957869 * 2
def baseEnd_2957869 : Nat := 1012539006689195371756343

theorem tailTrace_2957869 : CollatzResearch.WordTrace tailWord_2957869 prefixEnd_2957869 1012539006689195371756343 := by
  unfold tailWord_2957869
  simp only [CollatzResearch.WordTrace]
  refine ⟨107882345321153251652164661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71921563547435501101443107 107882345321153251652164661)
  ·
    refine ⟨10113969873858117342390437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 107882345321153251652164661 10113969873858117342390437)
    ·
      refine ⟨1896369351348397001698207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10113969873858117342390437 1896369351348397001698207)
      ·
        refine ⟨2844554027022595502547311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1896369351348397001698207 2844554027022595502547311)
        ·
          refine ⟨4266831040533893253820967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2844554027022595502547311 4266831040533893253820967)
          ·
            refine ⟨6400246560800839880731451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4266831040533893253820967 6400246560800839880731451)
            ·
              refine ⟨9600369841201259821097177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6400246560800839880731451 9600369841201259821097177)
              ·
                refine ⟨7200277380900944865822883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9600369841201259821097177 7200277380900944865822883)
                ·
                  refine ⟨10800416071351417298734325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7200277380900944865822883 10800416071351417298734325)
                  ·
                    refine ⟨1012539006689195371756343, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10800416071351417298734325 1012539006689195371756343)
                    ·
                      rfl

theorem cell22_2957869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 1, 1, 2, 1, 5].length) (baseStart_2957869 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2957869 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2957869 prefixEnd_2957869 := by exact prefixLift 2957869
  have htrace : WordTrace (prefixWord ++ tailWord_2957869) baseStart_2957869 baseEnd_2957869 := by
    simpa [prefixWord, tailWord_2957869, baseEnd_2957869] using wordTrace_append hprefix tailTrace_2957869
  have hstable : (prefixWord ++ tailWord_2957869).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2957869).length < 2 ^ (prefixWord ++ tailWord_2957869).sum := by decide
  have hdescent : baseEnd_2957869 < baseStart_2957869 := by decide
  rcases family_descends (prefixWord ++ tailWord_2957869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2957891 : List Nat := [1, 1, 1, 3, 1, 2, 1, 2, 3, 7]
def baseStart_2957891 : Nat := 118140960795 + 2957891 * 2 ^ 59
def prefixEnd_2957891 : Nat := 4983230072969 + 3 ^ 40 * 2957891 * 2
def baseEnd_2957891 : Nat := 1012546537738794647706275

theorem tailTrace_2957891 : CollatzResearch.WordTrace tailWord_2957891 prefixEnd_2957891 1012546537738794647706275 := by
  unfold tailWord_2957891
  simp only [CollatzResearch.WordTrace]
  refine ⟨107883147727073549409465527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71922098484715699606310351 107883147727073549409465527)
  ·
    refine ⟨161824721590610324114198291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107883147727073549409465527 161824721590610324114198291)
    ·
      refine ⟨242737082385915486171297437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 161824721590610324114198291 242737082385915486171297437)
      ·
        refine ⟨91026405894718307314236539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 242737082385915486171297437 91026405894718307314236539)
        ·
          refine ⟨136539608842077460971354809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91026405894718307314236539 136539608842077460971354809)
          ·
            refine ⟨102404706631558095728516107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 136539608842077460971354809 102404706631558095728516107)
            ·
              refine ⟨153607059947337143592774161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 102404706631558095728516107 153607059947337143592774161)
              ·
                refine ⟨115205294960502857694580621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 153607059947337143592774161 115205294960502857694580621)
                ·
                  refine ⟨43201985610188571635467733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 115205294960502857694580621 43201985610188571635467733)
                  ·
                    refine ⟨1012546537738794647706275, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 43201985610188571635467733 1012546537738794647706275)
                    ·
                      rfl

theorem cell22_2957891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 2, 3, 7].length) (baseStart_2957891 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2957891 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2957891 prefixEnd_2957891 := by exact prefixLift 2957891
  have htrace : WordTrace (prefixWord ++ tailWord_2957891) baseStart_2957891 baseEnd_2957891 := by
    simpa [prefixWord, tailWord_2957891, baseEnd_2957891] using wordTrace_append hprefix tailTrace_2957891
  have hstable : (prefixWord ++ tailWord_2957891).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2957891).length < 2 ^ (prefixWord ++ tailWord_2957891).sum := by decide
  have hdescent : baseEnd_2957891 < baseStart_2957891 := by decide
  rcases family_descends (prefixWord ++ tailWord_2957891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2957893 : List Nat := [1, 3, 1, 1, 1, 5, 1, 4, 5]
def baseStart_2957893 : Nat := 118140960795 + 2957893 * 2 ^ 59
def prefixEnd_2957893 : Nat := 4983230072969 + 3 ^ 40 * 2957893 * 2
def baseEnd_2957893 : Nat := 337515740793222436385423

theorem tailTrace_2957893 : CollatzResearch.WordTrace tailWord_2957893 prefixEnd_2957893 337515740793222436385423 := by
  unfold tailWord_2957893
  simp only [CollatzResearch.WordTrace]
  refine ⟨107883220673066303751038333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71922147115377535834025555 107883220673066303751038333)
  ·
    refine ⟨40456207752399863906639375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 107883220673066303751038333 40456207752399863906639375)
    ·
      refine ⟨60684311628599795859959063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40456207752399863906639375 60684311628599795859959063)
      ·
        refine ⟨91026467442899693789938595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60684311628599795859959063 91026467442899693789938595)
        ·
          refine ⟨136539701164349540684907893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91026467442899693789938595 136539701164349540684907893)
          ·
            refine ⟨12800596984157769439210115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 136539701164349540684907893 12800596984157769439210115)
            ·
              refine ⟨19200895476236654158815173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12800596984157769439210115 19200895476236654158815173)
              ·
                refine ⟨3600167901794372654777845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19200895476236654158815173 3600167901794372654777845)
                ·
                  refine ⟨337515740793222436385423, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3600167901794372654777845 337515740793222436385423)
                  ·
                    rfl

theorem cell22_2957893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 1, 4, 5].length) (baseStart_2957893 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2957893 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2957893 prefixEnd_2957893 := by exact prefixLift 2957893
  have htrace : WordTrace (prefixWord ++ tailWord_2957893) baseStart_2957893 baseEnd_2957893 := by
    simpa [prefixWord, tailWord_2957893, baseEnd_2957893] using wordTrace_append hprefix tailTrace_2957893
  have hstable : (prefixWord ++ tailWord_2957893).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2957893).length < 2 ^ (prefixWord ++ tailWord_2957893).sum := by decide
  have hdescent : baseEnd_2957893 < baseStart_2957893 := by decide
  rcases family_descends (prefixWord ++ tailWord_2957893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2957908 : List Nat := [2, 4, 1, 1, 1, 3, 1, 1, 1, 7]
def baseStart_2957908 : Nat := 118140960795 + 2957908 * 2 ^ 59
def prefixEnd_2957908 : Nat := 4983230072969 + 3 ^ 40 * 2957908 * 2
def baseEnd_2957908 : Nat := 1012552357186212270031223

theorem tailTrace_2957908 : CollatzResearch.WordTrace tailWord_2957908 prefixEnd_2957908 1012552357186212270031223 := by
  unfold tailWord_2957908
  simp only [CollatzResearch.WordTrace]
  refine ⟨53941883884005980656417189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71922511845341307541889585 53941883884005980656417189)
  ·
    refine ⟨10114103228251121373078223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 53941883884005980656417189 10114103228251121373078223)
    ·
      refine ⟨15171154842376682059617335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10114103228251121373078223 15171154842376682059617335)
      ·
        refine ⟨22756732263565023089426003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15171154842376682059617335 22756732263565023089426003)
        ·
          refine ⟨34135098395347534634139005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22756732263565023089426003 34135098395347534634139005)
          ·
            refine ⟨12800661898255325487802127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34135098395347534634139005 12800661898255325487802127)
            ·
              refine ⟨19200992847382988231703191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12800661898255325487802127 19200992847382988231703191)
              ·
                refine ⟨28801489271074482347554787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19200992847382988231703191 28801489271074482347554787)
                ·
                  refine ⟨43202233906611723521332181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28801489271074482347554787 43202233906611723521332181)
                  ·
                    refine ⟨1012552357186212270031223, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 43202233906611723521332181 1012552357186212270031223)
                    ·
                      rfl

theorem cell22_2957908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 1, 1, 1, 7].length) (baseStart_2957908 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2957908 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2957908 prefixEnd_2957908 := by exact prefixLift 2957908
  have htrace : WordTrace (prefixWord ++ tailWord_2957908) baseStart_2957908 baseEnd_2957908 := by
    simpa [prefixWord, tailWord_2957908, baseEnd_2957908] using wordTrace_append hprefix tailTrace_2957908
  have hstable : (prefixWord ++ tailWord_2957908).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2957908).length < 2 ^ (prefixWord ++ tailWord_2957908).sum := by decide
  have hdescent : baseEnd_2957908 < baseStart_2957908 := by decide
  rcases family_descends (prefixWord ++ tailWord_2957908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2957918 : List Nat := [4, 4, 1, 2, 2, 1, 1, 1, 2, 4]
def baseStart_2957918 : Nat := 118140960795 + 2957918 * 2 ^ 59
def prefixEnd_2957918 : Nat := 4983230072969 + 3 ^ 40 * 2957918 * 2
def baseEnd_2957918 : Nat := 1012555780390575577281193

theorem tailTrace_2957918 : CollatzResearch.WordTrace tailWord_2957918 prefixEnd_2957918 1012555780390575577281193 := by
  unfold tailWord_2957918
  simp only [CollatzResearch.WordTrace]
  refine ⟨13485516562246966627587301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 71922754998650488680465605 13485516562246966627587301)
  ·
    refine ⟨2528534355421306242672619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13485516562246966627587301 2528534355421306242672619)
    ·
      refine ⟨3792801533131959364008929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2528534355421306242672619 3792801533131959364008929)
      ·
        refine ⟨2844601149848969523006697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3792801533131959364008929 2844601149848969523006697)
        ·
          refine ⟨2133450862386727142255023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2844601149848969523006697 2133450862386727142255023)
          ·
            refine ⟨3200176293580090713382535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2133450862386727142255023 3200176293580090713382535)
            ·
              refine ⟨4800264440370136070073803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3200176293580090713382535 4800264440370136070073803)
              ·
                refine ⟨7200396660555204105110705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4800264440370136070073803 7200396660555204105110705)
                ·
                  refine ⟨5400297495416403078833029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7200396660555204105110705 5400297495416403078833029)
                  ·
                    refine ⟨1012555780390575577281193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5400297495416403078833029 1012555780390575577281193)
                    ·
                      rfl

theorem cell22_2957918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 2, 1, 1, 1, 2, 4].length) (baseStart_2957918 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2957918 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2957918 prefixEnd_2957918 := by exact prefixLift 2957918
  have htrace : WordTrace (prefixWord ++ tailWord_2957918) baseStart_2957918 baseEnd_2957918 := by
    simpa [prefixWord, tailWord_2957918, baseEnd_2957918] using wordTrace_append hprefix tailTrace_2957918
  have hstable : (prefixWord ++ tailWord_2957918).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2957918).length < 2 ^ (prefixWord ++ tailWord_2957918).sum := by decide
  have hdescent : baseEnd_2957918 < baseStart_2957918 := by decide
  rcases family_descends (prefixWord ++ tailWord_2957918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2957923 : List Nat := [1, 1, 1, 5, 1, 2, 1, 3, 3, 4]
def baseStart_2957923 : Nat := 118140960795 + 2957923 * 2 ^ 59
def prefixEnd_2957923 : Nat := 4983230072969 + 3 ^ 40 * 2957923 * 2
def baseEnd_2957923 : Nat := 1012557491992757230906177

theorem tailTrace_2957923 : CollatzResearch.WordTrace tailWord_2957923 prefixEnd_2957923 1012557491992757230906177 := by
  unfold tailWord_2957923
  simp only [CollatzResearch.WordTrace]
  refine ⟨107884314862957618874630423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71922876575305079249753615 107884314862957618874630423)
  ·
    refine ⟨161826472294436428311945635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107884314862957618874630423 161826472294436428311945635)
    ·
      refine ⟨242739708441654642467918453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 161826472294436428311945635 242739708441654642467918453)
      ·
        refine ⟨22756847666405122731367355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 242739708441654642467918453 22756847666405122731367355)
        ·
          refine ⟨34135271499607684097051033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22756847666405122731367355 34135271499607684097051033)
          ·
            refine ⟨25601453624705763072788275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34135271499607684097051033 25601453624705763072788275)
            ·
              refine ⟨38402180437058644609182413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25601453624705763072788275 38402180437058644609182413)
              ·
                refine ⟨14400817663896991728443405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38402180437058644609182413 14400817663896991728443405)
                ·
                  refine ⟨5400306623961371898166277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14400817663896991728443405 5400306623961371898166277)
                  ·
                    refine ⟨1012557491992757230906177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5400306623961371898166277 1012557491992757230906177)
                    ·
                      rfl

theorem cell22_2957923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 1, 3, 3, 4].length) (baseStart_2957923 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2957923 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2957923 prefixEnd_2957923 := by exact prefixLift 2957923
  have htrace : WordTrace (prefixWord ++ tailWord_2957923) baseStart_2957923 baseEnd_2957923 := by
    simpa [prefixWord, tailWord_2957923, baseEnd_2957923] using wordTrace_append hprefix tailTrace_2957923
  have hstable : (prefixWord ++ tailWord_2957923).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2957923).length < 2 ^ (prefixWord ++ tailWord_2957923).sum := by decide
  have hdescent : baseEnd_2957923 < baseStart_2957923 := by decide
  rcases family_descends (prefixWord ++ tailWord_2957923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2957955 : List Nat := [1, 1, 1, 3, 3, 1, 4, 4, 4]
def baseStart_2957955 : Nat := 118140960795 + 2957955 * 2 ^ 59
def prefixEnd_2957955 : Nat := 4983230072969 + 3 ^ 40 * 2957955 * 2
def baseEnd_2957955 : Nat := 337522815415573271368693

theorem tailTrace_2957955 : CollatzResearch.WordTrace tailWord_2957955 prefixEnd_2957955 337522815415573271368693 := by
  unfold tailWord_2957955
  simp only [CollatzResearch.WordTrace]
  refine ⟨107885481998841688339795319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71923654665894458893196879 107885481998841688339795319)
  ·
    refine ⟨161828222998262532509692979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107885481998841688339795319 161828222998262532509692979)
    ·
      refine ⟨242742334497393798764539469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 161828222998262532509692979 242742334497393798764539469)
      ·
        refine ⟨91028375436522674536702301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 242742334497393798764539469 91028375436522674536702301)
        ·
          refine ⟨34135640788696002951263363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 91028375436522674536702301 34135640788696002951263363)
          ·
            refine ⟨51203461183044004426895045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34135640788696002951263363 51203461183044004426895045)
            ·
              refine ⟨9600648971820750830042821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 51203461183044004426895045 9600648971820750830042821)
              ·
                refine ⟨1800121682216390780633029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9600648971820750830042821 1800121682216390780633029)
                ·
                  refine ⟨337522815415573271368693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1800121682216390780633029 337522815415573271368693)
                  ·
                    rfl

theorem cell22_2957955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 4, 4, 4].length) (baseStart_2957955 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2957955 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2957955 prefixEnd_2957955 := by exact prefixLift 2957955
  have htrace : WordTrace (prefixWord ++ tailWord_2957955) baseStart_2957955 baseEnd_2957955 := by
    simpa [prefixWord, tailWord_2957955, baseEnd_2957955] using wordTrace_append hprefix tailTrace_2957955
  have hstable : (prefixWord ++ tailWord_2957955).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2957955).length < 2 ^ (prefixWord ++ tailWord_2957955).sum := by decide
  have hdescent : baseEnd_2957955 < baseStart_2957955 := by decide
  rcases family_descends (prefixWord ++ tailWord_2957955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2958006 : List Nat := [5, 1, 3, 1, 3, 1, 1, 1, 6]
def baseStart_2958006 : Nat := 118140960795 + 2958006 * 2 ^ 59
def prefixEnd_2958006 : Nat := 4983230072969 + 3 ^ 40 * 2958006 * 2
def baseEnd_2958006 : Nat := 337528634862990893693641

theorem tailTrace_2958006 : CollatzResearch.WordTrace tailWord_2958006 prefixEnd_2958006 337528634862990893693641 := by
  unfold tailWord_2958006
  simp only [CollatzResearch.WordTrace]
  refine ⟨6742958882603557753118867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 71924894747771282699934581 6742958882603557753118867)
  ·
    refine ⟨10114438323905336629678301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6742958882603557753118867 10114438323905336629678301)
    ·
      refine ⟨3792914371464501236129363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10114438323905336629678301 3792914371464501236129363)
      ·
        refine ⟨5689371557196751854194045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3792914371464501236129363 5689371557196751854194045)
        ·
          refine ⟨2133514333948781945322767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5689371557196751854194045 2133514333948781945322767)
          ·
            refine ⟨3200271500923172917984151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2133514333948781945322767 3200271500923172917984151)
            ·
              refine ⟨4800407251384759376976227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3200271500923172917984151 4800407251384759376976227)
              ·
                refine ⟨7200610877077139065464341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4800407251384759376976227 7200610877077139065464341)
                ·
                  refine ⟨337528634862990893693641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7200610877077139065464341 337528634862990893693641)
                  ·
                    rfl

theorem cell22_2958006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 3, 1, 1, 1, 6].length) (baseStart_2958006 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2958006 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2958006 prefixEnd_2958006 := by exact prefixLift 2958006
  have htrace : WordTrace (prefixWord ++ tailWord_2958006) baseStart_2958006 baseEnd_2958006 := by
    simpa [prefixWord, tailWord_2958006, baseEnd_2958006] using wordTrace_append hprefix tailTrace_2958006
  have hstable : (prefixWord ++ tailWord_2958006).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2958006).length < 2 ^ (prefixWord ++ tailWord_2958006).sum := by decide
  have hdescent : baseEnd_2958006 < baseStart_2958006 := by decide
  rcases family_descends (prefixWord ++ tailWord_2958006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2958062 : List Nat := [4, 1, 2, 1, 1, 4, 2, 2, 5]
def baseStart_2958062 : Nat := 118140960795 + 2958062 * 2 ^ 59
def prefixEnd_2958062 : Nat := 4983230072969 + 3 ^ 40 * 2958062 * 2
def baseEnd_2958062 : Nat := 337535024844469067226917

theorem tailTrace_2958062 : CollatzResearch.WordTrace tailWord_2958062 prefixEnd_2958062 337535024844469067226917 := by
  unfold tailWord_2958062
  simp only [CollatzResearch.WordTrace]
  refine ⟨13486173076181755701742555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 71926256406302697075960293 13486173076181755701742555)
  ·
    refine ⟨20229259614272633552613833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13486173076181755701742555 20229259614272633552613833)
    ·
      refine ⟨15171944710704475164460375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20229259614272633552613833 15171944710704475164460375)
      ·
        refine ⟨22757917066056712746690563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15171944710704475164460375 22757917066056712746690563)
        ·
          refine ⟨34136875599085069120035845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22757917066056712746690563 34136875599085069120035845)
          ·
            refine ⟨6400664174828450460006721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 34136875599085069120035845 6400664174828450460006721)
            ·
              refine ⟨4800498131121337845005041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6400664174828450460006721 4800498131121337845005041)
              ·
                refine ⟨3600373598341003383753781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4800498131121337845005041 3600373598341003383753781)
                ·
                  refine ⟨337535024844469067226917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3600373598341003383753781 337535024844469067226917)
                  ·
                    rfl

theorem cell22_2958062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 4, 2, 2, 5].length) (baseStart_2958062 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2958062 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2958062 prefixEnd_2958062 := by exact prefixLift 2958062
  have htrace : WordTrace (prefixWord ++ tailWord_2958062) baseStart_2958062 baseEnd_2958062 := by
    simpa [prefixWord, tailWord_2958062, baseEnd_2958062] using wordTrace_append hprefix tailTrace_2958062
  have hstable : (prefixWord ++ tailWord_2958062).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2958062).length < 2 ^ (prefixWord ++ tailWord_2958062).sum := by decide
  have hdescent : baseEnd_2958062 < baseStart_2958062 := by decide
  rcases family_descends (prefixWord ++ tailWord_2958062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2958066 : List Nat := [3, 2, 1, 3, 1, 2, 4, 2, 1, 3]
def baseStart_2958066 : Nat := 118140960795 + 2958066 * 2 ^ 59
def prefixEnd_2958066 : Nat := 4983230072969 + 3 ^ 40 * 2958066 * 2
def baseEnd_2958066 : Nat := 1012606443815152524580739

theorem tailTrace_2958066 : CollatzResearch.WordTrace tailWord_2958066 prefixEnd_2958066 1012606443815152524580739 := by
  unfold tailWord_2958066
  simp only [CollatzResearch.WordTrace]
  refine ⟨26972382625359888574271513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71926353667626369531390701 26972382625359888574271513)
  ·
    refine ⟨20229286969019916430703635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26972382625359888574271513 20229286969019916430703635)
    ·
      refine ⟨30343930453529874646055453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20229286969019916430703635 30343930453529874646055453)
      ·
        refine ⟨11378973920073702992270795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30343930453529874646055453 11378973920073702992270795)
        ·
          refine ⟨17068460880110554488406193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11378973920073702992270795 17068460880110554488406193)
          ·
            refine ⟨12801345660082915866304645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17068460880110554488406193 12801345660082915866304645)
            ·
              refine ⟨2400252311265546724932121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12801345660082915866304645 2400252311265546724932121)
              ·
                refine ⟨1800189233449160043699091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2400252311265546724932121 1800189233449160043699091)
                ·
                  refine ⟨2700283850173740065548637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1800189233449160043699091 2700283850173740065548637)
                  ·
                    refine ⟨1012606443815152524580739, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2700283850173740065548637 1012606443815152524580739)
                    ·
                      rfl

theorem cell22_2958066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 4, 2, 1, 3].length) (baseStart_2958066 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2958066 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2958066 prefixEnd_2958066 := by exact prefixLift 2958066
  have htrace : WordTrace (prefixWord ++ tailWord_2958066) baseStart_2958066 baseEnd_2958066 := by
    simpa [prefixWord, tailWord_2958066, baseEnd_2958066] using wordTrace_append hprefix tailTrace_2958066
  have hstable : (prefixWord ++ tailWord_2958066).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2958066).length < 2 ^ (prefixWord ++ tailWord_2958066).sum := by decide
  have hdescent : baseEnd_2958066 < baseStart_2958066 := by decide
  rcases family_descends (prefixWord ++ tailWord_2958066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2958073 : List Nat := [1, 2, 1, 3, 1, 1, 1, 2, 10]
def baseStart_2958073 : Nat := 118140960795 + 2958073 * 2 ^ 59
def prefixEnd_2958073 : Nat := 4983230072969 + 3 ^ 40 * 2958073 * 2
def baseEnd_2958073 : Nat := 337536280019402279885239

theorem tailTrace_2958073 : CollatzResearch.WordTrace tailWord_2958073 prefixEnd_2958073 337536280019402279885239 := by
  unfold tailWord_2958073
  simp only [CollatzResearch.WordTrace]
  refine ⟨107889785812414194492590873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71926523874942796328393915 107889785812414194492590873)
  ·
    refine ⟨80917339359310645869443155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107889785812414194492590873 80917339359310645869443155)
    ·
      refine ⟨121376009038965968804164733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80917339359310645869443155 121376009038965968804164733)
      ·
        refine ⟨45516003389612238301561775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 121376009038965968804164733 45516003389612238301561775)
        ·
          refine ⟨68274005084418357452342663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45516003389612238301561775 68274005084418357452342663)
          ·
            refine ⟨102411007626627536178513995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68274005084418357452342663 102411007626627536178513995)
            ·
              refine ⟨153616511439941304267770993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 102411007626627536178513995 153616511439941304267770993)
              ·
                refine ⟨115212383579955978200828245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 153616511439941304267770993 115212383579955978200828245)
                ·
                  refine ⟨337536280019402279885239, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 115212383579955978200828245 337536280019402279885239)
                  ·
                    rfl

theorem cell22_2958073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 2, 10].length) (baseStart_2958073 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2958073 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2958073 prefixEnd_2958073 := by exact prefixLift 2958073
  have htrace : WordTrace (prefixWord ++ tailWord_2958073) baseStart_2958073 baseEnd_2958073 := by
    simpa [prefixWord, tailWord_2958073, baseEnd_2958073] using wordTrace_append hprefix tailTrace_2958073
  have hstable : (prefixWord ++ tailWord_2958073).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2958073).length < 2 ^ (prefixWord ++ tailWord_2958073).sum := by decide
  have hdescent : baseEnd_2958073 < baseStart_2958073 := by decide
  rcases family_descends (prefixWord ++ tailWord_2958073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2958090 : List Nat := [3, 1, 2, 2, 1, 2, 3, 2, 6]
def baseStart_2958090 : Nat := 118140960795 + 2958090 * 2 ^ 59
def prefixEnd_2958090 : Nat := 4983230072969 + 3 ^ 40 * 2958090 * 2
def baseEnd_2958090 : Nat := 337538219835208153993555

theorem tailTrace_2958090 : CollatzResearch.WordTrace tailWord_2958090 prefixEnd_2958090 337538219835208153993555 := by
  unfold tailWord_2958090
  simp only [CollatzResearch.WordTrace]
  refine ⟨26972601463338151598989931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71926937235568404263973149 26972601463338151598989931)
  ·
    refine ⟨40458902195007227398484897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26972601463338151598989931 40458902195007227398484897)
    ·
      refine ⟨30344176646255420548863673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40458902195007227398484897 30344176646255420548863673)
      ·
        refine ⟨22758132484691565411647755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30344176646255420548863673 22758132484691565411647755)
        ·
          refine ⟨34137198727037348117471633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22758132484691565411647755 34137198727037348117471633)
          ·
            refine ⟨25602899045278011088103725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34137198727037348117471633 25602899045278011088103725)
            ·
              refine ⟨9601087141979254158038897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25602899045278011088103725 9601087141979254158038897)
              ·
                refine ⟨7200815356484440618529173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9601087141979254158038897 7200815356484440618529173)
                ·
                  refine ⟨337538219835208153993555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7200815356484440618529173 337538219835208153993555)
                  ·
                    rfl

theorem cell22_2958090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 3, 2, 6].length) (baseStart_2958090 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2958090 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2958090 prefixEnd_2958090 := by exact prefixLift 2958090
  have htrace : WordTrace (prefixWord ++ tailWord_2958090) baseStart_2958090 baseEnd_2958090 := by
    simpa [prefixWord, tailWord_2958090, baseEnd_2958090] using wordTrace_append hprefix tailTrace_2958090
  have hstable : (prefixWord ++ tailWord_2958090).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2958090).length < 2 ^ (prefixWord ++ tailWord_2958090).sum := by decide
  have hdescent : baseEnd_2958090 < baseStart_2958090 := by decide
  rcases family_descends (prefixWord ++ tailWord_2958090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2958184 : List Nat := [2, 1, 4, 2, 1, 2, 3, 1, 3, 3]
def baseStart_2958184 : Nat := 118140960795 + 2958184 * 2 ^ 59
def prefixEnd_2958184 : Nat := 4983230072969 + 3 ^ 40 * 2958184 * 2
def baseEnd_2958184 : Nat := 1012646837626639550130377

theorem tailTrace_2958184 : CollatzResearch.WordTrace tailWord_2958184 prefixEnd_2958184 1012646837626639550130377 := by
  unfold tailWord_2958184
  simp only [CollatzResearch.WordTrace]
  refine ⟨53946917157506030224940803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71929222876674706966587737 53946917157506030224940803)
  ·
    refine ⟨80920375736259045337411205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53946917157506030224940803 80920375736259045337411205)
    ·
      refine ⟨15172570450548571000764601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 80920375736259045337411205 15172570450548571000764601)
      ·
        refine ⟨11379427837911428250573451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15172570450548571000764601 11379427837911428250573451)
        ·
          refine ⟨17069141756867142375860177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11379427837911428250573451 17069141756867142375860177)
          ·
            refine ⟨12801856317650356781895133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17069141756867142375860177 12801856317650356781895133)
            ·
              refine ⟨4800696119118883793210675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12801856317650356781895133 4800696119118883793210675)
              ·
                refine ⟨7201044178678325689816013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4800696119118883793210675 7201044178678325689816013)
                ·
                  refine ⟨2700391567004372133681005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7201044178678325689816013 2700391567004372133681005)
                  ·
                    refine ⟨1012646837626639550130377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2700391567004372133681005 1012646837626639550130377)
                    ·
                      rfl

theorem cell22_2958184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 3, 1, 3, 3].length) (baseStart_2958184 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2958184 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2958184 prefixEnd_2958184 := by exact prefixLift 2958184
  have htrace : WordTrace (prefixWord ++ tailWord_2958184) baseStart_2958184 baseEnd_2958184 := by
    simpa [prefixWord, tailWord_2958184, baseEnd_2958184] using wordTrace_append hprefix tailTrace_2958184
  have hstable : (prefixWord ++ tailWord_2958184).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2958184).length < 2 ^ (prefixWord ++ tailWord_2958184).sum := by decide
  have hdescent : baseEnd_2958184 < baseStart_2958184 := by decide
  rcases family_descends (prefixWord ++ tailWord_2958184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2958190 : List Nat := [4, 1, 2, 3, 3, 1, 2, 1, 2, 3]
def baseStart_2958190 : Nat := 118140960795 + 2958190 * 2 ^ 59
def prefixEnd_2958190 : Nat := 4983230072969 + 3 ^ 40 * 2958190 * 2
def baseEnd_2958190 : Nat := 1012648891549257534480359

theorem tailTrace_2958190 : CollatzResearch.WordTrace tailWord_2958190 prefixEnd_2958190 1012648891549257534480359 := by
  unfold tailWord_2958190
  simp only [CollatzResearch.WordTrace]
  refine ⟨13486756644123790434325003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 71929368768660215649733349 13486756644123790434325003)
  ·
    refine ⟨20230134966185685651487505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13486756644123790434325003 20230134966185685651487505)
    ·
      refine ⟨15172601224639264238615629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20230134966185685651487505 15172601224639264238615629)
      ·
        refine ⟨5689725459239724089480861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15172601224639264238615629 5689725459239724089480861)
        ·
          refine ⟨2133647047214896533555323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5689725459239724089480861 2133647047214896533555323)
          ·
            refine ⟨3200470570822344800332985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2133647047214896533555323 3200470570822344800332985)
            ·
              refine ⟨2400352928116758600249739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3200470570822344800332985 2400352928116758600249739)
              ·
                refine ⟨3600529392175137900374609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2400352928116758600249739 3600529392175137900374609)
                ·
                  refine ⟨2700397044131353425280957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3600529392175137900374609 2700397044131353425280957)
                  ·
                    refine ⟨1012648891549257534480359, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2700397044131353425280957 1012648891549257534480359)
                    ·
                      rfl

theorem cell22_2958190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 3, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 3, 1, 2, 1, 2, 3].length) (baseStart_2958190 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2958190 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2958190 prefixEnd_2958190 := by exact prefixLift 2958190
  have htrace : WordTrace (prefixWord ++ tailWord_2958190) baseStart_2958190 baseEnd_2958190 := by
    simpa [prefixWord, tailWord_2958190, baseEnd_2958190] using wordTrace_append hprefix tailTrace_2958190
  have hstable : (prefixWord ++ tailWord_2958190).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2958190).length < 2 ^ (prefixWord ++ tailWord_2958190).sum := by decide
  have hdescent : baseEnd_2958190 < baseStart_2958190 := by decide
  rcases family_descends (prefixWord ++ tailWord_2958190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2958195 : List Nat := [1, 1, 1, 2, 2, 1, 4, 3, 2, 5]
def baseStart_2958195 : Nat := 118140960795 + 2958195 * 2 ^ 59
def prefixEnd_2958195 : Nat := 4983230072969 + 3 ^ 40 * 2958195 * 2
def baseEnd_2958195 : Nat := 1012650603151439188105343

theorem tailTrace_2958195 : CollatzResearch.WordTrace tailWord_2958195 prefixEnd_2958195 1012650603151439188105343 := by
  unfold tailWord_2958195
  simp only [CollatzResearch.WordTrace]
  refine ⟨107894235517972209328532039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71929490345314806219021359 107894235517972209328532039)
  ·
    refine ⟨161841353276958313992798059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107894235517972209328532039 161841353276958313992798059)
    ·
      refine ⟨242762029915437470989197089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 161841353276958313992798059 242762029915437470989197089)
      ·
        refine ⟨182071522436578103241897817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 242762029915437470989197089 182071522436578103241897817)
        ·
          refine ⟨136553641827433577431423363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 182071522436578103241897817 136553641827433577431423363)
          ·
            refine ⟨204830462741150366147135045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 136553641827433577431423363 204830462741150366147135045)
            ·
              refine ⟨38405711763965693652587821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 204830462741150366147135045 38405711763965693652587821)
              ·
                refine ⟨14402141911487135119720433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38405711763965693652587821 14402141911487135119720433)
                ·
                  refine ⟨10801606433615351339790325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14402141911487135119720433 10801606433615351339790325)
                  ·
                    refine ⟨1012650603151439188105343, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10801606433615351339790325 1012650603151439188105343)
                    ·
                      rfl

theorem cell22_2958195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 4, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 4, 3, 2, 5].length) (baseStart_2958195 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2958195 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2958195 prefixEnd_2958195 := by exact prefixLift 2958195
  have htrace : WordTrace (prefixWord ++ tailWord_2958195) baseStart_2958195 baseEnd_2958195 := by
    simpa [prefixWord, tailWord_2958195, baseEnd_2958195] using wordTrace_append hprefix tailTrace_2958195
  have hstable : (prefixWord ++ tailWord_2958195).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2958195).length < 2 ^ (prefixWord ++ tailWord_2958195).sum := by decide
  have hdescent : baseEnd_2958195 < baseStart_2958195 := by decide
  rcases family_descends (prefixWord ++ tailWord_2958195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2958272 : List Nat := [2, 1, 1, 2, 3, 4, 1, 1, 1, 6]
def baseStart_2958272 : Nat := 118140960795 + 2958272 * 2 ^ 59
def prefixEnd_2958272 : Nat := 4983230072969 + 3 ^ 40 * 2958272 * 2
def baseEnd_2958272 : Nat := 1012676961825036653930107

theorem tailTrace_2958272 : CollatzResearch.WordTrace tailWord_2958272 prefixEnd_2958272 1012676961825036653930107 := by
  unfold tailWord_2958272
  simp only [CollatzResearch.WordTrace]
  refine ⟨53948521969346625739542535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71931362625795500986056713 53948521969346625739542535)
  ·
    refine ⟨80922782954019938609313803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53948521969346625739542535 80922782954019938609313803)
    ·
      refine ⟨121384174431029907913970705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80922782954019938609313803 121384174431029907913970705)
      ·
        refine ⟨91038130823272430935478029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 121384174431029907913970705 91038130823272430935478029)
        ·
          refine ⟨34139299058727161600804261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 91038130823272430935478029 34139299058727161600804261)
          ·
            refine ⟨6401118573511342800150799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 34139299058727161600804261 6401118573511342800150799)
            ·
              refine ⟨9601677860267014200226199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6401118573511342800150799 9601677860267014200226199)
              ·
                refine ⟨14402516790400521300339299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9601677860267014200226199 14402516790400521300339299)
                ·
                  refine ⟨21603775185600781950508949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14402516790400521300339299 21603775185600781950508949)
                  ·
                    refine ⟨1012676961825036653930107, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21603775185600781950508949 1012676961825036653930107)
                    ·
                      rfl

theorem cell22_2958272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 4, 1, 1, 1, 6].length) (baseStart_2958272 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2958272 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2958272 prefixEnd_2958272 := by exact prefixLift 2958272
  have htrace : WordTrace (prefixWord ++ tailWord_2958272) baseStart_2958272 baseEnd_2958272 := by
    simpa [prefixWord, tailWord_2958272, baseEnd_2958272] using wordTrace_append hprefix tailTrace_2958272
  have hstable : (prefixWord ++ tailWord_2958272).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2958272).length < 2 ^ (prefixWord ++ tailWord_2958272).sum := by decide
  have hdescent : baseEnd_2958272 < baseStart_2958272 := by decide
  rcases family_descends (prefixWord ++ tailWord_2958272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2958319 : List Nat := [1, 1, 2, 1, 4, 3, 2, 2, 3, 3]
def baseStart_2958319 : Nat := 118140960795 + 2958319 * 2 ^ 59
def prefixEnd_2958319 : Nat := 4983230072969 + 3 ^ 40 * 2958319 * 2
def baseEnd_2958319 : Nat := 1012693050885544198004963

theorem tailTrace_2958319 : CollatzResearch.WordTrace tailWord_2958319 prefixEnd_2958319 1012693050885544198004963 := by
  unfold tailWord_2958319
  simp only [CollatzResearch.WordTrace]
  refine ⟨107898758169522978506046011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71932505446348652337364007 107898758169522978506046011)
  ·
    refine ⟨161848137254284467759069017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107898758169522978506046011 161848137254284467759069017)
    ·
      refine ⟨121386102940713350819301763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 161848137254284467759069017 121386102940713350819301763)
      ·
        refine ⟨182079154411070026228952645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121386102940713350819301763 182079154411070026228952645)
        ·
          refine ⟨34139841452075629917928621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 182079154411070026228952645 34139841452075629917928621)
          ·
            refine ⟨12802440544528361219223233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34139841452075629917928621 12802440544528361219223233)
            ·
              refine ⟨9601830408396270914417425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12802440544528361219223233 9601830408396270914417425)
              ·
                refine ⟨7201372806297203185813069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9601830408396270914417425 7201372806297203185813069)
                ·
                  refine ⟨2700514802361451194679901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7201372806297203185813069 2700514802361451194679901)
                  ·
                    refine ⟨1012693050885544198004963, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2700514802361451194679901 1012693050885544198004963)
                    ·
                      rfl

theorem cell22_2958319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 2, 2, 3, 3].length) (baseStart_2958319 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2958319 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2958319 prefixEnd_2958319 := by exact prefixLift 2958319
  have htrace : WordTrace (prefixWord ++ tailWord_2958319) baseStart_2958319 baseEnd_2958319 := by
    simpa [prefixWord, tailWord_2958319, baseEnd_2958319] using wordTrace_append hprefix tailTrace_2958319
  have hstable : (prefixWord ++ tailWord_2958319).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2958319).length < 2 ^ (prefixWord ++ tailWord_2958319).sum := by decide
  have hdescent : baseEnd_2958319 < baseStart_2958319 := by decide
  rcases family_descends (prefixWord ++ tailWord_2958319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2958332 : List Nat := [2, 2, 2, 1, 2, 3, 1, 2, 7]
def baseStart_2958332 : Nat := 118140960795 + 2958332 * 2 ^ 59
def prefixEnd_2958332 : Nat := 4983230072969 + 3 ^ 40 * 2958332 * 2
def baseEnd_2958332 : Nat := 337565833683738832476641

theorem tailTrace_2958332 : CollatzResearch.WordTrace tailWord_2958332 prefixEnd_2958332 337565833683738832476641 := by
  unfold tailWord_2958332
  simp only [CollatzResearch.WordTrace]
  refine ⟨53949616159237940863134625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71932821545650587817512833 53949616159237940863134625)
  ·
    refine ⟨40462212119428455647350969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53949616159237940863134625 40462212119428455647350969)
    ·
      refine ⟨30346659089571341735513227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40462212119428455647350969 30346659089571341735513227)
      ·
        refine ⟨45519988634357012603269841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30346659089571341735513227 45519988634357012603269841)
        ·
          refine ⟨34139991475767759452452381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45519988634357012603269841 34139991475767759452452381)
          ·
            refine ⟨12802496803412909794669643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34139991475767759452452381 12802496803412909794669643)
            ·
              refine ⟨19203745205119364692004465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12802496803412909794669643 19203745205119364692004465)
              ·
                refine ⟨14402808903839523519003349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19203745205119364692004465 14402808903839523519003349)
                ·
                  refine ⟨337565833683738832476641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14402808903839523519003349 337565833683738832476641)
                  ·
                    rfl

theorem cell22_2958332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 1, 2, 7].length) (baseStart_2958332 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2958332 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2958332 prefixEnd_2958332 := by exact prefixLift 2958332
  have htrace : WordTrace (prefixWord ++ tailWord_2958332) baseStart_2958332 baseEnd_2958332 := by
    simpa [prefixWord, tailWord_2958332, baseEnd_2958332] using wordTrace_append hprefix tailTrace_2958332
  have hstable : (prefixWord ++ tailWord_2958332).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2958332).length < 2 ^ (prefixWord ++ tailWord_2958332).sum := by decide
  have hdescent : baseEnd_2958332 < baseStart_2958332 := by decide
  rcases family_descends (prefixWord ++ tailWord_2958332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2958338 : List Nat := [3, 4, 1, 3, 2, 1, 8]
def baseStart_2958338 : Nat := 118140960795 + 2958338 * 2 ^ 59
def prefixEnd_2958338 : Nat := 4983230072969 + 3 ^ 40 * 2958338 * 2
def baseEnd_2958338 : Nat := 37507390924956832658515

theorem tailTrace_2958338 : CollatzResearch.WordTrace tailWord_2958338 prefixEnd_2958338 37507390924956832658515 := by
  unfold tailWord_2958338
  simp only [CollatzResearch.WordTrace]
  refine ⟨26974862789113536187746917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71932967437636096500658445 26974862789113536187746917)
  ·
    refine ⟨5057786772958788035202547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 26974862789113536187746917 5057786772958788035202547)
    ·
      refine ⟨7586680159438182052803821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5057786772958788035202547 7586680159438182052803821)
      ·
        refine ⟨2845005059789318269801433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7586680159438182052803821 2845005059789318269801433)
        ·
          refine ⟨2133753794841988702351075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2845005059789318269801433 2133753794841988702351075)
          ·
            refine ⟨3200630692262983053526613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2133753794841988702351075 3200630692262983053526613)
            ·
              refine ⟨37507390924956832658515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3200630692262983053526613 37507390924956832658515)
              ·
                rfl

theorem cell22_2958338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 2, 1, 8].length) (baseStart_2958338 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2958338 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2958338 prefixEnd_2958338 := by exact prefixLift 2958338
  have htrace : WordTrace (prefixWord ++ tailWord_2958338) baseStart_2958338 baseEnd_2958338 := by
    simpa [prefixWord, tailWord_2958338, baseEnd_2958338] using wordTrace_append hprefix tailTrace_2958338
  have hstable : (prefixWord ++ tailWord_2958338).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2958338).length < 2 ^ (prefixWord ++ tailWord_2958338).sum := by decide
  have hdescent : baseEnd_2958338 < baseStart_2958338 := by decide
  rcases family_descends (prefixWord ++ tailWord_2958338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2958441 : List Nat := [1, 2, 1, 1, 1, 8, 1, 1, 2, 4]
def baseStart_2958441 : Nat := 118140960795 + 2958441 * 2 ^ 59
def prefixEnd_2958441 : Nat := 4983230072969 + 3 ^ 40 * 2958441 * 2
def baseEnd_2958441 : Nat := 1012734813978776546454589

theorem tailTrace_2958441 : CollatzResearch.WordTrace tailWord_2958441 prefixEnd_2958441 1012734813978776546454589 := by
  unfold tailWord_2958441
  simp only [CollatzResearch.WordTrace]
  refine ⟨107903207875080993341987177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71935471916720662227991451 107903207875080993341987177)
  ·
    refine ⟨80927405906310745006490383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107903207875080993341987177 80927405906310745006490383)
    ·
      refine ⟨121391108859466117509735575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80927405906310745006490383 121391108859466117509735575)
      ·
        refine ⟨182086663289199176264603363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121391108859466117509735575 182086663289199176264603363)
        ·
          refine ⟨273129994933798764396905045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 182086663289199176264603363 273129994933798764396905045)
          ·
            refine ⟨3200742128130454270276231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 273129994933798764396905045 3200742128130454270276231)
            ·
              refine ⟨4801113192195681405414347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3200742128130454270276231 4801113192195681405414347)
              ·
                refine ⟨7201669788293522108121521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4801113192195681405414347 7201669788293522108121521)
                ·
                  refine ⟨5401252341220141581091141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7201669788293522108121521 5401252341220141581091141)
                  ·
                    refine ⟨1012734813978776546454589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5401252341220141581091141 1012734813978776546454589)
                    ·
                      rfl

theorem cell22_2958441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 8, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 8, 1, 1, 2, 4].length) (baseStart_2958441 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2958441 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2958441 prefixEnd_2958441 := by exact prefixLift 2958441
  have htrace : WordTrace (prefixWord ++ tailWord_2958441) baseStart_2958441 baseEnd_2958441 := by
    simpa [prefixWord, tailWord_2958441, baseEnd_2958441] using wordTrace_append hprefix tailTrace_2958441
  have hstable : (prefixWord ++ tailWord_2958441).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2958441).length < 2 ^ (prefixWord ++ tailWord_2958441).sum := by decide
  have hdescent : baseEnd_2958441 < baseStart_2958441 := by decide
  rcases family_descends (prefixWord ++ tailWord_2958441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2958559 : List Nat := [1, 1, 2, 3, 2, 1, 2, 3, 1, 6]
def baseStart_2958559 : Nat := 118140960795 + 2958559 * 2 ^ 59
def prefixEnd_2958559 : Nat := 4983230072969 + 3 ^ 40 * 2958559 * 2
def baseEnd_2958559 : Nat := 1012775207790263572004227

theorem tailTrace_2958559 : CollatzResearch.WordTrace tailWord_2958559 prefixEnd_2958559 1012775207790263572004227 := by
  unfold tailWord_2958559
  simp only [CollatzResearch.WordTrace]
  refine ⟨107907511688653499494782731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71938341125768999663188487 107907511688653499494782731)
  ·
    refine ⟨161861267532980249242174097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107907511688653499494782731 161861267532980249242174097)
    ·
      refine ⟨121395950649735186931630573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 161861267532980249242174097 121395950649735186931630573)
      ·
        refine ⟨45523481493650695099361465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 121395950649735186931630573 45523481493650695099361465)
        ·
          refine ⟨34142611120238021324521099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45523481493650695099361465 34142611120238021324521099)
          ·
            refine ⟨51213916680357031986781649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34142611120238021324521099 51213916680357031986781649)
            ·
              refine ⟨38410437510267773990086237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51213916680357031986781649 38410437510267773990086237)
              ·
                refine ⟨14403914066350415246282339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38410437510267773990086237 14403914066350415246282339)
                ·
                  refine ⟨21605871099525622869423509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14403914066350415246282339 21605871099525622869423509)
                  ·
                    refine ⟨1012775207790263572004227, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21605871099525622869423509 1012775207790263572004227)
                    ·
                      rfl

theorem cell22_2958559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 2, 3, 1, 6].length) (baseStart_2958559 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2958559 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2958559 prefixEnd_2958559 := by exact prefixLift 2958559
  have htrace : WordTrace (prefixWord ++ tailWord_2958559) baseStart_2958559 baseEnd_2958559 := by
    simpa [prefixWord, tailWord_2958559, baseEnd_2958559] using wordTrace_append hprefix tailTrace_2958559
  have hstable : (prefixWord ++ tailWord_2958559).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2958559).length < 2 ^ (prefixWord ++ tailWord_2958559).sum := by decide
  have hdescent : baseEnd_2958559 < baseStart_2958559 := by decide
  rcases family_descends (prefixWord ++ tailWord_2958559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2958561 : List Nat := [1, 2, 3, 1, 3, 3, 1, 2, 1, 5]
def baseStart_2958561 : Nat := 118140960795 + 2958561 * 2 ^ 59
def prefixEnd_2958561 : Nat := 4983230072969 + 3 ^ 40 * 2958561 * 2
def baseEnd_2958561 : Nat := 1012775892431136233454221

theorem tailTrace_2958561 : CollatzResearch.WordTrace tailWord_2958561 prefixEnd_2958561 1012775892431136233454221 := by
  unfold tailWord_2958561
  simp only [CollatzResearch.WordTrace]
  refine ⟨107907584634646253836355537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71938389756430835890903691 107907584634646253836355537)
  ·
    refine ⟨80930688475984690377266653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107907584634646253836355537 80930688475984690377266653)
    ·
      refine ⟨30349008178494258891474995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 80930688475984690377266653 30349008178494258891474995)
      ·
        refine ⟨45523512267741388337212493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30349008178494258891474995 45523512267741388337212493)
        ·
          refine ⟨17071317100403020626454685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45523512267741388337212493 17071317100403020626454685)
          ·
            refine ⟨6401743912651132734920507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17071317100403020626454685 6401743912651132734920507)
            ·
              refine ⟨9602615868976699102380761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6401743912651132734920507 9602615868976699102380761)
              ·
                refine ⟨7201961901732524326785571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9602615868976699102380761 7201961901732524326785571)
                ·
                  refine ⟨10802942852598786490178357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7201961901732524326785571 10802942852598786490178357)
                  ·
                    refine ⟨1012775892431136233454221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10802942852598786490178357 1012775892431136233454221)
                    ·
                      rfl

theorem cell22_2958561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 3, 1, 2, 1, 5].length) (baseStart_2958561 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2958561 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2958561 prefixEnd_2958561 := by exact prefixLift 2958561
  have htrace : WordTrace (prefixWord ++ tailWord_2958561) baseStart_2958561 baseEnd_2958561 := by
    simpa [prefixWord, tailWord_2958561, baseEnd_2958561] using wordTrace_append hprefix tailTrace_2958561
  have hstable : (prefixWord ++ tailWord_2958561).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2958561).length < 2 ^ (prefixWord ++ tailWord_2958561).sum := by decide
  have hdescent : baseEnd_2958561 < baseStart_2958561 := by decide
  rcases family_descends (prefixWord ++ tailWord_2958561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2958565 : List Nat := [1, 3, 1, 4, 3, 1, 3, 1, 1, 4]
def baseStart_2958565 : Nat := 118140960795 + 2958565 * 2 ^ 59
def prefixEnd_2958565 : Nat := 4983230072969 + 3 ^ 40 * 2958565 * 2
def baseEnd_2958565 : Nat := 1012777261712881556354209

theorem tailTrace_2958565 : CollatzResearch.WordTrace tailWord_2958565 prefixEnd_2958565 1012777261712881556354209 := by
  unfold tailWord_2958565
  simp only [CollatzResearch.WordTrace]
  refine ⟨107907730526631762519501149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71938487017754508346334099 107907730526631762519501149)
  ·
    refine ⟨40465398947486910944812931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 107907730526631762519501149 40465398947486910944812931)
    ·
      refine ⟨60698098421230366417219397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40465398947486910944812931 60698098421230366417219397)
      ·
        refine ⟨11380893453980693703228637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 60698098421230366417219397 11380893453980693703228637)
        ·
          refine ⟨4267835045242760138710739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11380893453980693703228637 4267835045242760138710739)
          ·
            refine ⟨6401752567864140208066109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4267835045242760138710739 6401752567864140208066109)
            ·
              refine ⟨2400657212949052578024791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6401752567864140208066109 2400657212949052578024791)
              ·
                refine ⟨3600985819423578867037187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2400657212949052578024791 3600985819423578867037187)
                ·
                  refine ⟨5401478729135368300555781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3600985819423578867037187 5401478729135368300555781)
                  ·
                    refine ⟨1012777261712881556354209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5401478729135368300555781 1012777261712881556354209)
                    ·
                      rfl

theorem cell22_2958565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 1, 3, 1, 1, 4].length) (baseStart_2958565 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2958565 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2958565 prefixEnd_2958565 := by exact prefixLift 2958565
  have htrace : WordTrace (prefixWord ++ tailWord_2958565) baseStart_2958565 baseEnd_2958565 := by
    simpa [prefixWord, tailWord_2958565, baseEnd_2958565] using wordTrace_append hprefix tailTrace_2958565
  have hstable : (prefixWord ++ tailWord_2958565).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2958565).length < 2 ^ (prefixWord ++ tailWord_2958565).sum := by decide
  have hdescent : baseEnd_2958565 < baseStart_2958565 := by decide
  rcases family_descends (prefixWord ++ tailWord_2958565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2958589 : List Nat := [1, 4, 1, 1, 1, 1, 1, 1, 4, 7]
def baseStart_2958589 : Nat := 118140960795 + 2958589 * 2 ^ 59
def prefixEnd_2958589 : Nat := 4983230072969 + 3 ^ 40 * 2958589 * 2
def baseEnd_2958589 : Nat := 1012785477403353493754135

theorem tailTrace_2958589 : CollatzResearch.WordTrace tailWord_2958589 prefixEnd_2958589 1012785477403353493754135 := by
  unfold tailWord_2958589
  simp only [CollatzResearch.WordTrace]
  refine ⟨107908605878544814618374821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71939070585696543078916547 107908605878544814618374821)
  ·
    refine ⟨20232863602227152740945279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 107908605878544814618374821 20232863602227152740945279)
    ·
      refine ⟨30349295403340729111417919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20232863602227152740945279 30349295403340729111417919)
      ·
        refine ⟨45523943105011093667126879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30349295403340729111417919 45523943105011093667126879)
        ·
          refine ⟨68285914657516640500690319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45523943105011093667126879 68285914657516640500690319)
          ·
            refine ⟨102428871986274960751035479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68285914657516640500690319 102428871986274960751035479)
            ·
              refine ⟨153643307979412441126553219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 102428871986274960751035479 153643307979412441126553219)
              ·
                refine ⟨230464961969118661689829829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 153643307979412441126553219 230464961969118661689829829)
                ·
                  refine ⟨43212180369209749066843093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 230464961969118661689829829 43212180369209749066843093)
                  ·
                    refine ⟨1012785477403353493754135, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 43212180369209749066843093 1012785477403353493754135)
                    ·
                      rfl

theorem cell22_2958589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 1, 4, 7].length) (baseStart_2958589 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2958589 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2958589 prefixEnd_2958589 := by exact prefixLift 2958589
  have htrace : WordTrace (prefixWord ++ tailWord_2958589) baseStart_2958589 baseEnd_2958589 := by
    simpa [prefixWord, tailWord_2958589, baseEnd_2958589] using wordTrace_append hprefix tailTrace_2958589
  have hstable : (prefixWord ++ tailWord_2958589).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2958589).length < 2 ^ (prefixWord ++ tailWord_2958589).sum := by decide
  have hdescent : baseEnd_2958589 < baseStart_2958589 := by decide
  rcases family_descends (prefixWord ++ tailWord_2958589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2958591 : List Nat := [1, 1, 2, 2, 1, 7, 1, 7]
def baseStart_2958591 : Nat := 118140960795 + 2958591 * 2 ^ 59
def prefixEnd_2958591 : Nat := 4983230072969 + 3 ^ 40 * 2958591 * 2
def baseEnd_2958591 : Nat := 112531795782691795022681

theorem tailTrace_2958591 : CollatzResearch.WordTrace tailWord_2958591 prefixEnd_2958591 112531795782691795022681 := by
  unfold tailWord_2958591
  simp only [CollatzResearch.WordTrace]
  refine ⟨107908678824537568959947627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71939119216358379306631751 107908678824537568959947627)
  ·
    refine ⟨161863018236806353439921441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107908678824537568959947627 161863018236806353439921441)
    ·
      refine ⟨121397263677604765079941081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 161863018236806353439921441 121397263677604765079941081)
      ·
        refine ⟨91047947758203573809955811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 121397263677604765079941081 91047947758203573809955811)
        ·
          refine ⟨136571921637305360714933717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91047947758203573809955811 136571921637305360714933717)
          ·
            refine ⟨3200904413374344391756259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 136571921637305360714933717 3200904413374344391756259)
            ·
              refine ⟨4801356620061516587634389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3200904413374344391756259 4801356620061516587634389)
              ·
                refine ⟨112531795782691795022681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4801356620061516587634389 112531795782691795022681)
                ·
                  rfl

theorem cell22_2958591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 7, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 7, 1, 7].length) (baseStart_2958591 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2958591 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2958591 prefixEnd_2958591 := by exact prefixLift 2958591
  have htrace : WordTrace (prefixWord ++ tailWord_2958591) baseStart_2958591 baseEnd_2958591 := by
    simpa [prefixWord, tailWord_2958591, baseEnd_2958591] using wordTrace_append hprefix tailTrace_2958591
  have hstable : (prefixWord ++ tailWord_2958591).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2958591).length < 2 ^ (prefixWord ++ tailWord_2958591).sum := by decide
  have hdescent : baseEnd_2958591 < baseStart_2958591 := by decide
  rcases family_descends (prefixWord ++ tailWord_2958591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2958610 : List Nat := [3, 2, 4, 2, 1, 1, 1, 1, 1, 6]
def baseStart_2958610 : Nat := 118140960795 + 2958610 * 2 ^ 59
def prefixEnd_2958610 : Nat := 4983230072969 + 3 ^ 40 * 2958610 * 2
def baseEnd_2958610 : Nat := 1012792666132516438979071

theorem tailTrace_2958610 : CollatzResearch.WordTrace tailWord_2958610 prefixEnd_2958610 1012792666132516438979071 := by
  unfold tailWord_2958610
  simp only [CollatzResearch.WordTrace]
  refine ⟨26977342952867183801222321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71939581207645823469926189 26977342952867183801222321)
  ·
    refine ⟨20233007214650387850916741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26977342952867183801222321 20233007214650387850916741)
    ·
      refine ⟨3793688852746947722046889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 20233007214650387850916741 3793688852746947722046889)
      ·
        refine ⟨2845266639560210791535167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3793688852746947722046889 2845266639560210791535167)
        ·
          refine ⟨4267899959340316187302751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2845266639560210791535167 4267899959340316187302751)
          ·
            refine ⟨6401849939010474280954127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4267899959340316187302751 6401849939010474280954127)
            ·
              refine ⟨9602774908515711421431191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6401849939010474280954127 9602774908515711421431191)
              ·
                refine ⟨14404162362773567132146787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9602774908515711421431191 14404162362773567132146787)
                ·
                  refine ⟨21606243544160350698220181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14404162362773567132146787 21606243544160350698220181)
                  ·
                    refine ⟨1012792666132516438979071, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21606243544160350698220181 1012792666132516438979071)
                    ·
                      rfl

theorem cell22_2958610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 1, 1, 1, 1, 6].length) (baseStart_2958610 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2958610 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2958610 prefixEnd_2958610 := by exact prefixLift 2958610
  have htrace : WordTrace (prefixWord ++ tailWord_2958610) baseStart_2958610 baseEnd_2958610 := by
    simpa [prefixWord, tailWord_2958610, baseEnd_2958610] using wordTrace_append hprefix tailTrace_2958610
  have hstable : (prefixWord ++ tailWord_2958610).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2958610).length < 2 ^ (prefixWord ++ tailWord_2958610).sum := by decide
  have hdescent : baseEnd_2958610 < baseStart_2958610 := by decide
  rcases family_descends (prefixWord ++ tailWord_2958610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2958619 : List Nat := [1, 1, 1, 1, 1, 1, 5, 4, 7]
def baseStart_2958619 : Nat := 118140960795 + 2958619 * 2 ^ 59
def prefixEnd_2958619 : Nat := 4983230072969 + 3 ^ 40 * 2958619 * 2
def baseEnd_2958619 : Nat := 337598582338814471834681

theorem tailTrace_2958619 : CollatzResearch.WordTrace tailWord_2958619 prefixEnd_2958619 337598582338814471834681 := by
  unfold tailWord_2958619
  simp only [CollatzResearch.WordTrace]
  refine ⟨107909700068436129741966911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71939800045624086494644607 107909700068436129741966911)
  ·
    refine ⟨161864550102654194612950367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107909700068436129741966911 161864550102654194612950367)
    ·
      refine ⟨242796825153981291919425551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 161864550102654194612950367 242796825153981291919425551)
      ·
        refine ⟨364195237730971937879138327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 242796825153981291919425551 364195237730971937879138327)
        ·
          refine ⟨546292856596457906818707491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 364195237730971937879138327 546292856596457906818707491)
          ·
            refine ⟨819439284894686860228061237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 546292856596457906818707491 819439284894686860228061237)
            ·
              refine ⟨76822432958876893146380741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 819439284894686860228061237 76822432958876893146380741)
              ·
                refine ⟨14404206179789417464946389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 76822432958876893146380741 14404206179789417464946389)
                ·
                  refine ⟨337598582338814471834681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14404206179789417464946389 337598582338814471834681)
                  ·
                    rfl

theorem cell22_2958619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 4, 7].length) (baseStart_2958619 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2958619 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2958619 prefixEnd_2958619 := by exact prefixLift 2958619
  have htrace : WordTrace (prefixWord ++ tailWord_2958619) baseStart_2958619 baseEnd_2958619 := by
    simpa [prefixWord, tailWord_2958619, baseEnd_2958619] using wordTrace_append hprefix tailTrace_2958619
  have hstable : (prefixWord ++ tailWord_2958619).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2958619).length < 2 ^ (prefixWord ++ tailWord_2958619).sum := by decide
  have hdescent : baseEnd_2958619 < baseStart_2958619 := by decide
  rcases family_descends (prefixWord ++ tailWord_2958619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2958666 : List Nat := [3, 1, 2, 1, 1, 1, 1, 5, 3, 4]
def baseStart_2958666 : Nat := 118140960795 + 2958666 * 2 ^ 59
def prefixEnd_2958666 : Nat := 4983230072969 + 3 ^ 40 * 2958666 * 2
def baseEnd_2958666 : Nat := 1012811836076950959578899

theorem tailTrace_2958666 : CollatzResearch.WordTrace tailWord_2958666 prefixEnd_2958666 1012811836076950959578899 := by
  unfold tailWord_2958666
  simp only [CollatzResearch.WordTrace]
  refine ⟨26977853574816464192231963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71940942866177237845951901 26977853574816464192231963)
  ·
    refine ⟨40466780362224696288347945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26977853574816464192231963 40466780362224696288347945)
    ·
      refine ⟨30350085271668522216260959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40466780362224696288347945 30350085271668522216260959)
      ·
        refine ⟨45525127907502783324391439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30350085271668522216260959 45525127907502783324391439)
        ·
          refine ⟨68287691861254174986587159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45525127907502783324391439 68287691861254174986587159)
          ·
            refine ⟨102431537791881262479880739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68287691861254174986587159 102431537791881262479880739)
            ·
              refine ⟨153647306687821893719821109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 102431537791881262479880739 153647306687821893719821109)
              ·
                refine ⟨14404435001983302536233229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 153647306687821893719821109 14404435001983302536233229)
                ·
                  refine ⟨5401663125743738451087461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14404435001983302536233229 5401663125743738451087461)
                  ·
                    refine ⟨1012811836076950959578899, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5401663125743738451087461 1012811836076950959578899)
                    ·
                      rfl

theorem cell22_2958666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 5, 3, 4].length) (baseStart_2958666 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2958666 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2958666 prefixEnd_2958666 := by exact prefixLift 2958666
  have htrace : WordTrace (prefixWord ++ tailWord_2958666) baseStart_2958666 baseEnd_2958666 := by
    simpa [prefixWord, tailWord_2958666, baseEnd_2958666] using wordTrace_append hprefix tailTrace_2958666
  have hstable : (prefixWord ++ tailWord_2958666).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2958666).length < 2 ^ (prefixWord ++ tailWord_2958666).sum := by decide
  have hdescent : baseEnd_2958666 < baseStart_2958666 := by decide
  rcases family_descends (prefixWord ++ tailWord_2958666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2958711 : List Nat := [1, 1, 3, 1, 1, 2, 3, 2, 4, 4]
def baseStart_2958711 : Nat := 118140960795 + 2958711 * 2 ^ 59
def prefixEnd_2958711 : Nat := 4983230072969 + 3 ^ 40 * 2958711 * 2
def baseEnd_2958711 : Nat := 1012827240496585842203761

theorem tailTrace_2958711 : CollatzResearch.WordTrace tailWord_2958711 prefixEnd_2958711 1012827240496585842203761 := by
  unfold tailWord_2958711
  simp only [CollatzResearch.WordTrace]
  refine ⟨107913055584102829454315987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71942037056068552969543991 107913055584102829454315987)
  ·
    refine ⟨161869583376154244181473981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107913055584102829454315987 161869583376154244181473981)
    ·
      refine ⟨60701093766057841568052743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 161869583376154244181473981 60701093766057841568052743)
      ·
        refine ⟨91051640649086762352079115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60701093766057841568052743 91051640649086762352079115)
        ·
          refine ⟨136577460973630143528118673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91051640649086762352079115 136577460973630143528118673)
          ·
            refine ⟨102433095730222607646089005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 136577460973630143528118673 102433095730222607646089005)
            ·
              refine ⟨38412410898833477867283377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 102433095730222607646089005 38412410898833477867283377)
              ·
                refine ⟨28809308174125108400462533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38412410898833477867283377 28809308174125108400462533)
                ·
                  refine ⟨5401745282648457825086725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28809308174125108400462533 5401745282648457825086725)
                  ·
                    refine ⟨1012827240496585842203761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5401745282648457825086725 1012827240496585842203761)
                    ·
                      rfl

theorem cell22_2958711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 3, 2, 4, 4].length) (baseStart_2958711 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2958711 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2958711 prefixEnd_2958711 := by exact prefixLift 2958711
  have htrace : WordTrace (prefixWord ++ tailWord_2958711) baseStart_2958711 baseEnd_2958711 := by
    simpa [prefixWord, tailWord_2958711, baseEnd_2958711] using wordTrace_append hprefix tailTrace_2958711
  have hstable : (prefixWord ++ tailWord_2958711).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2958711).length < 2 ^ (prefixWord ++ tailWord_2958711).sum := by decide
  have hdescent : baseEnd_2958711 < baseStart_2958711 := by decide
  rcases family_descends (prefixWord ++ tailWord_2958711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2958728 : List Nat := [2, 1, 3, 3, 1, 2, 1, 3, 2, 4]
def baseStart_2958728 : Nat := 118140960795 + 2958728 * 2 ^ 59
def prefixEnd_2958728 : Nat := 4983230072969 + 3 ^ 40 * 2958728 * 2
def baseEnd_2958728 : Nat := 1012833059944003464528709

theorem tailTrace_2958728 : CollatzResearch.WordTrace tailWord_2958728 prefixEnd_2958728 1012833059944003464528709 := by
  unfold tailWord_2958728
  simp only [CollatzResearch.WordTrace]
  refine ⟨53956837812520620678842419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71942450416694160905123225 53956837812520620678842419)
  ·
    refine ⟨80935256718780931018263629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53956837812520620678842419 80935256718780931018263629)
    ·
      refine ⟨30350721269542849131848861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 80935256718780931018263629 30350721269542849131848861)
      ·
        refine ⟨11381520476078568424443323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30350721269542849131848861 11381520476078568424443323)
        ·
          refine ⟨17072280714117852636664985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11381520476078568424443323 17072280714117852636664985)
          ·
            refine ⟨12804210535588389477498739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17072280714117852636664985 12804210535588389477498739)
            ·
              refine ⟨19206315803382584216248109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12804210535588389477498739 19206315803382584216248109)
              ·
                refine ⟨7202368426268469081093041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19206315803382584216248109 7202368426268469081093041)
                ·
                  refine ⟨5401776319701351810819781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7202368426268469081093041 5401776319701351810819781)
                  ·
                    refine ⟨1012833059944003464528709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5401776319701351810819781 1012833059944003464528709)
                    ·
                      rfl

theorem cell22_2958728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 1, 3, 2, 4].length) (baseStart_2958728 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2958728 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2958728 prefixEnd_2958728 := by exact prefixLift 2958728
  have htrace : WordTrace (prefixWord ++ tailWord_2958728) baseStart_2958728 baseEnd_2958728 := by
    simpa [prefixWord, tailWord_2958728, baseEnd_2958728] using wordTrace_append hprefix tailTrace_2958728
  have hstable : (prefixWord ++ tailWord_2958728).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2958728).length < 2 ^ (prefixWord ++ tailWord_2958728).sum := by decide
  have hdescent : baseEnd_2958728 < baseStart_2958728 := by decide
  rcases family_descends (prefixWord ++ tailWord_2958728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2958792 : List Nat := [2, 1, 3, 1, 3, 1, 4, 3, 1, 3]
def baseStart_2958792 : Nat := 118140960795 + 2958792 * 2 ^ 59
def prefixEnd_2958792 : Nat := 4983230072969 + 3 ^ 40 * 2958792 * 2
def baseEnd_2958792 : Nat := 1012854968451928630928513

theorem tailTrace_2958792 : CollatzResearch.WordTrace tailWord_2958792 prefixEnd_2958792 1012854968451928630928513 := by
  unfold tailWord_2958792
  simp only [CollatzResearch.WordTrace]
  refine ⟨53958004948404690144007315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71944006597872920192009753 53958004948404690144007315)
  ·
    refine ⟨80937007422607035216010973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53958004948404690144007315 80937007422607035216010973)
    ·
      refine ⟨30351377783477638206004115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 80937007422607035216010973 30351377783477638206004115)
      ·
        refine ⟨45527066675216457309006173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30351377783477638206004115 45527066675216457309006173)
        ·
          refine ⟨17072650003206171490877315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45527066675216457309006173 17072650003206171490877315)
          ·
            refine ⟨25608975004809257236315973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17072650003206171490877315 25608975004809257236315973)
            ·
              refine ⟨4801682813401735731809245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25608975004809257236315973 4801682813401735731809245)
              ·
                refine ⟨1800631055025650899428467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4801682813401735731809245 1800631055025650899428467)
                ·
                  refine ⟨2700946582538476349142701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1800631055025650899428467 2700946582538476349142701)
                  ·
                    refine ⟨1012854968451928630928513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2700946582538476349142701 1012854968451928630928513)
                    ·
                      rfl

theorem cell22_2958792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 4, 3, 1, 3].length) (baseStart_2958792 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2958792 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2958792 prefixEnd_2958792 := by exact prefixLift 2958792
  have htrace : WordTrace (prefixWord ++ tailWord_2958792) baseStart_2958792 baseEnd_2958792 := by
    simpa [prefixWord, tailWord_2958792, baseEnd_2958792] using wordTrace_append hprefix tailTrace_2958792
  have hstable : (prefixWord ++ tailWord_2958792).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2958792).length < 2 ^ (prefixWord ++ tailWord_2958792).sum := by decide
  have hdescent : baseEnd_2958792 < baseStart_2958792 := by decide
  rcases family_descends (prefixWord ++ tailWord_2958792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2958833 : List Nat := [1, 2, 2, 2, 3, 2, 2, 2, 6]
def baseStart_2958833 : Nat := 118140960795 + 2958833 * 2 ^ 59
def prefixEnd_2958833 : Nat := 4983230072969 + 3 ^ 40 * 2958833 * 2
def baseEnd_2958833 : Nat := 337623001196606063551129

theorem tailTrace_2958833 : CollatzResearch.WordTrace tailWord_2958833 prefixEnd_2958833 337623001196606063551129 := by
  unfold tailWord_2958833
  simp only [CollatzResearch.WordTrace]
  refine ⟨107917505289660844290257153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71945003526440562860171435 107917505289660844290257153)
  ·
    refine ⟨80938128967245633217692865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107917505289660844290257153 80938128967245633217692865)
    ·
      refine ⟨60703596725434224913269649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80938128967245633217692865 60703596725434224913269649)
      ·
        refine ⟨45527697544075668684952237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60703596725434224913269649 45527697544075668684952237)
        ·
          refine ⟨17072886579028375756857089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45527697544075668684952237 17072886579028375756857089)
          ·
            refine ⟨12804664934271281817642817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17072886579028375756857089 12804664934271281817642817)
            ·
              refine ⟨9603498700703461363232113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12804664934271281817642817 9603498700703461363232113)
              ·
                refine ⟨7202624025527596022424085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9603498700703461363232113 7202624025527596022424085)
                ·
                  refine ⟨337623001196606063551129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7202624025527596022424085 337623001196606063551129)
                  ·
                    rfl

theorem cell22_2958833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 2, 2, 6].length) (baseStart_2958833 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2958833 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2958833 prefixEnd_2958833 := by exact prefixLift 2958833
  have htrace : WordTrace (prefixWord ++ tailWord_2958833) baseStart_2958833 baseEnd_2958833 := by
    simpa [prefixWord, tailWord_2958833, baseEnd_2958833] using wordTrace_append hprefix tailTrace_2958833
  have hstable : (prefixWord ++ tailWord_2958833).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2958833).length < 2 ^ (prefixWord ++ tailWord_2958833).sum := by decide
  have hdescent : baseEnd_2958833 < baseStart_2958833 := by decide
  rcases family_descends (prefixWord ++ tailWord_2958833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2958865 : List Nat := [1, 2, 2, 1, 1, 2, 4, 4, 2, 3]
def baseStart_2958865 : Nat := 118140960795 + 2958865 * 2 ^ 59
def prefixEnd_2958865 : Nat := 4983230072969 + 3 ^ 40 * 2958865 * 2
def baseEnd_2958865 : Nat := 1012879957843780773853289

theorem tailTrace_2958865 : CollatzResearch.WordTrace tailWord_2958865 prefixEnd_2958865 1012879957843780773853289 := by
  unfold tailWord_2958865
  simp only [CollatzResearch.WordTrace]
  refine ⟨107918672425544913755422049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71945781617029942503614699 107918672425544913755422049)
  ·
    refine ⟨80939004319158685316566537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107918672425544913755422049 80939004319158685316566537)
    ·
      refine ⟨60704253239369013987424903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80939004319158685316566537 60704253239369013987424903)
      ·
        refine ⟨91056379859053520981137355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60704253239369013987424903 91056379859053520981137355)
        ·
          refine ⟨136584569788580281471706033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91056379859053520981137355 136584569788580281471706033)
          ·
            refine ⟨102438427341435211103779525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 136584569788580281471706033 102438427341435211103779525)
            ·
              refine ⟨19207205126519102081958661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 102438427341435211103779525 19207205126519102081958661)
              ·
                refine ⟨3601350961222331640367249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19207205126519102081958661 3601350961222331640367249)
                ·
                  refine ⟨2701013220916748730275437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3601350961222331640367249 2701013220916748730275437)
                  ·
                    refine ⟨1012879957843780773853289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2701013220916748730275437 1012879957843780773853289)
                    ·
                      rfl

theorem cell22_2958865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 4, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 4, 4, 2, 3].length) (baseStart_2958865 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2958865 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2958865 prefixEnd_2958865 := by exact prefixLift 2958865
  have htrace : WordTrace (prefixWord ++ tailWord_2958865) baseStart_2958865 baseEnd_2958865 := by
    simpa [prefixWord, tailWord_2958865, baseEnd_2958865] using wordTrace_append hprefix tailTrace_2958865
  have hstable : (prefixWord ++ tailWord_2958865).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2958865).length < 2 ^ (prefixWord ++ tailWord_2958865).sum := by decide
  have hdescent : baseEnd_2958865 < baseStart_2958865 := by decide
  rcases family_descends (prefixWord ++ tailWord_2958865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2958867 : List Nat := [1, 1, 1, 2, 1, 7, 3, 2, 4]
def baseStart_2958867 : Nat := 118140960795 + 2958867 * 2 ^ 59
def prefixEnd_2958867 : Nat := 4983230072969 + 3 ^ 40 * 2958867 * 2
def baseEnd_2958867 : Nat := 337626880828217811767761

theorem tailTrace_2958867 : CollatzResearch.WordTrace tailWord_2958867 prefixEnd_2958867 337626880828217811767761 := by
  unfold tailWord_2958867
  simp only [CollatzResearch.WordTrace]
  refine ⟨107918745371537668096994855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71945830247691778731329903 107918745371537668096994855)
  ·
    refine ⟨161878118057306502145492283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107918745371537668096994855 161878118057306502145492283)
    ·
      refine ⟨242817177085959753218238425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 161878118057306502145492283 242817177085959753218238425)
      ·
        refine ⟨182112882814469814913678819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 242817177085959753218238425 182112882814469814913678819)
        ·
          refine ⟨273169324221704722370518229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 182112882814469814913678819 273169324221704722370518229)
          ·
            refine ⟨6402406036446204430559021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 273169324221704722370518229 6402406036446204430559021)
            ·
              refine ⟨2400902263667326661459633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6402406036446204430559021 2400902263667326661459633)
              ·
                refine ⟨1800676697750494996094725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2400902263667326661459633 1800676697750494996094725)
                ·
                  refine ⟨337626880828217811767761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1800676697750494996094725 337626880828217811767761)
                  ·
                    rfl

theorem cell22_2958867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 7, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 7, 3, 2, 4].length) (baseStart_2958867 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2958867 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2958867 prefixEnd_2958867 := by exact prefixLift 2958867
  have htrace : WordTrace (prefixWord ++ tailWord_2958867) baseStart_2958867 baseEnd_2958867 := by
    simpa [prefixWord, tailWord_2958867, baseEnd_2958867] using wordTrace_append hprefix tailTrace_2958867
  have hstable : (prefixWord ++ tailWord_2958867).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2958867).length < 2 ^ (prefixWord ++ tailWord_2958867).sum := by decide
  have hdescent : baseEnd_2958867 < baseStart_2958867 := by decide
  rcases family_descends (prefixWord ++ tailWord_2958867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2958918 : List Nat := [6, 1, 1, 1, 3, 2, 2, 2, 4]
def baseStart_2958918 : Nat := 118140960795 + 2958918 * 2 ^ 59
def prefixEnd_2958918 : Nat := 4983230072969 + 3 ^ 40 * 2958918 * 2
def baseEnd_2958918 : Nat := 337632700275635434092709

theorem tailTrace_2958918 : CollatzResearch.WordTrace tailWord_2958918 prefixEnd_2958918 337632700275635434092709 := by
  unfold tailWord_2958918
  simp only [CollatzResearch.WordTrace]
  refine ⟨3372518921698528243971919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 71947070329568602538067605 3372518921698528243971919)
  ·
    refine ⟨5058778382547792365957879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3372518921698528243971919 5058778382547792365957879)
    ·
      refine ⟨7588167573821688548936819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5058778382547792365957879 7588167573821688548936819)
      ·
        refine ⟨11382251360732532823405229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7588167573821688548936819 11382251360732532823405229)
        ·
          refine ⟨4268344260274699808776961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11382251360732532823405229 4268344260274699808776961)
          ·
            refine ⟨3201258195206024856582721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4268344260274699808776961 3201258195206024856582721)
            ·
              refine ⟨2400943646404518642437041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3201258195206024856582721 2400943646404518642437041)
              ·
                refine ⟨1800707734803388981827781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2400943646404518642437041 1800707734803388981827781)
                ·
                  refine ⟨337632700275635434092709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1800707734803388981827781 337632700275635434092709)
                  ·
                    rfl

theorem cell22_2958918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 2, 2, 2, 4].length) (baseStart_2958918 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2958918 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2958918 prefixEnd_2958918 := by exact prefixLift 2958918
  have htrace : WordTrace (prefixWord ++ tailWord_2958918) baseStart_2958918 baseEnd_2958918 := by
    simpa [prefixWord, tailWord_2958918, baseEnd_2958918] using wordTrace_append hprefix tailTrace_2958918
  have hstable : (prefixWord ++ tailWord_2958918).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2958918).length < 2 ^ (prefixWord ++ tailWord_2958918).sum := by decide
  have hdescent : baseEnd_2958918 < baseStart_2958918 := by decide
  rcases family_descends (prefixWord ++ tailWord_2958918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2959004 : List Nat := [2, 2, 3, 2, 3, 1, 2, 2, 1, 4]
def baseStart_2959004 : Nat := 118140960795 + 2959004 * 2 ^ 59
def prefixEnd_2959004 : Nat := 4983230072969 + 3 ^ 40 * 2959004 * 2
def baseEnd_2959004 : Nat := 1012927540384430744627863

theorem tailTrace_2959004 : CollatzResearch.WordTrace tailWord_2959004 prefixEnd_2959004 1012927540384430744627863 := by
  unfold tailWord_2959004
  simp only [CollatzResearch.WordTrace]
  refine ⟨53961871086020670247366033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71949161448027560329821377 53961871086020670247366033)
  ·
    refine ⟨40471403314515502685524525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53961871086020670247366033 40471403314515502685524525)
    ·
      refine ⟨15176776242943313507071697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40471403314515502685524525 15176776242943313507071697)
      ·
        refine ⟨11382582182207485130303773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15176776242943313507071697 11382582182207485130303773)
        ·
          refine ⟨4268468318327806923863915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11382582182207485130303773 4268468318327806923863915)
          ·
            refine ⟨6402702477491710385795873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4268468318327806923863915 6402702477491710385795873)
            ·
              refine ⟨4802026858118782789346905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6402702477491710385795873 4802026858118782789346905)
              ·
                refine ⟨3601520143589087092010179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4802026858118782789346905 3601520143589087092010179)
                ·
                  refine ⟨5402280215383630638015269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3601520143589087092010179 5402280215383630638015269)
                  ·
                    refine ⟨1012927540384430744627863, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5402280215383630638015269 1012927540384430744627863)
                    ·
                      rfl

theorem cell22_2959004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 1, 2, 2, 1, 4].length) (baseStart_2959004 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2959004 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2959004 prefixEnd_2959004 := by exact prefixLift 2959004
  have htrace : WordTrace (prefixWord ++ tailWord_2959004) baseStart_2959004 baseEnd_2959004 := by
    simpa [prefixWord, tailWord_2959004, baseEnd_2959004] using wordTrace_append hprefix tailTrace_2959004
  have hstable : (prefixWord ++ tailWord_2959004).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2959004).length < 2 ^ (prefixWord ++ tailWord_2959004).sum := by decide
  have hdescent : baseEnd_2959004 < baseStart_2959004 := by decide
  rcases family_descends (prefixWord ++ tailWord_2959004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2959117 : List Nat := [1, 7, 2, 1, 2, 1, 1, 1, 2, 4]
def baseStart_2959117 : Nat := 118140960795 + 2959117 * 2 ^ 59
def prefixEnd_2959117 : Nat := 4983230072969 + 3 ^ 40 * 2959117 * 2
def baseEnd_2959117 : Nat := 1012966222593736116552517

theorem tailTrace_2959117 : CollatzResearch.WordTrace tailWord_2959117 prefixEnd_2959117 1012966222593736116552517 := by
  unfold tailWord_2959117
  simp only [CollatzResearch.WordTrace]
  refine ⟨107927863620631960793595605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71951909080421307195730403 107927863620631960793595605)
  ·
    refine ⟨2529559303608561581099897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 107927863620631960793595605 2529559303608561581099897)
    ·
      refine ⟨1897169477706421185824923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2529559303608561581099897 1897169477706421185824923)
      ·
        refine ⟨2845754216559631778737385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1897169477706421185824923 2845754216559631778737385)
        ·
          refine ⟨2134315662419723834053039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2845754216559631778737385 2134315662419723834053039)
          ·
            refine ⟨3201473493629585751079559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2134315662419723834053039 3201473493629585751079559)
            ·
              refine ⟨4802210240444378626619339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3201473493629585751079559 4802210240444378626619339)
              ·
                refine ⟨7203315360666567939929009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4802210240444378626619339 7203315360666567939929009)
                ·
                  refine ⟨5402486520499925954946757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7203315360666567939929009 5402486520499925954946757)
                  ·
                    refine ⟨1012966222593736116552517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5402486520499925954946757 1012966222593736116552517)
                    ·
                      rfl

theorem cell22_2959117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 2, 1, 1, 1, 2, 4].length) (baseStart_2959117 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2959117 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2959117 prefixEnd_2959117 := by exact prefixLift 2959117
  have htrace : WordTrace (prefixWord ++ tailWord_2959117) baseStart_2959117 baseEnd_2959117 := by
    simpa [prefixWord, tailWord_2959117, baseEnd_2959117] using wordTrace_append hprefix tailTrace_2959117
  have hstable : (prefixWord ++ tailWord_2959117).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2959117).length < 2 ^ (prefixWord ++ tailWord_2959117).sum := by decide
  have hdescent : baseEnd_2959117 < baseStart_2959117 := by decide
  rcases family_descends (prefixWord ++ tailWord_2959117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2959139 : List Nat := [1, 1, 1, 4, 2, 1, 6, 1, 1, 4]
def baseStart_2959139 : Nat := 118140960795 + 2959139 * 2 ^ 59
def prefixEnd_2959139 : Nat := 4983230072969 + 3 ^ 40 * 2959139 * 2
def baseEnd_2959139 : Nat := 1012973753643335392502449

theorem tailTrace_2959139 : CollatzResearch.WordTrace tailWord_2959139 prefixEnd_2959139 1012973753643335392502449 := by
  unfold tailWord_2959139
  simp only [CollatzResearch.WordTrace]
  refine ⟨107928666026552258550896471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71952444017701505700597647 107928666026552258550896471)
  ·
    refine ⟨161892999039828387826344707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107928666026552258550896471 161892999039828387826344707)
    ·
      refine ⟨242839498559742581739517061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 161892999039828387826344707 242839498559742581739517061)
      ·
        refine ⟨45532405979951734076159449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 242839498559742581739517061 45532405979951734076159449)
        ·
          refine ⟨34149304484963800557119587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45532405979951734076159449 34149304484963800557119587)
          ·
            refine ⟨51223956727445700835679381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34149304484963800557119587 51223956727445700835679381)
            ·
              refine ⟨2401122971599017226672471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 51223956727445700835679381 2401122971599017226672471)
              ·
                refine ⟨3601684457398525840008707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2401122971599017226672471 3601684457398525840008707)
                ·
                  refine ⟨5402526686097788760013061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3601684457398525840008707 5402526686097788760013061)
                  ·
                    refine ⟨1012973753643335392502449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5402526686097788760013061 1012973753643335392502449)
                    ·
                      rfl

theorem cell22_2959139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 6, 1, 1, 4].length) (baseStart_2959139 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2959139 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2959139 prefixEnd_2959139 := by exact prefixLift 2959139
  have htrace : WordTrace (prefixWord ++ tailWord_2959139) baseStart_2959139 baseEnd_2959139 := by
    simpa [prefixWord, tailWord_2959139, baseEnd_2959139] using wordTrace_append hprefix tailTrace_2959139
  have hstable : (prefixWord ++ tailWord_2959139).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2959139).length < 2 ^ (prefixWord ++ tailWord_2959139).sum := by decide
  have hdescent : baseEnd_2959139 < baseStart_2959139 := by decide
  rcases family_descends (prefixWord ++ tailWord_2959139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2959154 : List Nat := [3, 2, 1, 1, 3, 2, 2, 4, 4]
def baseStart_2959154 : Nat := 118140960795 + 2959154 * 2 ^ 59
def prefixEnd_2959154 : Nat := 4983230072969 + 3 ^ 40 * 2959154 * 2
def baseEnd_2959154 : Nat := 337659629483293451125801

theorem tailTrace_2959154 : CollatzResearch.WordTrace tailWord_2959154 prefixEnd_2959154 337659629483293451125801 := by
  unfold tailWord_2959154
  simp only [CollatzResearch.WordTrace]
  refine ⟨26982303280374479028173129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71952808747665277408461677 26982303280374479028173129)
  ·
    refine ⟨20236727460280859271129847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26982303280374479028173129 20236727460280859271129847)
    ·
      refine ⟨30355091190421288906694771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20236727460280859271129847 30355091190421288906694771)
      ·
        refine ⟨45532636785631933360042157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30355091190421288906694771 45532636785631933360042157)
        ·
          refine ⟨17074738794611975010015809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45532636785631933360042157 17074738794611975010015809)
          ·
            refine ⟨12806054095958981257511857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17074738794611975010015809 12806054095958981257511857)
            ·
              refine ⟨9604540571969235943133893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12806054095958981257511857 9604540571969235943133893)
              ·
                refine ⟨1800851357244231739337605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9604540571969235943133893 1800851357244231739337605)
                ·
                  refine ⟨337659629483293451125801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1800851357244231739337605 337659629483293451125801)
                  ·
                    rfl

theorem cell22_2959154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 2, 4, 4].length) (baseStart_2959154 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2959154 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2959154 prefixEnd_2959154 := by exact prefixLift 2959154
  have htrace : WordTrace (prefixWord ++ tailWord_2959154) baseStart_2959154 baseEnd_2959154 := by
    simpa [prefixWord, tailWord_2959154, baseEnd_2959154] using wordTrace_append hprefix tailTrace_2959154
  have hstable : (prefixWord ++ tailWord_2959154).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2959154).length < 2 ^ (prefixWord ++ tailWord_2959154).sum := by decide
  have hdescent : baseEnd_2959154 < baseStart_2959154 := by decide
  rcases family_descends (prefixWord ++ tailWord_2959154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2959304 : List Nat := [2, 1, 3, 1, 4, 1, 2, 2, 1, 5]
def baseStart_2959304 : Nat := 118140960795 + 2959304 * 2 ^ 59
def prefixEnd_2959304 : Nat := 4983230072969 + 3 ^ 40 * 2959304 * 2
def baseEnd_2959304 : Nat := 1013030236515329962126943

theorem tailTrace_2959304 : CollatzResearch.WordTrace tailWord_2959304 prefixEnd_2959304 1013030236515329962126943 := by
  unfold tailWord_2959304
  simp only [CollatzResearch.WordTrace]
  refine ⟨53967342035477245865326483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71956456047302994487101977 53967342035477245865326483)
  ·
    refine ⟨80951013053215868797989725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53967342035477245865326483 80951013053215868797989725)
    ·
      refine ⟨30356629894955950799246147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 80951013053215868797989725 30356629894955950799246147)
      ·
        refine ⟨45534944842433926198869221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30356629894955950799246147 45534944842433926198869221)
        ·
          refine ⟨8537802157956361162287979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 45534944842433926198869221 8537802157956361162287979)
          ·
            refine ⟨12806703236934541743431969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8537802157956361162287979 12806703236934541743431969)
            ·
              refine ⟨9605027427700906307573977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12806703236934541743431969 9605027427700906307573977)
              ·
                refine ⟨7203770570775679730680483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9605027427700906307573977 7203770570775679730680483)
                ·
                  refine ⟨10805655856163519596020725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7203770570775679730680483 10805655856163519596020725)
                  ·
                    refine ⟨1013030236515329962126943, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10805655856163519596020725 1013030236515329962126943)
                    ·
                      rfl

theorem cell22_2959304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 2, 2, 1, 5].length) (baseStart_2959304 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2959304 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2959304 prefixEnd_2959304 := by exact prefixLift 2959304
  have htrace : WordTrace (prefixWord ++ tailWord_2959304) baseStart_2959304 baseEnd_2959304 := by
    simpa [prefixWord, tailWord_2959304, baseEnd_2959304] using wordTrace_append hprefix tailTrace_2959304
  have hstable : (prefixWord ++ tailWord_2959304).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2959304).length < 2 ^ (prefixWord ++ tailWord_2959304).sum := by decide
  have hdescent : baseEnd_2959304 < baseStart_2959304 := by decide
  rcases family_descends (prefixWord ++ tailWord_2959304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2959308 : List Nat := [2, 2, 1, 4, 1, 4, 2, 1, 1, 4]
def baseStart_2959308 : Nat := 118140960795 + 2959308 * 2 ^ 59
def prefixEnd_2959308 : Nat := 4983230072969 + 3 ^ 40 * 2959308 * 2
def baseEnd_2959308 : Nat := 1013031605797075285026931

theorem tailTrace_2959308 : CollatzResearch.WordTrace tailWord_2959308 prefixEnd_2959308 1013031605797075285026931 := by
  unfold tailWord_2959308
  simp only [CollatzResearch.WordTrace]
  refine ⟨53967414981470000206899289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71956553308626666942532385 53967414981470000206899289)
  ·
    refine ⟨40475561236102500155174467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53967414981470000206899289 40475561236102500155174467)
    ·
      refine ⟨60713341854153750232761701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40475561236102500155174467 60713341854153750232761701)
      ·
        refine ⟨11383751597653828168642819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 60713341854153750232761701 11383751597653828168642819)
        ·
          refine ⟨17075627396480742252964229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11383751597653828168642819 17075627396480742252964229)
          ·
            refine ⟨3201680136840139172430793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17075627396480742252964229 3201680136840139172430793)
            ·
              refine ⟨2401260102630104379323095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3201680136840139172430793 2401260102630104379323095)
              ·
                refine ⟨3601890153945156568984643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2401260102630104379323095 3601890153945156568984643)
                ·
                  refine ⟨5402835230917734853476965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3601890153945156568984643 5402835230917734853476965)
                  ·
                    refine ⟨1013031605797075285026931, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5402835230917734853476965 1013031605797075285026931)
                    ·
                      rfl

theorem cell22_2959308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 4, 2, 1, 1, 4].length) (baseStart_2959308 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2959308 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2959308 prefixEnd_2959308 := by exact prefixLift 2959308
  have htrace : WordTrace (prefixWord ++ tailWord_2959308) baseStart_2959308 baseEnd_2959308 := by
    simpa [prefixWord, tailWord_2959308, baseEnd_2959308] using wordTrace_append hprefix tailTrace_2959308
  have hstable : (prefixWord ++ tailWord_2959308).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2959308).length < 2 ^ (prefixWord ++ tailWord_2959308).sum := by decide
  have hdescent : baseEnd_2959308 < baseStart_2959308 := by decide
  rcases family_descends (prefixWord ++ tailWord_2959308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2959321 : List Nat := [1, 2, 1, 2, 6, 1, 1, 1, 4, 3]
def baseStart_2959321 : Nat := 118140960795 + 2959321 * 2 ^ 59
def prefixEnd_2959321 : Nat := 4983230072969 + 3 ^ 40 * 2959321 * 2
def baseEnd_2959321 : Nat := 1013036055962747584451891

theorem tailTrace_2959321 : CollatzResearch.WordTrace tailWord_2959321 prefixEnd_2959321 1013036055962747584451891 := by
  unfold tailWord_2959321
  simp only [CollatzResearch.WordTrace]
  refine ⟨107935304111892903634021817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71956869407928602422681211 107935304111892903634021817)
  ·
    refine ⟨80951478083919677725516363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107935304111892903634021817 80951478083919677725516363)
    ·
      refine ⟨121427217125879516588274545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80951478083919677725516363 121427217125879516588274545)
      ·
        refine ⟨91070412844409637441205909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 121427217125879516588274545 91070412844409637441205909)
        ·
          refine ⟨4268925602081701755056527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 91070412844409637441205909 4268925602081701755056527)
          ·
            refine ⟨6403388403122552632584791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4268925602081701755056527 6403388403122552632584791)
            ·
              refine ⟨9605082604683828948877187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6403388403122552632584791 9605082604683828948877187)
              ·
                refine ⟨14407623907025743423315781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9605082604683828948877187 14407623907025743423315781)
                ·
                  refine ⟨2701429482567326891871709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14407623907025743423315781 2701429482567326891871709)
                  ·
                    refine ⟨1013036055962747584451891, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2701429482567326891871709 1013036055962747584451891)
                    ·
                      rfl

theorem cell22_2959321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 1, 1, 1, 4, 3].length) (baseStart_2959321 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2959321 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2959321 prefixEnd_2959321 := by exact prefixLift 2959321
  have htrace : WordTrace (prefixWord ++ tailWord_2959321) baseStart_2959321 baseEnd_2959321 := by
    simpa [prefixWord, tailWord_2959321, baseEnd_2959321] using wordTrace_append hprefix tailTrace_2959321
  have hstable : (prefixWord ++ tailWord_2959321).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2959321).length < 2 ^ (prefixWord ++ tailWord_2959321).sum := by decide
  have hdescent : baseEnd_2959321 < baseStart_2959321 := by decide
  rcases family_descends (prefixWord ++ tailWord_2959321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2959338 : List Nat := [3, 1, 3, 1, 2, 1, 5, 1, 2, 3]
def baseStart_2959338 : Nat := 118140960795 + 2959338 * 2 ^ 59
def prefixEnd_2959338 : Nat := 4983230072969 + 3 ^ 40 * 2959338 * 2
def baseEnd_2959338 : Nat := 1013041875410165206776839

theorem tailTrace_2959338 : CollatzResearch.WordTrace tailWord_2959338 prefixEnd_2959338 1013041875410165206776839 := by
  unfold tailWord_2959338
  simp only [CollatzResearch.WordTrace]
  refine ⟨26983981038207828884347667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71957282768554210358260445 26983981038207828884347667)
  ·
    refine ⟨40475971557311743326521501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26983981038207828884347667 40475971557311743326521501)
    ·
      refine ⟨15178489333991903747445563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40475971557311743326521501 15178489333991903747445563)
      ·
        refine ⟨22767734000987855621168345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15178489333991903747445563 22767734000987855621168345)
        ·
          refine ⟨17075800500740891715876259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22767734000987855621168345 17075800500740891715876259)
          ·
            refine ⟨25613700751111337573814389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17075800500740891715876259 25613700751111337573814389)
            ·
              refine ⟨2401284445416687897545099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 25613700751111337573814389 2401284445416687897545099)
              ·
                refine ⟨3601926668125031846317649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2401284445416687897545099 3601926668125031846317649)
                ·
                  refine ⟨2701445001093773884738237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3601926668125031846317649 2701445001093773884738237)
                  ·
                    refine ⟨1013041875410165206776839, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2701445001093773884738237 1013041875410165206776839)
                    ·
                      rfl

theorem cell22_2959338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 5, 1, 2, 3].length) (baseStart_2959338 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2959338 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2959338 prefixEnd_2959338 := by exact prefixLift 2959338
  have htrace : WordTrace (prefixWord ++ tailWord_2959338) baseStart_2959338 baseEnd_2959338 := by
    simpa [prefixWord, tailWord_2959338, baseEnd_2959338] using wordTrace_append hprefix tailTrace_2959338
  have hstable : (prefixWord ++ tailWord_2959338).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2959338).length < 2 ^ (prefixWord ++ tailWord_2959338).sum := by decide
  have hdescent : baseEnd_2959338 < baseStart_2959338 := by decide
  rcases family_descends (prefixWord ++ tailWord_2959338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2959347 : List Nat := [1, 1, 1, 2, 2, 2, 1, 4, 2, 6]
def baseStart_2959347 : Nat := 118140960795 + 2959347 * 2 ^ 59
def prefixEnd_2959347 : Nat := 4983230072969 + 3 ^ 40 * 2959347 * 2
def baseEnd_2959347 : Nat := 1013044956294092183301811

theorem tailTrace_2959347 : CollatzResearch.WordTrace tailWord_2959347 prefixEnd_2959347 1013044956294092183301811 := by
  unfold tailWord_2959347
  simp only [CollatzResearch.WordTrace]
  refine ⟨107936252409798710074468295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71957501606532473382978863 107936252409798710074468295)
  ·
    refine ⟨161904378614698065111702443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107936252409798710074468295 161904378614698065111702443)
    ·
      refine ⟨242856567922047097667553665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 161904378614698065111702443 242856567922047097667553665)
      ·
        refine ⟨182142425941535323250665249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 242856567922047097667553665 182142425941535323250665249)
        ·
          refine ⟨136606819456151492437998937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 182142425941535323250665249 136606819456151492437998937)
          ·
            refine ⟨102455114592113619328499203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 136606819456151492437998937 102455114592113619328499203)
            ·
              refine ⟨153682671888170428992748805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 102455114592113619328499203 153682671888170428992748805)
              ·
                refine ⟨28815500979031955436140401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 153682671888170428992748805 28815500979031955436140401)
                ·
                  refine ⟨21611625734273966577105301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28815500979031955436140401 21611625734273966577105301)
                  ·
                    refine ⟨1013044956294092183301811, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21611625734273966577105301 1013044956294092183301811)
                    ·
                      rfl

theorem cell22_2959347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 4, 2, 6].length) (baseStart_2959347 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2959347 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2959347 prefixEnd_2959347 := by exact prefixLift 2959347
  have htrace : WordTrace (prefixWord ++ tailWord_2959347) baseStart_2959347 baseEnd_2959347 := by
    simpa [prefixWord, tailWord_2959347, baseEnd_2959347] using wordTrace_append hprefix tailTrace_2959347
  have hstable : (prefixWord ++ tailWord_2959347).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2959347).length < 2 ^ (prefixWord ++ tailWord_2959347).sum := by decide
  have hdescent : baseEnd_2959347 < baseStart_2959347 := by decide
  rcases family_descends (prefixWord ++ tailWord_2959347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2959394 : List Nat := [3, 3, 1, 1, 1, 2, 2, 1, 1, 7]
def baseStart_2959394 : Nat := 118140960795 + 2959394 * 2 ^ 59
def prefixEnd_2959394 : Nat := 4983230072969 + 3 ^ 40 * 2959394 * 2
def baseEnd_2959394 : Nat := 1013061045354599727376667

theorem tailTrace_2959394 : CollatzResearch.WordTrace tailWord_2959394 prefixEnd_2959394 1013061045354599727376667 := by
  unfold tailWord_2959394
  simp only [CollatzResearch.WordTrace]
  refine ⟨26984491660157109275357309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71958644427085624734286157 26984491660157109275357309)
  ·
    refine ⟨10119184372558915978258991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26984491660157109275357309 10119184372558915978258991)
    ·
      refine ⟨15178776558838373967388487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10119184372558915978258991 15178776558838373967388487)
      ·
        refine ⟨22768164838257560951082731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15178776558838373967388487 22768164838257560951082731)
        ·
          refine ⟨34152247257386341426624097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22768164838257560951082731 34152247257386341426624097)
          ·
            refine ⟨25614185443039756069968073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34152247257386341426624097 25614185443039756069968073)
            ·
              refine ⟨19210639082279817052476055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25614185443039756069968073 19210639082279817052476055)
              ·
                refine ⟨28815958623419725578714083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19210639082279817052476055 28815958623419725578714083)
                ·
                  refine ⟨43223937935129588368071125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28815958623419725578714083 43223937935129588368071125)
                  ·
                    refine ⟨1013061045354599727376667, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 43223937935129588368071125 1013061045354599727376667)
                    ·
                      rfl

theorem cell22_2959394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 2, 1, 1, 7].length) (baseStart_2959394 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2959394 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2959394 prefixEnd_2959394 := by exact prefixLift 2959394
  have htrace : WordTrace (prefixWord ++ tailWord_2959394) baseStart_2959394 baseEnd_2959394 := by
    simpa [prefixWord, tailWord_2959394, baseEnd_2959394] using wordTrace_append hprefix tailTrace_2959394
  have hstable : (prefixWord ++ tailWord_2959394).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2959394).length < 2 ^ (prefixWord ++ tailWord_2959394).sum := by decide
  have hdescent : baseEnd_2959394 < baseStart_2959394 := by decide
  rcases family_descends (prefixWord ++ tailWord_2959394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2959456 : List Nat := [2, 1, 1, 3, 2, 4, 2, 1, 1, 5]
def baseStart_2959456 : Nat := 118140960795 + 2959456 * 2 ^ 59
def prefixEnd_2959456 : Nat := 4983230072969 + 3 ^ 40 * 2959456 * 2
def baseEnd_2959456 : Nat := 1013082269221652232326477

theorem tailTrace_2959456 : CollatzResearch.WordTrace tailWord_2959456 prefixEnd_2959456 1013082269221652232326477 := by
  unfold tailWord_2959456
  simp only [CollatzResearch.WordTrace]
  refine ⟨53970113983201910845093111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71960151977602547793457481 53970113983201910845093111)
  ·
    refine ⟨80955170974802866267639667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53970113983201910845093111 80955170974802866267639667)
    ·
      refine ⟨121432756462204299401459501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80955170974802866267639667 121432756462204299401459501)
      ·
        refine ⟨45537283673326612275547313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 121432756462204299401459501 45537283673326612275547313)
        ·
          refine ⟨34152962754994959206660485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45537283673326612275547313 34152962754994959206660485)
          ·
            refine ⟨6403680516561554851248841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 34152962754994959206660485 6403680516561554851248841)
            ·
              refine ⟨4802760387421166138436631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6403680516561554851248841 4802760387421166138436631)
              ·
                refine ⟨7204140581131749207654947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4802760387421166138436631 7204140581131749207654947)
                ·
                  refine ⟨10806210871697623811482421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7204140581131749207654947 10806210871697623811482421)
                  ·
                    refine ⟨1013082269221652232326477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10806210871697623811482421 1013082269221652232326477)
                    ·
                      rfl

theorem cell22_2959456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 4, 2, 1, 1, 5].length) (baseStart_2959456 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2959456 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2959456 prefixEnd_2959456 := by exact prefixLift 2959456
  have htrace : WordTrace (prefixWord ++ tailWord_2959456) baseStart_2959456 baseEnd_2959456 := by
    simpa [prefixWord, tailWord_2959456, baseEnd_2959456] using wordTrace_append hprefix tailTrace_2959456
  have hstable : (prefixWord ++ tailWord_2959456).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2959456).length < 2 ^ (prefixWord ++ tailWord_2959456).sum := by decide
  have hdescent : baseEnd_2959456 < baseStart_2959456 := by decide
  rcases family_descends (prefixWord ++ tailWord_2959456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2959458 : List Nat := [3, 3, 2, 2, 2, 1, 1, 2, 6]
def baseStart_2959458 : Nat := 118140960795 + 2959458 * 2 ^ 59
def prefixEnd_2959458 : Nat := 4983230072969 + 3 ^ 40 * 2959458 * 2
def baseEnd_2959458 : Nat := 337694317954174964592157

theorem tailTrace_2959458 : CollatzResearch.WordTrace tailWord_2959458 prefixEnd_2959458 337694317954174964592157 := by
  unfold tailWord_2959458
  simp only [CollatzResearch.WordTrace]
  refine ⟨26985075228099144007939757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71960200608264384021172685 26985075228099144007939757)
  ·
    refine ⟨10119403210537179002977409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26985075228099144007939757 10119403210537179002977409)
    ·
      refine ⟨7589552407902884252233057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10119403210537179002977409 7589552407902884252233057)
      ·
        refine ⟨5692164305927163189174793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7589552407902884252233057 5692164305927163189174793)
        ·
          refine ⟨4269123229445372391881095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5692164305927163189174793 4269123229445372391881095)
          ·
            refine ⟨6403684844168058587821643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4269123229445372391881095 6403684844168058587821643)
            ·
              refine ⟨9605527266252087881732465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6403684844168058587821643 9605527266252087881732465)
              ·
                refine ⟨7204145449689065911299349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9605527266252087881732465 7204145449689065911299349)
                ·
                  refine ⟨337694317954174964592157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7204145449689065911299349 337694317954174964592157)
                  ·
                    rfl

theorem cell22_2959458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 1, 1, 2, 6].length) (baseStart_2959458 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2959458 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2959458 prefixEnd_2959458 := by exact prefixLift 2959458
  have htrace : WordTrace (prefixWord ++ tailWord_2959458) baseStart_2959458 baseEnd_2959458 := by
    simpa [prefixWord, tailWord_2959458, baseEnd_2959458] using wordTrace_append hprefix tailTrace_2959458
  have hstable : (prefixWord ++ tailWord_2959458).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2959458).length < 2 ^ (prefixWord ++ tailWord_2959458).sum := by decide
  have hdescent : baseEnd_2959458 < baseStart_2959458 := by decide
  rcases family_descends (prefixWord ++ tailWord_2959458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2959471 : List Nat := [1, 1, 2, 1, 3, 4, 3, 1, 2, 4]
def baseStart_2959471 : Nat := 118140960795 + 2959471 * 2 ^ 59
def prefixEnd_2959471 : Nat := 4983230072969 + 3 ^ 40 * 2959471 * 2
def baseEnd_2959471 : Nat := 1013087404028197193201431

theorem tailTrace_2959471 : CollatzResearch.WordTrace tailWord_2959471 prefixEnd_2959471 1013087404028197193201431 := by
  unfold tailWord_2959471
  simp only [CollatzResearch.WordTrace]
  refine ⟨107940775061349479251982267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71960516707566319501321511 107940775061349479251982267)
  ·
    refine ⟨161911162592024218877973401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107940775061349479251982267 161911162592024218877973401)
    ·
      refine ⟨121433371944018164158480051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 161911162592024218877973401 121433371944018164158480051)
      ·
        refine ⟨182150057916027246237720077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121433371944018164158480051 182150057916027246237720077)
        ·
          refine ⟨68306271718510217339145029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 182150057916027246237720077 68306271718510217339145029)
          ·
            refine ⟨12807425947220665751089693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 68306271718510217339145029 12807425947220665751089693)
            ·
              refine ⟨4802784730207749656658635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12807425947220665751089693 4802784730207749656658635)
              ·
                refine ⟨7204177095311624484987953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4802784730207749656658635 7204177095311624484987953)
                ·
                  refine ⟨5403132821483718363740965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7204177095311624484987953 5403132821483718363740965)
                  ·
                    refine ⟨1013087404028197193201431, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5403132821483718363740965 1013087404028197193201431)
                    ·
                      rfl

theorem cell22_2959471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 3, 1, 2, 4].length) (baseStart_2959471 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2959471 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2959471 prefixEnd_2959471 := by exact prefixLift 2959471
  have htrace : WordTrace (prefixWord ++ tailWord_2959471) baseStart_2959471 baseEnd_2959471 := by
    simpa [prefixWord, tailWord_2959471, baseEnd_2959471] using wordTrace_append hprefix tailTrace_2959471
  have hstable : (prefixWord ++ tailWord_2959471).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2959471).length < 2 ^ (prefixWord ++ tailWord_2959471).sum := by decide
  have hdescent : baseEnd_2959471 < baseStart_2959471 := by decide
  rcases family_descends (prefixWord ++ tailWord_2959471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2959552 : List Nat := [2, 1, 1, 2, 5, 2, 3, 2, 1, 3]
def baseStart_2959552 : Nat := 118140960795 + 2959552 * 2 ^ 59
def prefixEnd_2959552 : Nat := 4983230072969 + 3 ^ 40 * 2959552 * 2
def baseEnd_2959552 : Nat := 1013115131983539981926183

theorem tailTrace_2959552 : CollatzResearch.WordTrace tailWord_2959552 prefixEnd_2959552 1013115131983539981926183 := by
  unfold tailWord_2959552
  simp only [CollatzResearch.WordTrace]
  refine ⟨53971864687028015042840455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71962486249370686723787273 53971864687028015042840455)
  ·
    refine ⟨80957797030542022564260683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53971864687028015042840455 80957797030542022564260683)
    ·
      refine ⟨121436695545813033846391025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80957797030542022564260683 121436695545813033846391025)
      ·
        refine ⟨91077521659359775384793269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 121436695545813033846391025 91077521659359775384793269)
        ·
          refine ⟨8538517655564978942324369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 91077521659359775384793269 8538517655564978942324369)
          ·
            refine ⟨6403888241673734206743277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8538517655564978942324369 6403888241673734206743277)
            ·
              refine ⟨2401458090627650327528729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6403888241673734206743277 2401458090627650327528729)
              ·
                refine ⟨1801093567970737745646547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2401458090627650327528729 1801093567970737745646547)
                ·
                  refine ⟨2701640351956106618469821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1801093567970737745646547 2701640351956106618469821)
                  ·
                    refine ⟨1013115131983539981926183, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2701640351956106618469821 1013115131983539981926183)
                    ·
                      rfl

theorem cell22_2959552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 2, 3, 2, 1, 3].length) (baseStart_2959552 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2959552 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2959552 prefixEnd_2959552 := by exact prefixLift 2959552
  have htrace : WordTrace (prefixWord ++ tailWord_2959552) baseStart_2959552 baseEnd_2959552 := by
    simpa [prefixWord, tailWord_2959552, baseEnd_2959552] using wordTrace_append hprefix tailTrace_2959552
  have hstable : (prefixWord ++ tailWord_2959552).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2959552).length < 2 ^ (prefixWord ++ tailWord_2959552).sum := by decide
  have hdescent : baseEnd_2959552 < baseStart_2959552 := by decide
  rcases family_descends (prefixWord ++ tailWord_2959552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2959578 : List Nat := [3, 1, 1, 2, 2, 1, 5, 2, 1, 4]
def baseStart_2959578 : Nat := 118140960795 + 2959578 * 2 ^ 59
def prefixEnd_2959578 : Nat := 4983230072969 + 3 ^ 40 * 2959578 * 2
def baseEnd_2959578 : Nat := 1013124032314884580776103

theorem tailTrace_2959578 : CollatzResearch.WordTrace tailWord_2959578 prefixEnd_2959578 1013124032314884580776103 := by
  unfold tailWord_2959578
  simp only [CollatzResearch.WordTrace]
  refine ⟨26986169417990459131531847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71963118447974557684084925 26986169417990459131531847)
  ·
    refine ⟨40479254126985688697297771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26986169417990459131531847 40479254126985688697297771)
    ·
      refine ⟨60718881190478533045946657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40479254126985688697297771 60718881190478533045946657)
      ·
        refine ⟨45539160892858899784459993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60718881190478533045946657 45539160892858899784459993)
        ·
          refine ⟨34154370669644174838344995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45539160892858899784459993 34154370669644174838344995)
          ·
            refine ⟨51231556004466262257517493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34154370669644174838344995 51231556004466262257517493)
            ·
              refine ⟨4802958375418712086642265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 51231556004466262257517493 4802958375418712086642265)
              ·
                refine ⟨3602218781564034064981699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4802958375418712086642265 3602218781564034064981699)
                ·
                  refine ⟨5403328172346051097472549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3602218781564034064981699 5403328172346051097472549)
                  ·
                    refine ⟨1013124032314884580776103, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5403328172346051097472549 1013124032314884580776103)
                    ·
                      rfl

theorem cell22_2959578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 5, 2, 1, 4].length) (baseStart_2959578 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2959578 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2959578 prefixEnd_2959578 := by exact prefixLift 2959578
  have htrace : WordTrace (prefixWord ++ tailWord_2959578) baseStart_2959578 baseEnd_2959578 := by
    simpa [prefixWord, tailWord_2959578, baseEnd_2959578] using wordTrace_append hprefix tailTrace_2959578
  have hstable : (prefixWord ++ tailWord_2959578).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2959578).length < 2 ^ (prefixWord ++ tailWord_2959578).sum := by decide
  have hdescent : baseEnd_2959578 < baseStart_2959578 := by decide
  rcases family_descends (prefixWord ++ tailWord_2959578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2959610 : List Nat := [3, 1, 1, 1, 1, 5, 4, 2, 4]
def baseStart_2959610 : Nat := 118140960795 + 2959610 * 2 ^ 59
def prefixEnd_2959610 : Nat := 4983230072969 + 3 ^ 40 * 2959610 * 2
def baseEnd_2959610 : Nat := 337711662189615721325335

theorem tailTrace_2959610 : CollatzResearch.WordTrace tailWord_2959610 prefixEnd_2959610 337711662189615721325335 := by
  unfold tailWord_2959610
  simp only [CollatzResearch.WordTrace]
  refine ⟨26986461201961476497823071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71963896538563937327528189 26986461201961476497823071)
  ·
    refine ⟨40479691802942214746734607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26986461201961476497823071 40479691802942214746734607)
    ·
      refine ⟨60719537704413322120101911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40479691802942214746734607 60719537704413322120101911)
      ·
        refine ⟨91079306556619983180152867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60719537704413322120101911 91079306556619983180152867)
        ·
          refine ⟨136618959834929974770229301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91079306556619983180152867 136618959834929974770229301)
          ·
            refine ⟨12808027484524685134708997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 136618959834929974770229301 12808027484524685134708997)
            ·
              refine ⟨2401505153348378462757937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12808027484524685134708997 2401505153348378462757937)
              ·
                refine ⟨1801128865011283847068453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2401505153348378462757937 1801128865011283847068453)
                ·
                  refine ⟨337711662189615721325335, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1801128865011283847068453 337711662189615721325335)
                  ·
                    rfl

theorem cell22_2959610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 4, 2, 4].length) (baseStart_2959610 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2959610 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2959610 prefixEnd_2959610 := by exact prefixLift 2959610
  have htrace : WordTrace (prefixWord ++ tailWord_2959610) baseStart_2959610 baseEnd_2959610 := by
    simpa [prefixWord, tailWord_2959610, baseEnd_2959610] using wordTrace_append hprefix tailTrace_2959610
  have hstable : (prefixWord ++ tailWord_2959610).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2959610).length < 2 ^ (prefixWord ++ tailWord_2959610).sum := by decide
  have hdescent : baseEnd_2959610 < baseStart_2959610 := by decide
  rcases family_descends (prefixWord ++ tailWord_2959610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2959711 : List Nat := [1, 1, 2, 3, 1, 2, 2, 2, 8]
def baseStart_2959711 : Nat := 118140960795 + 2959711 * 2 ^ 59
def prefixEnd_2959711 : Nat := 4983230072969 + 3 ^ 40 * 2959711 * 2
def baseEnd_2959711 : Nat := 337723186977638855733565

theorem tailTrace_2959711 : CollatzResearch.WordTrace tailWord_2959711 prefixEnd_2959711 337723186977638855733565 := by
  unfold tailWord_2959711
  simp only [CollatzResearch.WordTrace]
  refine ⟨107949528580480000240718987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71966352386986666827145991 107949528580480000240718987)
  ·
    refine ⟨161924292870720000361078481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107949528580480000240718987 161924292870720000361078481)
    ·
      refine ⟨121443219653040000270808861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 161924292870720000361078481 121443219653040000270808861)
      ·
        refine ⟨45541207369890000101553323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 121443219653040000270808861 45541207369890000101553323)
        ·
          refine ⟨68311811054835000152329985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45541207369890000101553323 68311811054835000152329985)
          ·
            refine ⟨51233858291126250114247489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 68311811054835000152329985 51233858291126250114247489)
            ·
              refine ⟨38425393718344687585685617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51233858291126250114247489 38425393718344687585685617)
              ·
                refine ⟨28819045288758515689264213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38425393718344687585685617 28819045288758515689264213)
                ·
                  refine ⟨337723186977638855733565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 28819045288758515689264213 337723186977638855733565)
                  ·
                    rfl

theorem cell22_2959711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 2, 2, 8].length) (baseStart_2959711 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2959711 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2959711 prefixEnd_2959711 := by exact prefixLift 2959711
  have htrace : WordTrace (prefixWord ++ tailWord_2959711) baseStart_2959711 baseEnd_2959711 := by
    simpa [prefixWord, tailWord_2959711, baseEnd_2959711] using wordTrace_append hprefix tailTrace_2959711
  have hstable : (prefixWord ++ tailWord_2959711).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2959711).length < 2 ^ (prefixWord ++ tailWord_2959711).sum := by decide
  have hdescent : baseEnd_2959711 < baseStart_2959711 := by decide
  rcases family_descends (prefixWord ++ tailWord_2959711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2959728 : List Nat := [2, 1, 1, 1, 4, 3, 3, 1, 6]
def baseStart_2959728 : Nat := 118140960795 + 2959728 * 2 ^ 59
def prefixEnd_2959728 : Nat := 4983230072969 + 3 ^ 40 * 2959728 * 2
def baseEnd_2959728 : Nat := 337725126793444729841881

theorem tailTrace_2959728 : CollatzResearch.WordTrace tailWord_2959728 prefixEnd_2959728 337725126793444729841881 := by
  unfold tailWord_2959728
  simp only [CollatzResearch.WordTrace]
  refine ⟨53975074310709206072043919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71966765747612274762725225 53975074310709206072043919)
  ·
    refine ⟨80962611466063809108065879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53975074310709206072043919 80962611466063809108065879)
    ·
      refine ⟨121443917199095713662098819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80962611466063809108065879 121443917199095713662098819)
      ·
        refine ⟨182165875798643570493148229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121443917199095713662098819 182165875798643570493148229)
        ·
          refine ⟨34156101712245669467465293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 182165875798643570493148229 34156101712245669467465293)
          ·
            refine ⟨12808538142092126050299485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34156101712245669467465293 12808538142092126050299485)
            ·
              refine ⟨4803201803284547268862307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12808538142092126050299485 4803201803284547268862307)
              ·
                refine ⟨7204802704926820903293461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4803201803284547268862307 7204802704926820903293461)
                ·
                  refine ⟨337725126793444729841881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7204802704926820903293461 337725126793444729841881)
                  ·
                    rfl

theorem cell22_2959728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 3, 1, 6].length) (baseStart_2959728 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2959728 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2959728 prefixEnd_2959728 := by exact prefixLift 2959728
  have htrace : WordTrace (prefixWord ++ tailWord_2959728) baseStart_2959728 baseEnd_2959728 := by
    simpa [prefixWord, tailWord_2959728, baseEnd_2959728] using wordTrace_append hprefix tailTrace_2959728
  have hstable : (prefixWord ++ tailWord_2959728).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2959728).length < 2 ^ (prefixWord ++ tailWord_2959728).sum := by decide
  have hdescent : baseEnd_2959728 < baseStart_2959728 := by decide
  rcases family_descends (prefixWord ++ tailWord_2959728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2959747 : List Nat := [1, 1, 1, 3, 6, 2, 1, 2, 1, 4]
def baseStart_2959747 : Nat := 118140960795 + 2959747 * 2 ^ 59
def prefixEnd_2959747 : Nat := 4983230072969 + 3 ^ 40 * 2959747 * 2
def baseEnd_2959747 : Nat := 1013181884468624473300585

theorem tailTrace_2959747 : CollatzResearch.WordTrace tailWord_2959747 prefixEnd_2959747 1013181884468624473300585 := by
  unfold tailWord_2959747
  simp only [CollatzResearch.WordTrace]
  refine ⟨107950841608349578389029495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71967227738899718926019663 107950841608349578389029495)
  ·
    refine ⟨161926262412524367583544243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107950841608349578389029495 161926262412524367583544243)
    ·
      refine ⟨242889393618786551375316365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 161926262412524367583544243 242889393618786551375316365)
      ·
        refine ⟨91083522607044956765743637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 242889393618786551375316365 91083522607044956765743637)
        ·
          refine ⟨4269540122205232348394233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 91083522607044956765743637 4269540122205232348394233)
          ·
            refine ⟨3202155091653924261295675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4269540122205232348394233 3202155091653924261295675)
            ·
              refine ⟨4803232637480886391943513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3202155091653924261295675 4803232637480886391943513)
              ·
                refine ⟨3602424478110664793957635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4803232637480886391943513 3602424478110664793957635)
                ·
                  refine ⟨5403636717165997190936453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3602424478110664793957635 5403636717165997190936453)
                  ·
                    refine ⟨1013181884468624473300585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5403636717165997190936453 1013181884468624473300585)
                    ·
                      rfl

theorem cell22_2959747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 2, 1, 2, 1, 4].length) (baseStart_2959747 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2959747 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2959747 prefixEnd_2959747 := by exact prefixLift 2959747
  have htrace : WordTrace (prefixWord ++ tailWord_2959747) baseStart_2959747 baseEnd_2959747 := by
    simpa [prefixWord, tailWord_2959747, baseEnd_2959747] using wordTrace_append hprefix tailTrace_2959747
  have hstable : (prefixWord ++ tailWord_2959747).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2959747).length < 2 ^ (prefixWord ++ tailWord_2959747).sum := by decide
  have hdescent : baseEnd_2959747 < baseStart_2959747 := by decide
  rcases family_descends (prefixWord ++ tailWord_2959747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2959764 : List Nat := [2, 4, 2, 1, 3, 1, 3, 1, 1, 4]
def baseStart_2959764 : Nat := 118140960795 + 2959764 * 2 ^ 59
def prefixEnd_2959764 : Nat := 4983230072969 + 3 ^ 40 * 2959764 * 2
def baseEnd_2959764 : Nat := 1013187703916042095625533

theorem tailTrace_2959764 : CollatzResearch.WordTrace tailWord_2959764 prefixEnd_2959764 1013187703916042095625533 := by
  unfold tailWord_2959764
  simp only [CollatzResearch.WordTrace]
  refine ⟨53975730824643995146199173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71967641099525326861598897 53975730824643995146199173)
  ·
    refine ⟨10120449529620749089912345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 53975730824643995146199173 10120449529620749089912345)
    ·
      refine ⟨7590337147215561817434259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10120449529620749089912345 7590337147215561817434259)
      ·
        refine ⟨11385505720823342726151389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7590337147215561817434259 11385505720823342726151389)
        ·
          refine ⟨4269564645308753522306771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11385505720823342726151389 4269564645308753522306771)
          ·
            refine ⟨6404346967963130283460157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4269564645308753522306771 6404346967963130283460157)
            ·
              refine ⟨2401630112986173856297559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6404346967963130283460157 2401630112986173856297559)
              ·
                refine ⟨3602445169479260784446339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2401630112986173856297559 3602445169479260784446339)
                ·
                  refine ⟨5403667754218891176669509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3602445169479260784446339 5403667754218891176669509)
                  ·
                    refine ⟨1013187703916042095625533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5403667754218891176669509 1013187703916042095625533)
                    ·
                      rfl

theorem cell22_2959764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 1, 3, 1, 1, 4].length) (baseStart_2959764 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2959764 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2959764 prefixEnd_2959764 := by exact prefixLift 2959764
  have htrace : WordTrace (prefixWord ++ tailWord_2959764) baseStart_2959764 baseEnd_2959764 := by
    simpa [prefixWord, tailWord_2959764, baseEnd_2959764] using wordTrace_append hprefix tailTrace_2959764
  have hstable : (prefixWord ++ tailWord_2959764).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2959764).length < 2 ^ (prefixWord ++ tailWord_2959764).sum := by decide
  have hdescent : baseEnd_2959764 < baseStart_2959764 := by decide
  rcases family_descends (prefixWord ++ tailWord_2959764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2959773 : List Nat := [1, 4, 2, 1, 4, 10]
def baseStart_2959773 : Nat := 118140960795 + 2959773 * 2 ^ 59
def prefixEnd_2959773 : Nat := 4983230072969 + 3 ^ 40 * 2959773 * 2
def baseEnd_2959773 : Nat := 12508528207407025582105

theorem tailTrace_2959773 : CollatzResearch.WordTrace tailWord_2959773 prefixEnd_2959773 12508528207407025582105 := by
  unfold tailWord_2959773
  simp only [CollatzResearch.WordTrace]
  refine ⟨107951789906255384829475973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71967859937503589886317315 107951789906255384829475973)
  ·
    refine ⟨20240960607422884655526745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 107951789906255384829475973 20240960607422884655526745)
    ·
      refine ⟨15180720455567163491645059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20240960607422884655526745 15180720455567163491645059)
      ·
        refine ⟨22771080683350745237467589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15180720455567163491645059 22771080683350745237467589)
        ·
          refine ⟨4269577628128264732025173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22771080683350745237467589 4269577628128264732025173)
          ·
            refine ⟨12508528207407025582105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 4269577628128264732025173 12508528207407025582105)
            ·
              rfl

theorem cell22_2959773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 10].length) (baseStart_2959773 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2959773 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2959773 prefixEnd_2959773 := by exact prefixLift 2959773
  have htrace : WordTrace (prefixWord ++ tailWord_2959773) baseStart_2959773 baseEnd_2959773 := by
    simpa [prefixWord, tailWord_2959773, baseEnd_2959773] using wordTrace_append hprefix tailTrace_2959773
  have hstable : (prefixWord ++ tailWord_2959773).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2959773).length < 2 ^ (prefixWord ++ tailWord_2959773).sum := by decide
  have hdescent : baseEnd_2959773 < baseStart_2959773 := by decide
  rcases family_descends (prefixWord ++ tailWord_2959773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2959805 : List Nat := [1, 4, 1, 2, 2, 2, 1, 1, 5, 3]
def baseStart_2959805 : Nat := 118140960795 + 2959805 * 2 ^ 59
def prefixEnd_2959805 : Nat := 4983230072969 + 3 ^ 40 * 2959805 * 2
def baseEnd_2959805 : Nat := 1013201739053931655350407

theorem tailTrace_2959805 : CollatzResearch.WordTrace tailWord_2959805 prefixEnd_2959805 1013201739053931655350407 := by
  unfold tailWord_2959805
  simp only [CollatzResearch.WordTrace]
  refine ⟨107952957042139454294640869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71968638028092969529760579 107952957042139454294640869)
  ·
    refine ⟨20241179445401147680245163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 107952957042139454294640869 20241179445401147680245163)
    ·
      refine ⟨30361769168101721520367745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20241179445401147680245163 30361769168101721520367745)
      ·
        refine ⟨22771326876076291140275809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30361769168101721520367745 22771326876076291140275809)
        ·
          refine ⟨17078495157057218355206857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22771326876076291140275809 17078495157057218355206857)
          ·
            refine ⟨12808871367792913766405143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17078495157057218355206857 12808871367792913766405143)
            ·
              refine ⟨19213307051689370649607715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12808871367792913766405143 19213307051689370649607715)
              ·
                refine ⟨28819960577534055974411573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19213307051689370649607715 28819960577534055974411573)
                ·
                  refine ⟨2701871304143817747601085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 28819960577534055974411573 2701871304143817747601085)
                  ·
                    refine ⟨1013201739053931655350407, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2701871304143817747601085 1013201739053931655350407)
                    ·
                      rfl

theorem cell22_2959805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 1, 1, 5, 3].length) (baseStart_2959805 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2959805 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2959805 prefixEnd_2959805 := by exact prefixLift 2959805
  have htrace : WordTrace (prefixWord ++ tailWord_2959805) baseStart_2959805 baseEnd_2959805 := by
    simpa [prefixWord, tailWord_2959805, baseEnd_2959805] using wordTrace_append hprefix tailTrace_2959805
  have hstable : (prefixWord ++ tailWord_2959805).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2959805).length < 2 ^ (prefixWord ++ tailWord_2959805).sum := by decide
  have hdescent : baseEnd_2959805 < baseStart_2959805 := by decide
  rcases family_descends (prefixWord ++ tailWord_2959805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2959809 : List Nat := [1, 2, 7, 1, 1, 1, 1, 1, 1, 6]
def baseStart_2959809 : Nat := 118140960795 + 2959809 * 2 ^ 59
def prefixEnd_2959809 : Nat := 4983230072969 + 3 ^ 40 * 2959809 * 2
def baseEnd_2959809 : Nat := 1013203108335676978250395

theorem tailTrace_2959809 : CollatzResearch.WordTrace tailWord_2959809 prefixEnd_2959809 1013203108335676978250395 := by
  unfold tailWord_2959809
  simp only [CollatzResearch.WordTrace]
  refine ⟨107953102934124962977786481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71968735289416641985190987 107953102934124962977786481)
  ·
    refine ⟨80964827200593722233339861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107953102934124962977786481 80964827200593722233339861)
    ·
      refine ⟨1897613137513915364843903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 80964827200593722233339861 1897613137513915364843903)
      ·
        refine ⟨2846419706270873047265855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1897613137513915364843903 2846419706270873047265855)
        ·
          refine ⟨4269629559406309570898783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2846419706270873047265855 4269629559406309570898783)
          ·
            refine ⟨6404444339109464356348175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4269629559406309570898783 6404444339109464356348175)
            ·
              refine ⟨9606666508664196534522263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6404444339109464356348175 9606666508664196534522263)
              ·
                refine ⟨14409999762996294801783395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9606666508664196534522263 14409999762996294801783395)
                ·
                  refine ⟨21614999644494442202675093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14409999762996294801783395 21614999644494442202675093)
                  ·
                    refine ⟨1013203108335676978250395, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21614999644494442202675093 1013203108335676978250395)
                    ·
                      rfl

theorem cell22_2959809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 1, 1, 1, 1, 6].length) (baseStart_2959809 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2959809 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2959809 prefixEnd_2959809 := by exact prefixLift 2959809
  have htrace : WordTrace (prefixWord ++ tailWord_2959809) baseStart_2959809 baseEnd_2959809 := by
    simpa [prefixWord, tailWord_2959809, baseEnd_2959809] using wordTrace_append hprefix tailTrace_2959809
  have hstable : (prefixWord ++ tailWord_2959809).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2959809).length < 2 ^ (prefixWord ++ tailWord_2959809).sum := by decide
  have hdescent : baseEnd_2959809 < baseStart_2959809 := by decide
  rcases family_descends (prefixWord ++ tailWord_2959809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2959818 : List Nat := [3, 1, 2, 1, 2, 2, 2, 2, 7]
def baseStart_2959818 : Nat := 118140960795 + 2959818 * 2 ^ 59
def prefixEnd_2959818 : Nat := 4983230072969 + 3 ^ 40 * 2959818 * 2
def baseEnd_2959818 : Nat := 337735396406534651591789

theorem tailTrace_2959818 : CollatzResearch.WordTrace tailWord_2959818 prefixEnd_2959818 337735396406534651591789 := by
  unfold tailWord_2959818
  simp only [CollatzResearch.WordTrace]
  refine ⟨26988357797773089378716027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71968954127394905009909405 26988357797773089378716027)
  ·
    refine ⟨40482536696659634068074041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26988357797773089378716027 40482536696659634068074041)
    ·
      refine ⟨30361902522494725551055531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40482536696659634068074041 30361902522494725551055531)
      ·
        refine ⟨45542853783742088326583297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30361902522494725551055531 45542853783742088326583297)
        ·
          refine ⟨34157140337806566244937473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45542853783742088326583297 34157140337806566244937473)
          ·
            refine ⟨25617855253354924683703105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34157140337806566244937473 25617855253354924683703105)
            ·
              refine ⟨19213391440016193512777329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25617855253354924683703105 19213391440016193512777329)
              ·
                refine ⟨14410043580012145134582997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19213391440016193512777329 14410043580012145134582997)
                ·
                  refine ⟨337735396406534651591789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14410043580012145134582997 337735396406534651591789)
                  ·
                    rfl

theorem cell22_2959818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 2, 2, 7].length) (baseStart_2959818 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2959818 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2959818 prefixEnd_2959818 := by exact prefixLift 2959818
  have htrace : WordTrace (prefixWord ++ tailWord_2959818) baseStart_2959818 baseEnd_2959818 := by
    simpa [prefixWord, tailWord_2959818, baseEnd_2959818] using wordTrace_append hprefix tailTrace_2959818
  have hstable : (prefixWord ++ tailWord_2959818).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2959818).length < 2 ^ (prefixWord ++ tailWord_2959818).sum := by decide
  have hdescent : baseEnd_2959818 < baseStart_2959818 := by decide
  rcases family_descends (prefixWord ++ tailWord_2959818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2959833 : List Nat := [1, 2, 1, 2, 4, 1, 1, 1, 4, 5]
def baseStart_2959833 : Nat := 118140960795 + 2959833 * 2 ^ 59
def prefixEnd_2959833 : Nat := 4983230072969 + 3 ^ 40 * 2959833 * 2
def baseEnd_2959833 : Nat := 1013211324026148915650321

theorem tailTrace_2959833 : CollatzResearch.WordTrace tailWord_2959833 prefixEnd_2959833 1013211324026148915650321 := by
  unfold tailWord_2959833
  simp only [CollatzResearch.WordTrace]
  refine ⟨107953978286038015076660153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71969318857358676717773435 107953978286038015076660153)
  ·
    refine ⟨80965483714528511307495115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107953978286038015076660153 80965483714528511307495115)
    ·
      refine ⟨121448225571792766961242673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80965483714528511307495115 121448225571792766961242673)
      ·
        refine ⟨91086169178844575220932005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 121448225571792766961242673 91086169178844575220932005)
        ·
          refine ⟨17078656721033357853924751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 91086169178844575220932005 17078656721033357853924751)
          ·
            refine ⟨25617985081550036780887127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17078656721033357853924751 25617985081550036780887127)
            ·
              refine ⟨38426977622325055171330691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25617985081550036780887127 38426977622325055171330691)
              ·
                refine ⟨57640466433487582756996037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38426977622325055171330691 57640466433487582756996037)
                ·
                  refine ⟨10807587456278921766936757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 57640466433487582756996037 10807587456278921766936757)
                  ·
                    refine ⟨1013211324026148915650321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10807587456278921766936757 1013211324026148915650321)
                    ·
                      rfl

theorem cell22_2959833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 1, 1, 4, 5].length) (baseStart_2959833 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2959833 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2959833 prefixEnd_2959833 := by exact prefixLift 2959833
  have htrace : WordTrace (prefixWord ++ tailWord_2959833) baseStart_2959833 baseEnd_2959833 := by
    simpa [prefixWord, tailWord_2959833, baseEnd_2959833] using wordTrace_append hprefix tailTrace_2959833
  have hstable : (prefixWord ++ tailWord_2959833).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2959833).length < 2 ^ (prefixWord ++ tailWord_2959833).sum := by decide
  have hdescent : baseEnd_2959833 < baseStart_2959833 := by decide
  rcases family_descends (prefixWord ++ tailWord_2959833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2959850 : List Nat := [3, 1, 3, 1, 3, 1, 2, 1, 2, 5]
def baseStart_2959850 : Nat := 118140960795 + 2959850 * 2 ^ 59
def prefixEnd_2959850 : Nat := 4983230072969 + 3 ^ 40 * 2959850 * 2
def baseEnd_2959850 : Nat := 1013217143473566537975269

theorem tailTrace_2959850 : CollatzResearch.WordTrace tailWord_2959850 prefixEnd_2959850 1013217143473566537975269 := by
  unfold tailWord_2959850
  simp only [CollatzResearch.WordTrace]
  refine ⟨26988649581744106745007251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71969732217984284653352669 26988649581744106745007251)
  ·
    refine ⟨40482974372616160117510877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26988649581744106745007251 40482974372616160117510877)
    ·
      refine ⟨15181115389731060044066579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40482974372616160117510877 15181115389731060044066579)
      ·
        refine ⟨22771673084596590066099869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15181115389731060044066579 22771673084596590066099869)
        ·
          refine ⟨8539377406723721274787451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22771673084596590066099869 8539377406723721274787451)
          ·
            refine ⟨12809066110085581912181177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8539377406723721274787451 12809066110085581912181177)
            ·
              refine ⟨9606799582564186434135883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12809066110085581912181177 9606799582564186434135883)
              ·
                refine ⟨14410199373846279651203825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9606799582564186434135883 14410199373846279651203825)
                ·
                  refine ⟨10807649530384709738402869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14410199373846279651203825 10807649530384709738402869)
                  ·
                    refine ⟨1013217143473566537975269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10807649530384709738402869 1013217143473566537975269)
                    ·
                      rfl

theorem cell22_2959850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 2, 1, 2, 5].length) (baseStart_2959850 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2959850 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2959850 prefixEnd_2959850 := by exact prefixLift 2959850
  have htrace : WordTrace (prefixWord ++ tailWord_2959850) baseStart_2959850 baseEnd_2959850 := by
    simpa [prefixWord, tailWord_2959850, baseEnd_2959850] using wordTrace_append hprefix tailTrace_2959850
  have hstable : (prefixWord ++ tailWord_2959850).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2959850).length < 2 ^ (prefixWord ++ tailWord_2959850).sum := by decide
  have hdescent : baseEnd_2959850 < baseStart_2959850 := by decide
  rcases family_descends (prefixWord ++ tailWord_2959850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2959865 : List Nat := [1, 2, 1, 3, 1, 2, 3, 4, 1, 4]
def baseStart_2959865 : Nat := 118140960795 + 2959865 * 2 ^ 59
def prefixEnd_2959865 : Nat := 4983230072969 + 3 ^ 40 * 2959865 * 2
def baseEnd_2959865 : Nat := 1013222278280111498850223

theorem tailTrace_2959865 : CollatzResearch.WordTrace tailWord_2959865 prefixEnd_2959865 1013222278280111498850223 := by
  unfold tailWord_2959865
  simp only [CollatzResearch.WordTrace]
  refine ⟨107955145421922084541825049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71970096947948056361216699 107955145421922084541825049)
  ·
    refine ⟨80966359066441563406368787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107955145421922084541825049 80966359066441563406368787)
    ·
      refine ⟨121449538599662345109553181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80966359066441563406368787 121449538599662345109553181)
      ·
        refine ⟨45543576974873379416082443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 121449538599662345109553181 45543576974873379416082443)
        ·
          refine ⟨68315365462310069124123665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45543576974873379416082443 68315365462310069124123665)
          ·
            refine ⟨51236524096732551843092749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 68315365462310069124123665 51236524096732551843092749)
            ·
              refine ⟨19213696536274706941159781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 51236524096732551843092749 19213696536274706941159781)
              ·
                refine ⟨3602568100551507551467459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19213696536274706941159781 3602568100551507551467459)
                ·
                  refine ⟨5403852150827261327201189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3602568100551507551467459 5403852150827261327201189)
                  ·
                    refine ⟨1013222278280111498850223, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5403852150827261327201189 1013222278280111498850223)
                    ·
                      rfl

theorem cell22_2959865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 3, 4, 1, 4].length) (baseStart_2959865 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2959865 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2959865 prefixEnd_2959865 := by exact prefixLift 2959865
  have htrace : WordTrace (prefixWord ++ tailWord_2959865) baseStart_2959865 baseEnd_2959865 := by
    simpa [prefixWord, tailWord_2959865, baseEnd_2959865] using wordTrace_append hprefix tailTrace_2959865
  have hstable : (prefixWord ++ tailWord_2959865).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2959865).length < 2 ^ (prefixWord ++ tailWord_2959865).sum := by decide
  have hdescent : baseEnd_2959865 < baseStart_2959865 := by decide
  rcases family_descends (prefixWord ++ tailWord_2959865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2959942 : List Nat := [6, 1, 1, 1, 2, 11]
def baseStart_2959942 : Nat := 118140960795 + 2959942 * 2 ^ 59
def prefixEnd_2959942 : Nat := 4983230072969 + 3 ^ 40 * 2959942 * 2
def baseEnd_2959942 : Nat := 12509242431527271168827

theorem tailTrace_2959942 : CollatzResearch.WordTrace tailWord_2959942 prefixEnd_2959942 12509242431527271168827 := by
  unfold tailWord_2959942
  simp only [CollatzResearch.WordTrace]
  refine ⟨3373686057582597709136815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 71971969228428751128252053 3373686057582597709136815)
  ·
    refine ⟨5060529086373896563705223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3373686057582597709136815 5060529086373896563705223)
    ·
      refine ⟨7590793629560844845557835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5060529086373896563705223 7590793629560844845557835)
      ·
        refine ⟨11386190444341267268336753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7590793629560844845557835 11386190444341267268336753)
        ·
          refine ⟨8539642833255950451252565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11386190444341267268336753 8539642833255950451252565)
          ·
            refine ⟨12509242431527271168827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 8539642833255950451252565 12509242431527271168827)
            ·
              rfl

theorem cell22_2959942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 11].length) (baseStart_2959942 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2959942 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2959942 prefixEnd_2959942 := by exact prefixLift 2959942
  have htrace : WordTrace (prefixWord ++ tailWord_2959942) baseStart_2959942 baseEnd_2959942 := by
    simpa [prefixWord, tailWord_2959942, baseEnd_2959942] using wordTrace_append hprefix tailTrace_2959942
  have hstable : (prefixWord ++ tailWord_2959942).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2959942).length < 2 ^ (prefixWord ++ tailWord_2959942).sum := by decide
  have hdescent : baseEnd_2959942 < baseStart_2959942 := by decide
  rcases family_descends (prefixWord ++ tailWord_2959942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2960004 : List Nat := [2, 3, 2, 1, 3, 3, 1, 2, 5]
def baseStart_2960004 : Nat := 118140960795 + 2960004 * 2 ^ 59
def prefixEnd_2960004 : Nat := 4983230072969 + 3 ^ 40 * 2960004 * 2
def baseEnd_2960004 : Nat := 337756620273587156541599

theorem tailTrace_2960004 : CollatzResearch.WordTrace tailWord_2960004 prefixEnd_2960004 337756620273587156541599 := by
  unfold tailWord_2960004
  simp only [CollatzResearch.WordTrace]
  refine ⟨53980107584209255640567533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71973476778945674187423377 53980107584209255640567533)
  ·
    refine ⟨20242540344078470865212825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53980107584209255640567533 20242540344078470865212825)
    ·
      refine ⟨15181905258058853148909619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20242540344078470865212825 15181905258058853148909619)
      ·
        refine ⟨22772857887088279723364429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15181905258058853148909619 22772857887088279723364429)
        ·
          refine ⟨8539821707658104896261661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22772857887088279723364429 8539821707658104896261661)
          ·
            refine ⟨3202433140371789336098123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8539821707658104896261661 3202433140371789336098123)
            ·
              refine ⟨4803649710557684004147185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3202433140371789336098123 4803649710557684004147185)
              ·
                refine ⟨3602737282918263003110389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4803649710557684004147185 3602737282918263003110389)
                ·
                  refine ⟨337756620273587156541599, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3602737282918263003110389 337756620273587156541599)
                  ·
                    rfl

theorem cell22_2960004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 3, 1, 2, 5].length) (baseStart_2960004 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2960004 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2960004 prefixEnd_2960004 := by exact prefixLift 2960004
  have htrace : WordTrace (prefixWord ++ tailWord_2960004) baseStart_2960004 baseEnd_2960004 := by
    simpa [prefixWord, tailWord_2960004, baseEnd_2960004] using wordTrace_append hprefix tailTrace_2960004
  have hstable : (prefixWord ++ tailWord_2960004).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2960004).length < 2 ^ (prefixWord ++ tailWord_2960004).sum := by decide
  have hdescent : baseEnd_2960004 < baseStart_2960004 := by decide
  rcases family_descends (prefixWord ++ tailWord_2960004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2960042 : List Nat := [3, 1, 5, 2, 2, 1, 1, 3, 1, 3]
def baseStart_2960042 : Nat := 118140960795 + 2960042 * 2 ^ 59
def prefixEnd_2960042 : Nat := 4983230072969 + 3 ^ 40 * 2960042 * 2
def baseEnd_2960042 : Nat := 1013282868997342037174681

theorem tailTrace_2960042 : CollatzResearch.WordTrace tailWord_2960042 prefixEnd_2960042 1013282868997342037174681 := by
  unfold tailWord_2960042
  simp only [CollatzResearch.WordTrace]
  refine ⟨26990400285570210942754595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71974400761520562514012253 26990400285570210942754595)
  ·
    refine ⟨40485600428355316414131893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26990400285570210942754595 40485600428355316414131893)
    ·
      refine ⟨3795525040158310913824865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 40485600428355316414131893 3795525040158310913824865)
      ·
        refine ⟨2846643780118733185368649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3795525040158310913824865 2846643780118733185368649)
        ·
          refine ⟨2134982835089049889026487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2846643780118733185368649 2134982835089049889026487)
          ·
            refine ⟨3202474252633574833539731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2134982835089049889026487 3202474252633574833539731)
            ·
              refine ⟨4803711378950362250309597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3202474252633574833539731 4803711378950362250309597)
              ·
                refine ⟨1801391767106385843866099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4803711378950362250309597 1801391767106385843866099)
                ·
                  refine ⟨2702087650659578765799149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1801391767106385843866099 2702087650659578765799149)
                  ·
                    refine ⟨1013282868997342037174681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2702087650659578765799149 1013282868997342037174681)
                    ·
                      rfl

theorem cell22_2960042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 2, 1, 1, 3, 1, 3].length) (baseStart_2960042 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2960042 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2960042 prefixEnd_2960042 := by exact prefixLift 2960042
  have htrace : WordTrace (prefixWord ++ tailWord_2960042) baseStart_2960042 baseEnd_2960042 := by
    simpa [prefixWord, tailWord_2960042, baseEnd_2960042] using wordTrace_append hprefix tailTrace_2960042
  have hstable : (prefixWord ++ tailWord_2960042).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2960042).length < 2 ^ (prefixWord ++ tailWord_2960042).sum := by decide
  have hdescent : baseEnd_2960042 < baseStart_2960042 := by decide
  rcases family_descends (prefixWord ++ tailWord_2960042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2960047 : List Nat := [1, 1, 2, 1, 2, 5, 1, 2, 4, 3]
def baseStart_2960047 : Nat := 118140960795 + 2960047 * 2 ^ 59
def prefixEnd_2960047 : Nat := 4983230072969 + 3 ^ 40 * 2960047 * 2
def baseEnd_2960047 : Nat := 1013284580599523690799665

theorem tailTrace_2960047 : CollatzResearch.WordTrace tailWord_2960047 prefixEnd_2960047 1013284580599523690799665 := by
  unfold tailWord_2960047
  simp only [CollatzResearch.WordTrace]
  refine ⟨107961783507262729624950395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71974522338175153083300263 107961783507262729624950395)
  ·
    refine ⟨161942675260894094437425593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107961783507262729624950395 161942675260894094437425593)
    ·
      refine ⟨121457006445670570828069195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 161942675260894094437425593 121457006445670570828069195)
      ·
        refine ⟨182185509668505856242103793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121457006445670570828069195 182185509668505856242103793)
        ·
          refine ⟨136639132251379392181577845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 182185509668505856242103793 136639132251379392181577845)
          ·
            refine ⟨12809918648566818017022923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 136639132251379392181577845 12809918648566818017022923)
            ·
              refine ⟨19214877972850227025534385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12809918648566818017022923 19214877972850227025534385)
              ·
                refine ⟨14411158479637670269150789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19214877972850227025534385 14411158479637670269150789)
                ·
                  refine ⟨2702092214932063175465773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14411158479637670269150789 2702092214932063175465773)
                  ·
                    refine ⟨1013284580599523690799665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2702092214932063175465773 1013284580599523690799665)
                    ·
                      rfl

theorem cell22_2960047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 1, 2, 4, 3].length) (baseStart_2960047 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2960047 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2960047 prefixEnd_2960047 := by exact prefixLift 2960047
  have htrace : WordTrace (prefixWord ++ tailWord_2960047) baseStart_2960047 baseEnd_2960047 := by
    simpa [prefixWord, tailWord_2960047, baseEnd_2960047] using wordTrace_append hprefix tailTrace_2960047
  have hstable : (prefixWord ++ tailWord_2960047).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2960047).length < 2 ^ (prefixWord ++ tailWord_2960047).sum := by decide
  have hdescent : baseEnd_2960047 < baseStart_2960047 := by decide
  rcases family_descends (prefixWord ++ tailWord_2960047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2960105 : List Nat := [1, 2, 1, 1, 1, 2, 4, 1, 9]
def baseStart_2960105 : Nat := 118140960795 + 2960105 * 2 ^ 59
def prefixEnd_2960105 : Nat := 4983230072969 + 3 ^ 40 * 2960105 * 2
def baseEnd_2960105 : Nat := 337768145061610290949829

theorem tailTrace_2960105 : CollatzResearch.WordTrace tailWord_2960105 prefixEnd_2960105 337768145061610290949829 := by
  unfold tailWord_2960105
  simp only [CollatzResearch.WordTrace]
  refine ⟨107963898941052605530561769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71975932627368403687041179 107963898941052605530561769)
  ·
    refine ⟨80972924205789454147921327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107963898941052605530561769 80972924205789454147921327)
    ·
      refine ⟨121459386308684181221881991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80972924205789454147921327 121459386308684181221881991)
      ·
        refine ⟨182189079463026271832822987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121459386308684181221881991 182189079463026271832822987)
        ·
          refine ⟨273283619194539407749234481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 182189079463026271832822987 273283619194539407749234481)
          ·
            refine ⟨204962714395904555811925861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 273283619194539407749234481 204962714395904555811925861)
            ·
              refine ⟨38430508949232104214736099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 204962714395904555811925861 38430508949232104214736099)
              ·
                refine ⟨57645763423848156322104149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38430508949232104214736099 57645763423848156322104149)
                ·
                  refine ⟨337768145061610290949829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 57645763423848156322104149 337768145061610290949829)
                  ·
                    rfl

theorem cell22_2960105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 4, 1, 9].length) (baseStart_2960105 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2960105 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2960105 prefixEnd_2960105 := by exact prefixLift 2960105
  have htrace : WordTrace (prefixWord ++ tailWord_2960105) baseStart_2960105 baseEnd_2960105 := by
    simpa [prefixWord, tailWord_2960105, baseEnd_2960105] using wordTrace_append hprefix tailTrace_2960105
  have hstable : (prefixWord ++ tailWord_2960105).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2960105).length < 2 ^ (prefixWord ++ tailWord_2960105).sum := by decide
  have hdescent : baseEnd_2960105 < baseStart_2960105 := by decide
  rcases family_descends (prefixWord ++ tailWord_2960105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2960117 : List Nat := [1, 3, 6, 1, 1, 2, 2, 2, 4]
def baseStart_2960117 : Nat := 118140960795 + 2960117 * 2 ^ 59
def prefixEnd_2960117 : Nat := 4983230072969 + 3 ^ 40 * 2960117 * 2
def baseEnd_2960117 : Nat := 337769514343355613849817

theorem tailTrace_2960117 : CollatzResearch.WordTrace tailWord_2960117 prefixEnd_2960117 337769514343355613849817 := by
  unfold tailWord_2960117
  simp only [CollatzResearch.WordTrace]
  refine ⟨107964336617009131579998605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71976224411339421053332403 107964336617009131579998605)
  ·
    refine ⟨40486626231378424342499477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 107964336617009131579998605 40486626231378424342499477)
    ·
      refine ⟨1897810604595863641054663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 40486626231378424342499477 1897810604595863641054663)
      ·
        refine ⟨2846715906893795461581995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1897810604595863641054663 2846715906893795461581995)
        ·
          refine ⟨4270073860340693192372993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2846715906893795461581995 4270073860340693192372993)
          ·
            refine ⟨3202555395255519894279745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4270073860340693192372993 3202555395255519894279745)
            ·
              refine ⟨2401916546441639920709809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3202555395255519894279745 2401916546441639920709809)
              ·
                refine ⟨1801437409831229940532357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2401916546441639920709809 1801437409831229940532357)
                ·
                  refine ⟨337769514343355613849817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1801437409831229940532357 337769514343355613849817)
                  ·
                    rfl

theorem cell22_2960117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 2, 2, 2, 4].length) (baseStart_2960117 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2960117 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2960117 prefixEnd_2960117 := by exact prefixLift 2960117
  have htrace : WordTrace (prefixWord ++ tailWord_2960117) baseStart_2960117 baseEnd_2960117 := by
    simpa [prefixWord, tailWord_2960117, baseEnd_2960117] using wordTrace_append hprefix tailTrace_2960117
  have hstable : (prefixWord ++ tailWord_2960117).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2960117).length < 2 ^ (prefixWord ++ tailWord_2960117).sum := by decide
  have hdescent : baseEnd_2960117 < baseStart_2960117 := by decide
  rcases family_descends (prefixWord ++ tailWord_2960117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2960122 : List Nat := [3, 1, 1, 1, 1, 3, 3, 4, 5]
def baseStart_2960122 : Nat := 118140960795 + 2960122 * 2 ^ 59
def prefixEnd_2960122 : Nat := 4983230072969 + 3 ^ 40 * 2960122 * 2
def baseEnd_2960122 : Nat := 337770084877416165058145

theorem tailTrace_2960122 : CollatzResearch.WordTrace tailWord_2960122 prefixEnd_2960122 337770084877416165058145 := by
  unfold tailWord_2960122
  simp only [CollatzResearch.WordTrace]
  refine ⟨26991129745497754358482655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71976345987994011622620413 26991129745497754358482655)
  ·
    refine ⟨40486694618246631537723983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26991129745497754358482655 40486694618246631537723983)
    ·
      refine ⟨60730041927369947306585975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40486694618246631537723983 60730041927369947306585975)
      ·
        refine ⟨91095062891054920959878963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60730041927369947306585975 91095062891054920959878963)
        ·
          refine ⟨136642594336582381439818445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91095062891054920959878963 136642594336582381439818445)
          ·
            refine ⟨51240972876218393039931917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 136642594336582381439818445 51240972876218393039931917)
            ·
              refine ⟨19215364828581897389974469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 51240972876218393039931917 19215364828581897389974469)
              ·
                refine ⟨3602880905359105760620213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19215364828581897389974469 3602880905359105760620213)
                ·
                  refine ⟨337770084877416165058145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3602880905359105760620213 337770084877416165058145)
                  ·
                    rfl

theorem cell22_2960122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 3, 4, 5].length) (baseStart_2960122 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2960122 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2960122 prefixEnd_2960122 := by exact prefixLift 2960122
  have htrace : WordTrace (prefixWord ++ tailWord_2960122) baseStart_2960122 baseEnd_2960122 := by
    simpa [prefixWord, tailWord_2960122, baseEnd_2960122] using wordTrace_append hprefix tailTrace_2960122
  have hstable : (prefixWord ++ tailWord_2960122).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2960122).length < 2 ^ (prefixWord ++ tailWord_2960122).sum := by decide
  have hdescent : baseEnd_2960122 < baseStart_2960122 := by decide
  rcases family_descends (prefixWord ++ tailWord_2960122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2960184 : List Nat := [2, 1, 2, 1, 3, 2, 1, 6, 4]
def baseStart_2960184 : Nat := 118140960795 + 2960184 * 2 ^ 59
def prefixEnd_2960184 : Nat := 4983230072969 + 3 ^ 40 * 2960184 * 2
def baseEnd_2960184 : Nat := 337777159499767000041415

theorem tailTrace_2960184 : CollatzResearch.WordTrace tailWord_2960184 prefixEnd_2960184 337777159499767000041415 := by
  unfold tailWord_2960184
  simp only [CollatzResearch.WordTrace]
  refine ⟨53983390153883201011343803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71977853538510934681791737 53983390153883201011343803)
  ·
    refine ⟨80975085230824801517015705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53983390153883201011343803 80975085230824801517015705)
    ·
      refine ⟨60731313923118601137761779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80975085230824801517015705 60731313923118601137761779)
      ·
        refine ⟨91096970884677901706642669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60731313923118601137761779 91096970884677901706642669)
        ·
          refine ⟨34161364081754213139991001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 91096970884677901706642669 34161364081754213139991001)
          ·
            refine ⟨25621023061315659854993251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34161364081754213139991001 25621023061315659854993251)
            ·
              refine ⟨38431534591973489782489877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25621023061315659854993251 38431534591973489782489877)
              ·
                refine ⟨1801478183998757333554213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 38431534591973489782489877 1801478183998757333554213)
                ·
                  refine ⟨337777159499767000041415, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1801478183998757333554213 337777159499767000041415)
                  ·
                    rfl

theorem cell22_2960184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 1, 6, 4].length) (baseStart_2960184 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2960184 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2960184 prefixEnd_2960184 := by exact prefixLift 2960184
  have htrace : WordTrace (prefixWord ++ tailWord_2960184) baseStart_2960184 baseEnd_2960184 := by
    simpa [prefixWord, tailWord_2960184, baseEnd_2960184] using wordTrace_append hprefix tailTrace_2960184
  have hstable : (prefixWord ++ tailWord_2960184).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2960184).length < 2 ^ (prefixWord ++ tailWord_2960184).sum := by decide
  have hdescent : baseEnd_2960184 < baseStart_2960184 := by decide
  rcases family_descends (prefixWord ++ tailWord_2960184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2960197 : List Nat := [1, 3, 1, 1, 1, 2, 2, 1, 6, 4]
def baseStart_2960197 : Nat := 118140960795 + 2960197 * 2 ^ 59
def prefixEnd_2960197 : Nat := 4983230072969 + 3 ^ 40 * 2960197 * 2
def baseEnd_2960197 : Nat := 1013335928664973299549205

theorem tailTrace_2960197 : CollatzResearch.WordTrace tailWord_2960197 prefixEnd_2960197 1013335928664973299549205 := by
  unfold tailWord_2960197
  simp only [CollatzResearch.WordTrace]
  refine ⟨107967254456719305242910845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71978169637812870161940563 107967254456719305242910845)
  ·
    refine ⟨40487720421269739466091567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 107967254456719305242910845 40487720421269739466091567)
    ·
      refine ⟨60731580631904609199137351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40487720421269739466091567 60731580631904609199137351)
      ·
        refine ⟨91097370947856913798706027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60731580631904609199137351 91097370947856913798706027)
        ·
          refine ⟨136646056421785370698059041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91097370947856913798706027 136646056421785370698059041)
          ·
            refine ⟨102484542316339028023544281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 136646056421785370698059041 102484542316339028023544281)
            ·
              refine ⟨76863406737254271017658211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 102484542316339028023544281 76863406737254271017658211)
              ·
                refine ⟨115295110105881406526487317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 76863406737254271017658211 115295110105881406526487317)
                ·
                  refine ⟨5404458286213190930929093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 115295110105881406526487317 5404458286213190930929093)
                  ·
                    refine ⟨1013335928664973299549205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5404458286213190930929093 1013335928664973299549205)
                    ·
                      rfl

theorem cell22_2960197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 1, 6, 4].length) (baseStart_2960197 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2960197 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2960197 prefixEnd_2960197 := by exact prefixLift 2960197
  have htrace : WordTrace (prefixWord ++ tailWord_2960197) baseStart_2960197 baseEnd_2960197 := by
    simpa [prefixWord, tailWord_2960197, baseEnd_2960197] using wordTrace_append hprefix tailTrace_2960197
  have hstable : (prefixWord ++ tailWord_2960197).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2960197).length < 2 ^ (prefixWord ++ tailWord_2960197).sum := by decide
  have hdescent : baseEnd_2960197 < baseStart_2960197 := by decide
  rcases family_descends (prefixWord ++ tailWord_2960197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2960246 : List Nat := [5, 1, 1, 3, 1, 2, 2, 7]
def baseStart_2960246 : Nat := 118140960795 + 2960246 * 2 ^ 59
def prefixEnd_2960246 : Nat := 4983230072969 + 3 ^ 40 * 2960246 * 2
def baseEnd_2960246 : Nat := 112594744707372611674895

theorem tailTrace_2960246 : CollatzResearch.WordTrace tailWord_2960246 prefixEnd_2960246 112594744707372611674895 := by
  unfold tailWord_2960246
  simp only [CollatzResearch.WordTrace]
  refine ⟨6748065102096361663215287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 71979361089027857740963061 6748065102096361663215287)
  ·
    refine ⟨10122097653144542494822931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6748065102096361663215287 10122097653144542494822931)
    ·
      refine ⟨15183146479716813742234397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10122097653144542494822931 15183146479716813742234397)
      ·
        refine ⟨5693679929893805153337899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15183146479716813742234397 5693679929893805153337899)
        ·
          refine ⟨8540519894840707730006849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5693679929893805153337899 8540519894840707730006849)
          ·
            refine ⟨6405389921130530797505137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8540519894840707730006849 6405389921130530797505137)
            ·
              refine ⟨4804042440847898098128853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6405389921130530797505137 4804042440847898098128853)
              ·
                refine ⟨112594744707372611674895, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4804042440847898098128853 112594744707372611674895)
                ·
                  rfl

theorem cell22_2960246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 2, 2, 7].length) (baseStart_2960246 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2960246 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2960246 prefixEnd_2960246 := by exact prefixLift 2960246
  have htrace : WordTrace (prefixWord ++ tailWord_2960246) baseStart_2960246 baseEnd_2960246 := by
    simpa [prefixWord, tailWord_2960246, baseEnd_2960246] using wordTrace_append hprefix tailTrace_2960246
  have hstable : (prefixWord ++ tailWord_2960246).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2960246).length < 2 ^ (prefixWord ++ tailWord_2960246).sum := by decide
  have hdescent : baseEnd_2960246 < baseStart_2960246 := by decide
  rcases family_descends (prefixWord ++ tailWord_2960246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2960295 : List Nat := [1, 1, 6, 1, 3, 1, 1, 4, 1, 3]
def baseStart_2960295 : Nat := 118140960795 + 2960295 * 2 ^ 59
def prefixEnd_2960295 : Nat := 4983230072969 + 3 ^ 40 * 2960295 * 2
def baseEnd_2960295 : Nat := 1013369476067733710598905

theorem tailTrace_2960295 : CollatzResearch.WordTrace tailWord_2960295 prefixEnd_2960295 1013369476067733710598905 := by
  unfold tailWord_2960295
  simp only [CollatzResearch.WordTrace]
  refine ⟨107970828810364267979978339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71980552540242845319985559 107970828810364267979978339)
  ·
    refine ⟨161956243215546401969967509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107970828810364267979978339 161956243215546401969967509)
    ·
      refine ⟨7591698900728737592342227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 161956243215546401969967509 7591698900728737592342227)
      ·
        refine ⟨11387548351093106388513341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7591698900728737592342227 11387548351093106388513341)
        ·
          refine ⟨4270330631659914895692503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11387548351093106388513341 4270330631659914895692503)
          ·
            refine ⟨6405495947489872343538755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4270330631659914895692503 6405495947489872343538755)
            ·
              refine ⟨9608243921234808515308133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6405495947489872343538755 9608243921234808515308133)
              ·
                refine ⟨1801545735231526596620275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9608243921234808515308133 1801545735231526596620275)
                ·
                  refine ⟨2702318602847289894930413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1801545735231526596620275 2702318602847289894930413)
                  ·
                    refine ⟨1013369476067733710598905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2702318602847289894930413 1013369476067733710598905)
                    ·
                      rfl

theorem cell22_2960295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 1, 1, 4, 1, 3].length) (baseStart_2960295 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2960295 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2960295 prefixEnd_2960295 := by exact prefixLift 2960295
  have htrace : WordTrace (prefixWord ++ tailWord_2960295) baseStart_2960295 baseEnd_2960295 := by
    simpa [prefixWord, tailWord_2960295, baseEnd_2960295] using wordTrace_append hprefix tailTrace_2960295
  have hstable : (prefixWord ++ tailWord_2960295).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2960295).length < 2 ^ (prefixWord ++ tailWord_2960295).sum := by decide
  have hdescent : baseEnd_2960295 < baseStart_2960295 := by decide
  rcases family_descends (prefixWord ++ tailWord_2960295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2960308 : List Nat := [2, 5, 2, 1, 1, 1, 2, 3, 5]
def baseStart_2960308 : Nat := 118140960795 + 2960308 * 2 ^ 59
def prefixEnd_2960308 : Nat := 4983230072969 + 3 ^ 40 * 2960308 * 2
def baseEnd_2960308 : Nat := 337791308744468670007955

theorem tailTrace_2960308 : CollatzResearch.WordTrace tailWord_2960308 prefixEnd_2960308 337791308744468670007955 := by
  unfold tailWord_2960308
  simp only [CollatzResearch.WordTrace]
  refine ⟨53985651479658585600100789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71980868639544780800134385 53985651479658585600100789)
  ·
    refine ⟨5061154826217992400009449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 53985651479658585600100789 5061154826217992400009449)
    ·
      refine ⟨3795866119663494300007087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5061154826217992400009449 3795866119663494300007087)
      ·
        refine ⟨5693799179495241450010631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3795866119663494300007087 5693799179495241450010631)
        ·
          refine ⟨8540698769242862175015947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5693799179495241450010631 8540698769242862175015947)
          ·
            refine ⟨12811048153864293262523921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8540698769242862175015947 12811048153864293262523921)
            ·
              refine ⟨9608286115398219946892941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12811048153864293262523921 9608286115398219946892941)
              ·
                refine ⟨3603107293274332480084853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9608286115398219946892941 3603107293274332480084853)
                ·
                  refine ⟨337791308744468670007955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3603107293274332480084853 337791308744468670007955)
                  ·
                    rfl

theorem cell22_2960308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 2, 3, 5].length) (baseStart_2960308 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2960308 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2960308 prefixEnd_2960308 := by exact prefixLift 2960308
  have htrace : WordTrace (prefixWord ++ tailWord_2960308) baseStart_2960308 baseEnd_2960308 := by
    simpa [prefixWord, tailWord_2960308, baseEnd_2960308] using wordTrace_append hprefix tailTrace_2960308
  have hstable : (prefixWord ++ tailWord_2960308).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2960308).length < 2 ^ (prefixWord ++ tailWord_2960308).sum := by decide
  have hdescent : baseEnd_2960308 < baseStart_2960308 := by decide
  rcases family_descends (prefixWord ++ tailWord_2960308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2960338 : List Nat := [3, 2, 2, 3, 1, 2, 1, 3, 1, 4]
def baseStart_2960338 : Nat := 118140960795 + 2960338 * 2 ^ 59
def prefixEnd_2960338 : Nat := 4983230072969 + 3 ^ 40 * 2960338 * 2
def baseEnd_2960338 : Nat := 1013384195846495931773773

theorem tailTrace_2960338 : CollatzResearch.WordTrace tailWord_2960338 prefixEnd_2960338 1013384195846495931773773 := by
  unfold tailWord_2960338
  simp only [CollatzResearch.WordTrace]
  refine ⟨26993099287302121580948417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71981598099472324215862445 26993099287302121580948417)
  ·
    refine ⟨20244824465476591185711313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26993099287302121580948417 20244824465476591185711313)
    ·
      refine ⟨15183618349107443389283485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20244824465476591185711313 15183618349107443389283485)
      ·
        refine ⟨5693856880915291270981307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15183618349107443389283485 5693856880915291270981307)
        ·
          refine ⟨8540785321372936906471961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5693856880915291270981307 8540785321372936906471961)
          ·
            refine ⟨6405588991029702679853971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8540785321372936906471961 6405588991029702679853971)
            ·
              refine ⟨9608383486544554019780957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6405588991029702679853971 9608383486544554019780957)
              ·
                refine ⟨3603143807454207757417859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9608383486544554019780957 3603143807454207757417859)
                ·
                  refine ⟨5404715711181311636126789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3603143807454207757417859 5404715711181311636126789)
                  ·
                    refine ⟨1013384195846495931773773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5404715711181311636126789 1013384195846495931773773)
                    ·
                      rfl

theorem cell22_2960338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 2, 1, 3, 1, 4].length) (baseStart_2960338 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2960338 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2960338 prefixEnd_2960338 := by exact prefixLift 2960338
  have htrace : WordTrace (prefixWord ++ tailWord_2960338) baseStart_2960338 baseEnd_2960338 := by
    simpa [prefixWord, tailWord_2960338, baseEnd_2960338] using wordTrace_append hprefix tailTrace_2960338
  have hstable : (prefixWord ++ tailWord_2960338).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2960338).length < 2 ^ (prefixWord ++ tailWord_2960338).sum := by decide
  have hdescent : baseEnd_2960338 < baseStart_2960338 := by decide
  rcases family_descends (prefixWord ++ tailWord_2960338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2960409 : List Nat := [1, 2, 1, 2, 1, 1, 6, 1, 7]
def baseStart_2960409 : Nat := 118140960795 + 2960409 * 2 ^ 59
def prefixEnd_2960409 : Nat := 4983230072969 + 3 ^ 40 * 2960409 * 2
def baseEnd_2960409 : Nat := 337802833532491804416185

theorem tailTrace_2960409 : CollatzResearch.WordTrace tailWord_2960409 prefixEnd_2960409 337802833532491804416185 := by
  unfold tailWord_2960409
  simp only [CollatzResearch.WordTrace]
  refine ⟨107974986731951265449628281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71983324487967510299752187 107974986731951265449628281)
  ·
    refine ⟨80981240048963449087221211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107974986731951265449628281 80981240048963449087221211)
    ·
      refine ⟨121471860073445173630831817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80981240048963449087221211 121471860073445173630831817)
      ·
        refine ⟨91103895055083880223123863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 121471860073445173630831817 91103895055083880223123863)
        ·
          refine ⟨136655842582625820334685795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91103895055083880223123863 136655842582625820334685795)
          ·
            refine ⟨204983763873938730502028693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 136655842582625820334685795 204983763873938730502028693)
            ·
              refine ⟨9608613931590877992282595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 204983763873938730502028693 9608613931590877992282595)
              ·
                refine ⟨14412920897386316988423893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9608613931590877992282595 14412920897386316988423893)
                ·
                  refine ⟨337802833532491804416185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14412920897386316988423893 337802833532491804416185)
                  ·
                    rfl

theorem cell22_2960409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 6, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 6, 1, 7].length) (baseStart_2960409 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2960409 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2960409 prefixEnd_2960409 := by exact prefixLift 2960409
  have htrace : WordTrace (prefixWord ++ tailWord_2960409) baseStart_2960409 baseEnd_2960409 := by
    simpa [prefixWord, tailWord_2960409, baseEnd_2960409] using wordTrace_append hprefix tailTrace_2960409
  have hstable : (prefixWord ++ tailWord_2960409).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2960409).length < 2 ^ (prefixWord ++ tailWord_2960409).sum := by decide
  have hdescent : baseEnd_2960409 < baseStart_2960409 := by decide
  rcases family_descends (prefixWord ++ tailWord_2960409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2960505 : List Nat := [1, 2, 1, 3, 5, 1, 2, 3, 4]
def baseStart_2960505 : Nat := 118140960795 + 2960505 * 2 ^ 59
def prefixEnd_2960505 : Nat := 4983230072969 + 3 ^ 40 * 2960505 * 2
def baseEnd_2960505 : Nat := 337813787786454387616087

theorem tailTrace_2960505 : CollatzResearch.WordTrace tailWord_2960505 prefixEnd_2960505 337813787786454387616087 := by
  unfold tailWord_2960505
  simp only [CollatzResearch.WordTrace]
  refine ⟨107978488139603473845122969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71985658759735649230081979 107978488139603473845122969)
  ·
    refine ⟨80983866104702605383842227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107978488139603473845122969 80983866104702605383842227)
    ·
      refine ⟨121475799157053908075763341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80983866104702605383842227 121475799157053908075763341)
      ·
        refine ⟨45553424683895215528411253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 121475799157053908075763341 45553424683895215528411253)
        ·
          refine ⟨4270633564115176455788555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 45553424683895215528411253 4270633564115176455788555)
          ·
            refine ⟨6405950346172764683682833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4270633564115176455788555 6405950346172764683682833)
            ·
              refine ⟨4804462759629573512762125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6405950346172764683682833 4804462759629573512762125)
              ·
                refine ⟨1801673534861090067285797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4804462759629573512762125 1801673534861090067285797)
                ·
                  refine ⟨337813787786454387616087, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1801673534861090067285797 337813787786454387616087)
                  ·
                    rfl

theorem cell22_2960505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 1, 2, 3, 4].length) (baseStart_2960505 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2960505 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2960505 prefixEnd_2960505 := by exact prefixLift 2960505
  have htrace : WordTrace (prefixWord ++ tailWord_2960505) baseStart_2960505 baseEnd_2960505 := by
    simpa [prefixWord, tailWord_2960505, baseEnd_2960505] using wordTrace_append hprefix tailTrace_2960505
  have hstable : (prefixWord ++ tailWord_2960505).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2960505).length < 2 ^ (prefixWord ++ tailWord_2960505).sum := by decide
  have hdescent : baseEnd_2960505 < baseStart_2960505 := by decide
  rcases family_descends (prefixWord ++ tailWord_2960505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2960516 : List Nat := [2, 3, 2, 1, 2, 3, 9]
def baseStart_2960516 : Nat := 118140960795 + 2960516 * 2 ^ 59
def prefixEnd_2960516 : Nat := 4983230072969 + 3 ^ 40 * 2960516 * 2
def baseEnd_2960516 : Nat := 37535004773487511141601

theorem tailTrace_2960516 : CollatzResearch.WordTrace tailWord_2960516 prefixEnd_2960516 37535004773487511141601 := by
  unfold tailWord_2960516
  simp only [CollatzResearch.WordTrace]
  refine ⟨53989444671281811361886701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71985926228375748482515601 53989444671281811361886701)
  ·
    refine ⟨20246041751730679260707513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53989444671281811361886701 20246041751730679260707513)
    ·
      refine ⟨15184531313798009445530635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20246041751730679260707513 15184531313798009445530635)
      ·
        refine ⟨22776796970697014168295953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15184531313798009445530635 22776796970697014168295953)
        ·
          refine ⟨17082597728022760626221965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22776796970697014168295953 17082597728022760626221965)
          ·
            refine ⟨6405974148008535234833237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17082597728022760626221965 6405974148008535234833237)
            ·
              refine ⟨37535004773487511141601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 6405974148008535234833237 37535004773487511141601)
              ·
                rfl

theorem cell22_2960516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 3, 9].length) (baseStart_2960516 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2960516 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2960516 prefixEnd_2960516 := by exact prefixLift 2960516
  have htrace : WordTrace (prefixWord ++ tailWord_2960516) baseStart_2960516 baseEnd_2960516 := by
    simpa [prefixWord, tailWord_2960516, baseEnd_2960516] using wordTrace_append hprefix tailTrace_2960516
  have hstable : (prefixWord ++ tailWord_2960516).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2960516).length < 2 ^ (prefixWord ++ tailWord_2960516).sum := by decide
  have hdescent : baseEnd_2960516 < baseStart_2960516 := by decide
  rcases family_descends (prefixWord ++ tailWord_2960516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2960520 : List Nat := [2, 1, 3, 4, 2, 1, 1, 1, 4, 3]
def baseStart_2960520 : Nat := 118140960795 + 2960520 * 2 ^ 59
def prefixEnd_2960520 : Nat := 4983230072969 + 3 ^ 40 * 2960520 * 2
def baseEnd_2960520 : Nat := 1013446498165908123723215

theorem tailTrace_2960520 : CollatzResearch.WordTrace tailWord_2960520 prefixEnd_2960520 1013446498165908123723215 := by
  unfold tailWord_2960520
  simp only [CollatzResearch.WordTrace]
  refine ⟨53989517617274565703459507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71986023489699420937946009 53989517617274565703459507)
  ·
    refine ⟨80984276425911848555189261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53989517617274565703459507 80984276425911848555189261)
    ·
      refine ⟨30369103659716943208195973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 80984276425911848555189261 30369103659716943208195973)
      ·
        refine ⟨5694206936196926851536745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 30369103659716943208195973 5694206936196926851536745)
        ·
          refine ⟨4270655202147695138652559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5694206936196926851536745 4270655202147695138652559)
          ·
            refine ⟨6405982803221542707978839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4270655202147695138652559 6405982803221542707978839)
            ·
              refine ⟨9608974204832314061968259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6405982803221542707978839 9608974204832314061968259)
              ·
                refine ⟨14413461307248471092952389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9608974204832314061968259 14413461307248471092952389)
                ·
                  refine ⟨2702523995109088329928573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14413461307248471092952389 2702523995109088329928573)
                  ·
                    refine ⟨1013446498165908123723215, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2702523995109088329928573 1013446498165908123723215)
                    ·
                      rfl

theorem cell22_2960520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 1, 1, 1, 4, 3].length) (baseStart_2960520 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2960520 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2960520 prefixEnd_2960520 := by exact prefixLift 2960520
  have htrace : WordTrace (prefixWord ++ tailWord_2960520) baseStart_2960520 baseEnd_2960520 := by
    simpa [prefixWord, tailWord_2960520, baseEnd_2960520] using wordTrace_append hprefix tailTrace_2960520
  have hstable : (prefixWord ++ tailWord_2960520).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2960520).length < 2 ^ (prefixWord ++ tailWord_2960520).sum := by decide
  have hdescent : baseEnd_2960520 < baseStart_2960520 := by decide
  rcases family_descends (prefixWord ++ tailWord_2960520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2960608 : List Nat := [2, 1, 1, 3, 1, 5, 1, 1, 3, 4]
def baseStart_2960608 : Nat := 118140960795 + 2960608 * 2 ^ 59
def prefixEnd_2960608 : Nat := 4983230072969 + 3 ^ 40 * 2960608 * 2
def baseEnd_2960608 : Nat := 1013476622364305227522945

theorem tailTrace_2960608 : CollatzResearch.WordTrace tailWord_2960608 prefixEnd_2960608 1013476622364305227522945 := by
  unfold tailWord_2960608
  simp only [CollatzResearch.WordTrace]
  refine ⟨53991122429115161218061239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71988163238820214957414985 53991122429115161218061239)
  ·
    refine ⟨80986683643672741827091859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53991122429115161218061239 80986683643672741827091859)
    ·
      refine ⟨121480025465509112740637789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80986683643672741827091859 121480025465509112740637789)
      ·
        refine ⟨45555009549565917277739171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 121480025465509112740637789 45555009549565917277739171)
        ·
          refine ⟨68332514324348875916608757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45555009549565917277739171 68332514324348875916608757)
          ·
            refine ⟨6406173217907707117182071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 68332514324348875916608757 6406173217907707117182071)
            ·
              refine ⟨9609259826861560675773107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6406173217907707117182071 9609259826861560675773107)
              ·
                refine ⟨14413889740292341013659661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9609259826861560675773107 14413889740292341013659661)
                ·
                  refine ⟨5405208652609627880122373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14413889740292341013659661 5405208652609627880122373)
                  ·
                    refine ⟨1013476622364305227522945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5405208652609627880122373 1013476622364305227522945)
                    ·
                      rfl

theorem cell22_2960608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 5, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 5, 1, 1, 3, 4].length) (baseStart_2960608 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2960608 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2960608 prefixEnd_2960608 := by exact prefixLift 2960608
  have htrace : WordTrace (prefixWord ++ tailWord_2960608) baseStart_2960608 baseEnd_2960608 := by
    simpa [prefixWord, tailWord_2960608, baseEnd_2960608] using wordTrace_append hprefix tailTrace_2960608
  have hstable : (prefixWord ++ tailWord_2960608).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2960608).length < 2 ^ (prefixWord ++ tailWord_2960608).sum := by decide
  have hdescent : baseEnd_2960608 < baseStart_2960608 := by decide
  rcases family_descends (prefixWord ++ tailWord_2960608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2960685 : List Nat := [1, 5, 3, 1, 1, 2, 9]
def baseStart_2960685 : Nat := 118140960795 + 2960685 * 2 ^ 59
def prefixEnd_2960685 : Nat := 4983230072969 + 3 ^ 40 * 2960685 * 2
def baseEnd_2960685 : Nat := 37537147445848247901767

theorem tailTrace_2960685 : CollatzResearch.WordTrace tailWord_2960685 prefixEnd_2960685 37537147445848247901767 := by
  unfold tailWord_2960685
  simp only [CollatzResearch.WordTrace]
  refine ⟨107985053278951364586675509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71990035519300909724450339 107985053278951364586675509)
  ·
    refine ⟨10123598744901690430000829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 107985053278951364586675509 10123598744901690430000829)
    ·
      refine ⟨3796349529338133911250311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10123598744901690430000829 3796349529338133911250311)
      ·
        refine ⟨5694524294007200866875467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3796349529338133911250311 5694524294007200866875467)
        ·
          refine ⟨8541786441010801300313201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5694524294007200866875467 8541786441010801300313201)
          ·
            refine ⟨6406339830758100975234901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8541786441010801300313201 6406339830758100975234901)
            ·
              refine ⟨37537147445848247901767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 6406339830758100975234901 37537147445848247901767)
              ·
                rfl

theorem cell22_2960685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 2, 9].length) (baseStart_2960685 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2960685 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2960685 prefixEnd_2960685 := by exact prefixLift 2960685
  have htrace : WordTrace (prefixWord ++ tailWord_2960685) baseStart_2960685 baseEnd_2960685 := by
    simpa [prefixWord, tailWord_2960685, baseEnd_2960685] using wordTrace_append hprefix tailTrace_2960685
  have hstable : (prefixWord ++ tailWord_2960685).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2960685).length < 2 ^ (prefixWord ++ tailWord_2960685).sum := by decide
  have hdescent : baseEnd_2960685 < baseStart_2960685 := by decide
  rcases family_descends (prefixWord ++ tailWord_2960685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2960700 : List Nat := [2, 2, 2, 2, 1, 3, 1, 3, 3, 3]
def baseStart_2960700 : Nat := 118140960795 + 2960700 * 2 ^ 59
def prefixEnd_2960700 : Nat := 4983230072969 + 3 ^ 40 * 2960700 * 2
def baseEnd_2960700 : Nat := 1013508115844447654222663

theorem tailTrace_2960700 : CollatzResearch.WordTrace tailWord_2960700 prefixEnd_2960700 1013508115844447654222663 := by
  unfold tailWord_2960700
  simp only [CollatzResearch.WordTrace]
  refine ⟨53992800186948511074235777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71990400249264681432314369 53992800186948511074235777)
  ·
    refine ⟨40494600140211383305676833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53992800186948511074235777 40494600140211383305676833)
    ·
      refine ⟨30370950105158537479257625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40494600140211383305676833 30370950105158537479257625)
      ·
        refine ⟨22778212578868903109443219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30370950105158537479257625 22778212578868903109443219)
        ·
          refine ⟨34167318868303354664164829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22778212578868903109443219 34167318868303354664164829)
          ·
            refine ⟨12812744575613757999061811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34167318868303354664164829 12812744575613757999061811)
            ·
              refine ⟨19219116863420636998592717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12812744575613757999061811 19219116863420636998592717)
              ·
                refine ⟨7207168823782738874472269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19219116863420636998592717 7207168823782738874472269)
                ·
                  refine ⟨2702688308918527077927101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7207168823782738874472269 2702688308918527077927101)
                  ·
                    refine ⟨1013508115844447654222663, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2702688308918527077927101 1013508115844447654222663)
                    ·
                      rfl

theorem cell22_2960700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 1, 3, 3, 3].length) (baseStart_2960700 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2960700 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2960700 prefixEnd_2960700 := by exact prefixLift 2960700
  have htrace : WordTrace (prefixWord ++ tailWord_2960700) baseStart_2960700 baseEnd_2960700 := by
    simpa [prefixWord, tailWord_2960700, baseEnd_2960700] using wordTrace_append hprefix tailTrace_2960700
  have hstable : (prefixWord ++ tailWord_2960700).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2960700).length < 2 ^ (prefixWord ++ tailWord_2960700).sum := by decide
  have hdescent : baseEnd_2960700 < baseStart_2960700 := by decide
  rcases family_descends (prefixWord ++ tailWord_2960700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2960713 : List Nat := [1, 2, 1, 1, 2, 3, 2, 5, 5]
def baseStart_2960713 : Nat := 118140960795 + 2960713 * 2 ^ 59
def prefixEnd_2960713 : Nat := 4983230072969 + 3 ^ 40 * 2960713 * 2
def baseEnd_2960713 : Nat := 337837522003373317882541

theorem tailTrace_2960713 : CollatzResearch.WordTrace tailWord_2960713 prefixEnd_2960713 337837522003373317882541 := by
  unfold tailWord_2960713
  simp only [CollatzResearch.WordTrace]
  refine ⟨107986074522849925368694793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71990716348566616912463195 107986074522849925368694793)
  ·
    refine ⟨80989555892137444026521095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107986074522849925368694793 80989555892137444026521095)
    ·
      refine ⟨121484333838206166039781643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80989555892137444026521095 121484333838206166039781643)
      ·
        refine ⟨182226500757309249059672465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121484333838206166039781643 182226500757309249059672465)
        ·
          refine ⟨136669875567981936794754349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 182226500757309249059672465 136669875567981936794754349)
          ·
            refine ⟨51251203337993226298032881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 136669875567981936794754349 51251203337993226298032881)
            ·
              refine ⟨38438402503494919723524661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51251203337993226298032881 38438402503494919723524661)
              ·
                refine ⟨3603600234702648724080437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 38438402503494919723524661 3603600234702648724080437)
                ·
                  refine ⟨337837522003373317882541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3603600234702648724080437 337837522003373317882541)
                  ·
                    rfl

theorem cell22_2960713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 2, 5, 5].length) (baseStart_2960713 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2960713 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2960713 prefixEnd_2960713 := by exact prefixLift 2960713
  have htrace : WordTrace (prefixWord ++ tailWord_2960713) baseStart_2960713 baseEnd_2960713 := by
    simpa [prefixWord, tailWord_2960713, baseEnd_2960713] using wordTrace_append hprefix tailTrace_2960713
  have hstable : (prefixWord ++ tailWord_2960713).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2960713).length < 2 ^ (prefixWord ++ tailWord_2960713).sum := by decide
  have hdescent : baseEnd_2960713 < baseStart_2960713 := by decide
  rcases family_descends (prefixWord ++ tailWord_2960713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2960835 : List Nat := [1, 1, 1, 3, 1, 1, 5, 1, 5, 3]
def baseStart_2960835 : Nat := 118140960795 + 2960835 * 2 ^ 59
def prefixEnd_2960835 : Nat := 4983230072969 + 3 ^ 40 * 2960835 * 2
def baseEnd_2960835 : Nat := 1013554329103352302097249

theorem tailTrace_2960835 : CollatzResearch.WordTrace tailWord_2960835 prefixEnd_2960835 1013554329103352302097249 := by
  unfold tailWord_2960835
  simp only [CollatzResearch.WordTrace]
  refine ⟨107990524228407940204635959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71993682818938626803090639 107990524228407940204635959)
  ·
    refine ⟨161985786342611910306953939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107990524228407940204635959 161985786342611910306953939)
    ·
      refine ⟨242978679513917865460430909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 161985786342611910306953939 242978679513917865460430909)
      ·
        refine ⟨91117004817719199547661591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 242978679513917865460430909 91117004817719199547661591)
        ·
          refine ⟨136675507226578799321492387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91117004817719199547661591 136675507226578799321492387)
          ·
            refine ⟨205013260839868198982238581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 136675507226578799321492387 205013260839868198982238581)
            ·
              refine ⟨19219993203737643654584867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 205013260839868198982238581 19219993203737643654584867)
              ·
                refine ⟨28829989805606465481877301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19219993203737643654584867 28829989805606465481877301)
                ·
                  refine ⟨2702811544275606138925997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 28829989805606465481877301 2702811544275606138925997)
                  ·
                    refine ⟨1013554329103352302097249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2702811544275606138925997 1013554329103352302097249)
                    ·
                      rfl

theorem cell22_2960835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 5, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 5, 1, 5, 3].length) (baseStart_2960835 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2960835 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2960835 prefixEnd_2960835 := by exact prefixLift 2960835
  have htrace : WordTrace (prefixWord ++ tailWord_2960835) baseStart_2960835 baseEnd_2960835 := by
    simpa [prefixWord, tailWord_2960835, baseEnd_2960835] using wordTrace_append hprefix tailTrace_2960835
  have hstable : (prefixWord ++ tailWord_2960835).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2960835).length < 2 ^ (prefixWord ++ tailWord_2960835).sum := by decide
  have hdescent : baseEnd_2960835 < baseStart_2960835 := by decide
  rcases family_descends (prefixWord ++ tailWord_2960835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2960848 : List Nat := [2, 1, 1, 1, 1, 2, 2, 3, 9]
def baseStart_2960848 : Nat := 118140960795 + 2960848 * 2 ^ 59
def prefixEnd_2960848 : Nat := 4983230072969 + 3 ^ 40 * 2960848 * 2
def baseEnd_2960848 : Nat := 337852926423008200507403

theorem tailTrace_2960848 : CollatzResearch.WordTrace tailWord_2960848 prefixEnd_2960848 337852926423008200507403 := by
  unfold tailWord_2960848
  simp only [CollatzResearch.WordTrace]
  refine ⟨53995499188680421712429599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71993998918240562283239465 53995499188680421712429599)
  ·
    refine ⟨80993248783020632568644399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53995499188680421712429599 80993248783020632568644399)
    ·
      refine ⟨121489873174530948852966599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80993248783020632568644399 121489873174530948852966599)
      ·
        refine ⟨182234809761796423279449899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121489873174530948852966599 182234809761796423279449899)
        ·
          refine ⟨273352214642694634919174849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 182234809761796423279449899 273352214642694634919174849)
          ·
            refine ⟨205014160982020976189381137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 273352214642694634919174849 205014160982020976189381137)
            ·
              refine ⟨153760620736515732142035853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 205014160982020976189381137 153760620736515732142035853)
              ·
                refine ⟨57660232776193399553263445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 153760620736515732142035853 57660232776193399553263445)
                ·
                  refine ⟨337852926423008200507403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 57660232776193399553263445 337852926423008200507403)
                  ·
                    rfl

theorem cell22_2960848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 3, 9].length) (baseStart_2960848 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2960848 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2960848 prefixEnd_2960848 := by exact prefixLift 2960848
  have htrace : WordTrace (prefixWord ++ tailWord_2960848) baseStart_2960848 baseEnd_2960848 := by
    simpa [prefixWord, tailWord_2960848, baseEnd_2960848] using wordTrace_append hprefix tailTrace_2960848
  have hstable : (prefixWord ++ tailWord_2960848).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2960848).length < 2 ^ (prefixWord ++ tailWord_2960848).sum := by decide
  have hdescent : baseEnd_2960848 < baseStart_2960848 := by decide
  rcases family_descends (prefixWord ++ tailWord_2960848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2960865 : List Nat := [1, 2, 3, 1, 2, 4, 1, 1, 7]
def baseStart_2960865 : Nat := 118140960795 + 2960865 * 2 ^ 59
def prefixEnd_2960865 : Nat := 4983230072969 + 3 ^ 40 * 2960865 * 2
def baseEnd_2960865 : Nat := 337854866238814074615719

theorem tailTrace_2960865 : CollatzResearch.WordTrace tailWord_2960865 prefixEnd_2960865 337854866238814074615719 := by
  unfold tailWord_2960865
  simp only [CollatzResearch.WordTrace]
  refine ⟨107991618418299255328228049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71994412278866170218818699 107991618418299255328228049)
  ·
    refine ⟨80993713813724441496171037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107991618418299255328228049 80993713813724441496171037)
    ·
      refine ⟨30372642680146665561064139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 80993713813724441496171037 30372642680146665561064139)
      ·
        refine ⟨45558964020219998341596209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30372642680146665561064139 45558964020219998341596209)
        ·
          refine ⟨34169223015164998756197157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45558964020219998341596209 34169223015164998756197157)
          ·
            refine ⟨6406729315343437266786967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 34169223015164998756197157 6406729315343437266786967)
            ·
              refine ⟨9610093973015155900180451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6406729315343437266786967 9610093973015155900180451)
              ·
                refine ⟨14415140959522733850270677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9610093973015155900180451 14415140959522733850270677)
                ·
                  refine ⟨337854866238814074615719, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14415140959522733850270677 337854866238814074615719)
                  ·
                    rfl

theorem cell22_2960865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 4, 1, 1, 7].length) (baseStart_2960865 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2960865 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2960865 prefixEnd_2960865 := by exact prefixLift 2960865
  have htrace : WordTrace (prefixWord ++ tailWord_2960865) baseStart_2960865 baseEnd_2960865 := by
    simpa [prefixWord, tailWord_2960865, baseEnd_2960865] using wordTrace_append hprefix tailTrace_2960865
  have hstable : (prefixWord ++ tailWord_2960865).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2960865).length < 2 ^ (prefixWord ++ tailWord_2960865).sum := by decide
  have hdescent : baseEnd_2960865 < baseStart_2960865 := by decide
  rcases family_descends (prefixWord ++ tailWord_2960865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2960869 : List Nat := [1, 3, 1, 5, 1, 2, 2, 1, 3, 3]
def baseStart_2960869 : Nat := 118140960795 + 2960869 * 2 ^ 59
def prefixEnd_2960869 : Nat := 4983230072969 + 3 ^ 40 * 2960869 * 2
def baseEnd_2960869 : Nat := 1013565967998187546747145

theorem tailTrace_2960869 : CollatzResearch.WordTrace tailWord_2960869 prefixEnd_2960869 1013565967998187546747145 := by
  unfold tailWord_2960869
  simp only [CollatzResearch.WordTrace]
  refine ⟨107991764310284764011373661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71994509540189842674249107 107991764310284764011373661)
  ·
    refine ⟨40496911616356786504265123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 107991764310284764011373661 40496911616356786504265123)
    ·
      refine ⟨60745367424535179756397685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40496911616356786504265123 60745367424535179756397685)
      ·
        refine ⟨5694878196050173102162283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 60745367424535179756397685 5694878196050173102162283)
        ·
          refine ⟨8542317294075259653243425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5694878196050173102162283 8542317294075259653243425)
          ·
            refine ⟨6406737970556444739932569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8542317294075259653243425 6406737970556444739932569)
            ·
              refine ⟨4805053477917333554949427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6406737970556444739932569 4805053477917333554949427)
              ·
                refine ⟨7207580216876000332424141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4805053477917333554949427 7207580216876000332424141)
                ·
                  refine ⟨2702842581328500124659053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7207580216876000332424141 2702842581328500124659053)
                  ·
                    refine ⟨1013565967998187546747145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2702842581328500124659053 1013565967998187546747145)
                    ·
                      rfl

theorem cell22_2960869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 2, 2, 1, 3, 3].length) (baseStart_2960869 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2960869 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2960869 prefixEnd_2960869 := by exact prefixLift 2960869
  have htrace : WordTrace (prefixWord ++ tailWord_2960869) baseStart_2960869 baseEnd_2960869 := by
    simpa [prefixWord, tailWord_2960869, baseEnd_2960869] using wordTrace_append hprefix tailTrace_2960869
  have hstable : (prefixWord ++ tailWord_2960869).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2960869).length < 2 ^ (prefixWord ++ tailWord_2960869).sum := by decide
  have hdescent : baseEnd_2960869 < baseStart_2960869 := by decide
  rcases family_descends (prefixWord ++ tailWord_2960869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2960880 : List Nat := [2, 1, 1, 1, 3, 4, 2, 1, 2, 5]
def baseStart_2960880 : Nat := 118140960795 + 2960880 * 2 ^ 59
def prefixEnd_2960880 : Nat := 4983230072969 + 3 ^ 40 * 2960880 * 2
def baseEnd_2960880 : Nat := 1013569733522987184722111

theorem tailTrace_2960880 : CollatzResearch.WordTrace tailWord_2960880 prefixEnd_2960880 1013569733522987184722111 := by
  unfold tailWord_2960880
  simp only [CollatzResearch.WordTrace]
  refine ⟨53996082756622456445012047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71994777008829941926682729 53996082756622456445012047)
  ·
    refine ⟨80994124134933684667518071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53996082756622456445012047 80994124134933684667518071)
    ·
      refine ⟨121491186202400527001277107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80994124134933684667518071 121491186202400527001277107)
      ·
        refine ⟨182236779303600790501915661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121491186202400527001277107 182236779303600790501915661)
        ·
          refine ⟨68338792238850296438218373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 182236779303600790501915661 68338792238850296438218373)
          ·
            refine ⟨12813523544784430582165945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 68338792238850296438218373 12813523544784430582165945)
            ·
              refine ⟨9610142658588322936624459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12813523544784430582165945 9610142658588322936624459)
              ·
                refine ⟨14415213987882484404936689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9610142658588322936624459 14415213987882484404936689)
                ·
                  refine ⟨10811410490911863303702517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14415213987882484404936689 10811410490911863303702517)
                  ·
                    refine ⟨1013569733522987184722111, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10811410490911863303702517 1013569733522987184722111)
                    ·
                      rfl

theorem cell22_2960880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 2, 1, 2, 5].length) (baseStart_2960880 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2960880 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2960880 prefixEnd_2960880 := by exact prefixLift 2960880
  have htrace : WordTrace (prefixWord ++ tailWord_2960880) baseStart_2960880 baseEnd_2960880 := by
    simpa [prefixWord, tailWord_2960880, baseEnd_2960880] using wordTrace_append hprefix tailTrace_2960880
  have hstable : (prefixWord ++ tailWord_2960880).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2960880).length < 2 ^ (prefixWord ++ tailWord_2960880).sum := by decide
  have hdescent : baseEnd_2960880 < baseStart_2960880 := by decide
  rcases family_descends (prefixWord ++ tailWord_2960880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2960927 : List Nat := [1, 1, 2, 4, 1, 1, 2, 6, 4]
def baseStart_2960927 : Nat := 118140960795 + 2960927 * 2 ^ 59
def prefixEnd_2960927 : Nat := 4983230072969 + 3 ^ 40 * 2960927 * 2
def baseEnd_2960927 : Nat := 337861940861164909598989

theorem tailTrace_2960927 : CollatzResearch.WordTrace tailWord_2960927 prefixEnd_2960927 337861940861164909598989 := by
  unfold tailWord_2960927
  simp only [CollatzResearch.WordTrace]
  refine ⟨107993879744074639916985035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71995919829383093277990023 107993879744074639916985035)
  ·
    refine ⟨161990819616111959875477553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107993879744074639916985035 161990819616111959875477553)
    ·
      refine ⟨121493114712083969906608165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 161990819616111959875477553 121493114712083969906608165)
      ·
        refine ⟨22779959008515744357489031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 121493114712083969906608165 22779959008515744357489031)
        ·
          refine ⟨34169938512773616536233547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22779959008515744357489031 34169938512773616536233547)
          ·
            refine ⟨51254907769160424804350321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34169938512773616536233547 51254907769160424804350321)
            ·
              refine ⟨38441180826870318603262741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51254907769160424804350321 38441180826870318603262741)
              ·
                refine ⟨1801930351259546184527941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 38441180826870318603262741 1801930351259546184527941)
                ·
                  refine ⟨337861940861164909598989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1801930351259546184527941 337861940861164909598989)
                  ·
                    rfl

theorem cell22_2960927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 2, 6, 4].length) (baseStart_2960927 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2960927 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2960927 prefixEnd_2960927 := by exact prefixLift 2960927
  have htrace : WordTrace (prefixWord ++ tailWord_2960927) baseStart_2960927 baseEnd_2960927 := by
    simpa [prefixWord, tailWord_2960927, baseEnd_2960927] using wordTrace_append hprefix tailTrace_2960927
  have hstable : (prefixWord ++ tailWord_2960927).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2960927).length < 2 ^ (prefixWord ++ tailWord_2960927).sum := by decide
  have hdescent : baseEnd_2960927 < baseStart_2960927 := by decide
  rcases family_descends (prefixWord ++ tailWord_2960927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2961015 : List Nat := [1, 1, 3, 1, 1, 3, 1, 1, 3, 7]
def baseStart_2961015 : Nat := 118140960795 + 2961015 * 2 ^ 59
def prefixEnd_2961015 : Nat := 4983230072969 + 3 ^ 40 * 2961015 * 2
def baseEnd_2961015 : Nat := 1013615946781891832596697

theorem tailTrace_2961015 : CollatzResearch.WordTrace tailWord_2961015 prefixEnd_2961015 1013615946781891832596697 := by
  unfold tailWord_2961015
  simp only [CollatzResearch.WordTrace]
  refine ⟨107997089367755830946188499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71998059578503887297458999 107997089367755830946188499)
  ·
    refine ⟨161995634051633746419282749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107997089367755830946188499 161995634051633746419282749)
    ·
      refine ⟨60748362769362654907231031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 161995634051633746419282749 60748362769362654907231031)
      ·
        refine ⟨91122544154043982360846547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60748362769362654907231031 91122544154043982360846547)
        ·
          refine ⟨136683816231065973541269821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91122544154043982360846547 136683816231065973541269821)
          ·
            refine ⟨51256431086649740077976183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 136683816231065973541269821 51256431086649740077976183)
            ·
              refine ⟨76884646629974610116964275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51256431086649740077976183 76884646629974610116964275)
              ·
                refine ⟨115326969944961915175446413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 76884646629974610116964275 115326969944961915175446413)
                ·
                  refine ⟨43247613729360718190792405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 115326969944961915175446413 43247613729360718190792405)
                  ·
                    refine ⟨1013615946781891832596697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 43247613729360718190792405 1013615946781891832596697)
                    ·
                      rfl

theorem cell22_2961015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 1, 3, 7].length) (baseStart_2961015 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2961015 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2961015 prefixEnd_2961015 := by exact prefixLift 2961015
  have htrace : WordTrace (prefixWord ++ tailWord_2961015) baseStart_2961015 baseEnd_2961015 := by
    simpa [prefixWord, tailWord_2961015, baseEnd_2961015] using wordTrace_append hprefix tailTrace_2961015
  have hstable : (prefixWord ++ tailWord_2961015).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2961015).length < 2 ^ (prefixWord ++ tailWord_2961015).sum := by decide
  have hdescent : baseEnd_2961015 < baseStart_2961015 := by decide
  rcases family_descends (prefixWord ++ tailWord_2961015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2961021 : List Nat := [1, 4, 1, 1, 4, 1, 1, 5, 1, 3]
def baseStart_2961021 : Nat := 118140960795 + 2961021 * 2 ^ 59
def prefixEnd_2961021 : Nat := 4983230072969 + 3 ^ 40 * 2961021 * 2
def baseEnd_2961021 : Nat := 1013618000704509816946679

theorem tailTrace_2961021 : CollatzResearch.WordTrace tailWord_2961021 prefixEnd_2961021 1013618000704509816946679 := by
  unfold tailWord_2961021
  simp only [CollatzResearch.WordTrace]
  refine ⟨107997308205734093970906917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71998205470489395980604611 107997308205734093970906917)
  ·
    refine ⟨20249495288575142619545047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 107997308205734093970906917 20249495288575142619545047)
    ·
      refine ⟨30374242932862713929317571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20249495288575142619545047 30374242932862713929317571)
      ·
        refine ⟨45561364399294070893976357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30374242932862713929317571 45561364399294070893976357)
        ·
          refine ⟨8542755824867638292620567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 45561364399294070893976357 8542755824867638292620567)
          ·
            refine ⟨12814133737301457438930851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8542755824867638292620567 12814133737301457438930851)
            ·
              refine ⟨19221200605952186158396277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12814133737301457438930851 19221200605952186158396277)
              ·
                refine ⟨1801987556808017452349651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 19221200605952186158396277 1801987556808017452349651)
                ·
                  refine ⟨2702981335212026178524477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1801987556808017452349651 2702981335212026178524477)
                  ·
                    refine ⟨1013618000704509816946679, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2702981335212026178524477 1013618000704509816946679)
                    ·
                      rfl

theorem cell22_2961021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 1, 5, 1, 3].length) (baseStart_2961021 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2961021 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2961021 prefixEnd_2961021 := by exact prefixLift 2961021
  have htrace : WordTrace (prefixWord ++ tailWord_2961021) baseStart_2961021 baseEnd_2961021 := by
    simpa [prefixWord, tailWord_2961021, baseEnd_2961021] using wordTrace_append hprefix tailTrace_2961021
  have hstable : (prefixWord ++ tailWord_2961021).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2961021).length < 2 ^ (prefixWord ++ tailWord_2961021).sum := by decide
  have hdescent : baseEnd_2961021 < baseStart_2961021 := by decide
  rcases family_descends (prefixWord ++ tailWord_2961021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2961034 : List Nat := [3, 1, 2, 3, 2, 1, 3, 2, 5]
def baseStart_2961034 : Nat := 118140960795 + 2961034 * 2 ^ 59
def prefixEnd_2961034 : Nat := 4983230072969 + 3 ^ 40 * 2961034 * 2
def baseEnd_2961034 : Nat := 337874150290060705457213

theorem tailTrace_2961034 : CollatzResearch.WordTrace tailWord_2961034 prefixEnd_2961034 337874150290060705457213 := by
  unfold tailWord_2961034
  simp only [CollatzResearch.WordTrace]
  refine ⟨26999445588671749297782539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71998521569791331460753437 26999445588671749297782539)
  ·
    refine ⟨40499168383007623946673809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26999445588671749297782539 40499168383007623946673809)
    ·
      refine ⟨30374376287255717960005357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40499168383007623946673809 30374376287255717960005357)
      ·
        refine ⟨11390391107720894235002009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30374376287255717960005357 11390391107720894235002009)
        ·
          refine ⟨8542793330790670676251507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11390391107720894235002009 8542793330790670676251507)
          ·
            refine ⟨12814189996186006014377261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8542793330790670676251507 12814189996186006014377261)
            ·
              refine ⟨4805321248569752255391473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12814189996186006014377261 4805321248569752255391473)
              ·
                refine ⟨3603990936427314191543605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4805321248569752255391473 3603990936427314191543605)
                ·
                  refine ⟨337874150290060705457213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3603990936427314191543605 337874150290060705457213)
                  ·
                    rfl

theorem cell22_2961034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 3, 2, 5].length) (baseStart_2961034 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2961034 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2961034 prefixEnd_2961034 := by exact prefixLift 2961034
  have htrace : WordTrace (prefixWord ++ tailWord_2961034) baseStart_2961034 baseEnd_2961034 := by
    simpa [prefixWord, tailWord_2961034, baseEnd_2961034] using wordTrace_append hprefix tailTrace_2961034
  have hstable : (prefixWord ++ tailWord_2961034).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2961034).length < 2 ^ (prefixWord ++ tailWord_2961034).sum := by decide
  have hdescent : baseEnd_2961034 < baseStart_2961034 := by decide
  rcases family_descends (prefixWord ++ tailWord_2961034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2961096 : List Nat := [2, 1, 3, 1, 2, 2, 5, 2, 4]
def baseStart_2961096 : Nat := 118140960795 + 2961096 * 2 ^ 59
def prefixEnd_2961096 : Nat := 4983230072969 + 3 ^ 40 * 2961096 * 2
def baseEnd_2961096 : Nat := 337881224912411540440483

theorem tailTrace_2961096 : CollatzResearch.WordTrace tailWord_2961096 prefixEnd_2961096 337881224912411540440483 := by
  unfold tailWord_2961096
  simp only [CollatzResearch.WordTrace]
  refine ⟨54000021840231190889943571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72000029120308254519924761 54000021840231190889943571)
  ·
    refine ⟨81000032760346786334915357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54000021840231190889943571 81000032760346786334915357)
    ·
      refine ⟨30375012285130044875593259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 81000032760346786334915357 30375012285130044875593259)
      ·
        refine ⟨45562518427695067313389889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30375012285130044875593259 45562518427695067313389889)
        ·
          refine ⟨34171888820771300485042417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45562518427695067313389889 34171888820771300485042417)
          ·
            refine ⟨25628916615578475363781813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34171888820771300485042417 25628916615578475363781813)
            ·
              refine ⟨2402710932710482065354545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 25628916615578475363781813 2402710932710482065354545)
              ·
                refine ⟨1802033199532861549015909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2402710932710482065354545 1802033199532861549015909)
                ·
                  refine ⟨337881224912411540440483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1802033199532861549015909 337881224912411540440483)
                  ·
                    rfl

theorem cell22_2961096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 5, 2, 4].length) (baseStart_2961096 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2961096 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2961096 prefixEnd_2961096 := by exact prefixLift 2961096
  have htrace : WordTrace (prefixWord ++ tailWord_2961096) baseStart_2961096 baseEnd_2961096 := by
    simpa [prefixWord, tailWord_2961096, baseEnd_2961096] using wordTrace_append hprefix tailTrace_2961096
  have hstable : (prefixWord ++ tailWord_2961096).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2961096).length < 2 ^ (prefixWord ++ tailWord_2961096).sum := by decide
  have hdescent : baseEnd_2961096 < baseStart_2961096 := by decide
  rcases family_descends (prefixWord ++ tailWord_2961096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2961154 : List Nat := [3, 4, 1, 1, 1, 1, 1, 1, 1, 8]
def baseStart_2961154 : Nat := 118140960795 + 2961154 * 2 ^ 59
def prefixEnd_2961154 : Nat := 4983230072969 + 3 ^ 40 * 2961154 * 2
def baseEnd_2961154 : Nat := 1013663529322541803371271

theorem tailTrace_2961154 : CollatzResearch.WordTrace tailWord_2961154 prefixEnd_2961154 1013663529322541803371271 := by
  unfold tailWord_2961154
  simp only [CollatzResearch.WordTrace]
  refine ⟨27000539778563064421374629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72001439409501505123665677 27000539778563064421374629)
  ·
    refine ⟨5062601208480574579007743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 27000539778563064421374629 5062601208480574579007743)
    ·
      refine ⟨7593901812720861868511615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5062601208480574579007743 7593901812720861868511615)
      ·
        refine ⟨11390852719081292802767423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7593901812720861868511615 11390852719081292802767423)
        ·
          refine ⟨17086279078621939204151135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11390852719081292802767423 17086279078621939204151135)
          ·
            refine ⟨25629418617932908806226703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17086279078621939204151135 25629418617932908806226703)
            ·
              refine ⟨38444127926899363209340055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25629418617932908806226703 38444127926899363209340055)
              ·
                refine ⟨57666191890349044814010083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38444127926899363209340055 57666191890349044814010083)
                ·
                  refine ⟨86499287835523567221015125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 57666191890349044814010083 86499287835523567221015125)
                  ·
                    refine ⟨1013663529322541803371271, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 86499287835523567221015125 1013663529322541803371271)
                    ·
                      rfl

theorem cell22_2961154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 1, 1, 1, 8].length) (baseStart_2961154 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2961154 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2961154 prefixEnd_2961154 := by exact prefixLift 2961154
  have htrace : WordTrace (prefixWord ++ tailWord_2961154) baseStart_2961154 baseEnd_2961154 := by
    simpa [prefixWord, tailWord_2961154, baseEnd_2961154] using wordTrace_append hprefix tailTrace_2961154
  have hstable : (prefixWord ++ tailWord_2961154).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2961154).length < 2 ^ (prefixWord ++ tailWord_2961154).sum := by decide
  have hdescent : baseEnd_2961154 < baseStart_2961154 := by decide
  rcases family_descends (prefixWord ++ tailWord_2961154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2961199 : List Nat := [1, 1, 2, 1, 2, 1, 2, 7, 1, 4]
def baseStart_2961199 : Nat := 118140960795 + 2961199 * 2 ^ 59
def prefixEnd_2961199 : Nat := 4983230072969 + 3 ^ 40 * 2961199 * 2
def baseEnd_2961199 : Nat := 1013678933742176685996133

theorem tailTrace_2961199 : CollatzResearch.WordTrace tailWord_2961199 prefixEnd_2961199 1013678933742176685996133 := by
  unfold tailWord_2961199
  simp only [CollatzResearch.WordTrace]
  refine ⟨108003800399089230370886651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72002533599392820247257767 108003800399089230370886651)
  ·
    refine ⟨162005700598633845556329977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108003800399089230370886651 162005700598633845556329977)
    ·
      refine ⟨121504275448975384167247483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 162005700598633845556329977 121504275448975384167247483)
      ·
        refine ⟨182256413173463076250871225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121504275448975384167247483 182256413173463076250871225)
        ·
          refine ⟨136692309880097307188153419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 182256413173463076250871225 136692309880097307188153419)
          ·
            refine ⟨205038464820145960782230129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 136692309880097307188153419 205038464820145960782230129)
            ·
              refine ⟨153778848615109470586672597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 205038464820145960782230129 153778848615109470586672597)
              ·
                refine ⟨3604191764416628216875139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 153778848615109470586672597 3604191764416628216875139)
                ·
                  refine ⟨5406287646624942325312709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3604191764416628216875139 5406287646624942325312709)
                  ·
                    refine ⟨1013678933742176685996133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5406287646624942325312709 1013678933742176685996133)
                    ·
                      rfl

theorem cell22_2961199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 7, 1, 4].length) (baseStart_2961199 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2961199 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2961199 prefixEnd_2961199 := by exact prefixLift 2961199
  have htrace : WordTrace (prefixWord ++ tailWord_2961199) baseStart_2961199 baseEnd_2961199 := by
    simpa [prefixWord, tailWord_2961199, baseEnd_2961199] using wordTrace_append hprefix tailTrace_2961199
  have hstable : (prefixWord ++ tailWord_2961199).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2961199).length < 2 ^ (prefixWord ++ tailWord_2961199).sum := by decide
  have hdescent : baseEnd_2961199 < baseStart_2961199 := by decide
  rcases family_descends (prefixWord ++ tailWord_2961199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2961203 : List Nat := [1, 1, 1, 2, 8, 1, 1, 2, 5]
def baseStart_2961203 : Nat := 118140960795 + 2961203 * 2 ^ 59
def prefixEnd_2961203 : Nat := 4983230072969 + 3 ^ 40 * 2961203 * 2
def baseEnd_2961203 : Nat := 337893434341307336298707

theorem tailTrace_2961203 : CollatzResearch.WordTrace tailWord_2961203 prefixEnd_2961203 337893434341307336298707 := by
  unfold tailWord_2961203
  simp only [CollatzResearch.WordTrace]
  refine ⟨108003946291074739054032263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72002630860716492702688175 108003946291074739054032263)
  ·
    refine ⟨162005919436612108581048395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108003946291074739054032263 162005919436612108581048395)
    ·
      refine ⟨243008879154918162871572593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 162005919436612108581048395 243008879154918162871572593)
      ·
        refine ⟨182256659366188622153679445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 243008879154918162871572593 182256659366188622153679445)
        ·
          refine ⟨2135820226947522915863431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 182256659366188622153679445 2135820226947522915863431)
          ·
            refine ⟨3203730340421284373795147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2135820226947522915863431 3203730340421284373795147)
            ·
              refine ⟨4805595510631926560692721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3203730340421284373795147 4805595510631926560692721)
              ·
                refine ⟨3604196632973944920519541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4805595510631926560692721 3604196632973944920519541)
                ·
                  refine ⟨337893434341307336298707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3604196632973944920519541 337893434341307336298707)
                  ·
                    rfl

theorem cell22_2961203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 8, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 8, 1, 1, 2, 5].length) (baseStart_2961203 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2961203 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2961203 prefixEnd_2961203 := by exact prefixLift 2961203
  have htrace : WordTrace (prefixWord ++ tailWord_2961203) baseStart_2961203 baseEnd_2961203 := by
    simpa [prefixWord, tailWord_2961203, baseEnd_2961203] using wordTrace_append hprefix tailTrace_2961203
  have hstable : (prefixWord ++ tailWord_2961203).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2961203).length < 2 ^ (prefixWord ++ tailWord_2961203).sum := by decide
  have hdescent : baseEnd_2961203 < baseStart_2961203 := by decide
  rcases family_descends (prefixWord ++ tailWord_2961203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2961248 : List Nat := [2, 1, 1, 3, 3, 4, 1, 3, 4]
def baseStart_2961248 : Nat := 118140960795 + 2961248 * 2 ^ 59
def prefixEnd_2961248 : Nat := 4983230072969 + 3 ^ 40 * 2961248 * 2
def baseEnd_2961248 : Nat := 337898569147852297173661

theorem tailTrace_2961248 : CollatzResearch.WordTrace tailWord_2961248 prefixEnd_2961248 337898569147852297173661 := by
  unfold tailWord_2961248
  simp only [CollatzResearch.WordTrace]
  refine ⟨54002793787955855869710199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72003725050607807826280265 54002793787955855869710199)
  ·
    refine ⟨81004190681933783804565299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54002793787955855869710199 81004190681933783804565299)
    ·
      refine ⟨121506286022900675706847949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81004190681933783804565299 121506286022900675706847949)
      ·
        refine ⟨45564857258587753390067981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 121506286022900675706847949 45564857258587753390067981)
        ·
          refine ⟨17086821471970407521275493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45564857258587753390067981 17086821471970407521275493)
          ·
            refine ⟨3203779025994451410239155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17086821471970407521275493 3203779025994451410239155)
            ·
              refine ⟨4805668538991677115358733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3203779025994451410239155 4805668538991677115358733)
              ·
                refine ⟨1802125702121878918259525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4805668538991677115358733 1802125702121878918259525)
                ·
                  refine ⟨337898569147852297173661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1802125702121878918259525 337898569147852297173661)
                  ·
                    rfl

theorem cell22_2961248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 4, 1, 3, 4].length) (baseStart_2961248 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2961248 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2961248 prefixEnd_2961248 := by exact prefixLift 2961248
  have htrace : WordTrace (prefixWord ++ tailWord_2961248) baseStart_2961248 baseEnd_2961248 := by
    simpa [prefixWord, tailWord_2961248, baseEnd_2961248] using wordTrace_append hprefix tailTrace_2961248
  have hstable : (prefixWord ++ tailWord_2961248).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2961248).length < 2 ^ (prefixWord ++ tailWord_2961248).sum := by decide
  have hdescent : baseEnd_2961248 < baseStart_2961248 := by decide
  rcases family_descends (prefixWord ++ tailWord_2961248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2961351 : List Nat := [1, 1, 4, 1, 1, 2, 1, 6, 1, 4]
def baseStart_2961351 : Nat := 118140960795 + 2961351 * 2 ^ 59
def prefixEnd_2961351 : Nat := 4983230072969 + 3 ^ 40 * 2961351 * 2
def baseEnd_2961351 : Nat := 1013730966448498956195667

theorem tailTrace_2961351 : CollatzResearch.WordTrace tailWord_2961351 prefixEnd_2961351 1013730966448498956195667 := by
  unfold tailWord_2961351
  simp only [CollatzResearch.WordTrace]
  refine ⟨108009344294538560330419907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72006229529692373553613271 108009344294538560330419907)
  ·
    refine ⟨162014016441807840495629861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108009344294538560330419907 162014016441807840495629861)
    ·
      refine ⟨30377628082838970092930599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 162014016441807840495629861 30377628082838970092930599)
      ·
        refine ⟨45566442124258455139395899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30377628082838970092930599 45566442124258455139395899)
        ·
          refine ⟨68349663186387682709093849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45566442124258455139395899 68349663186387682709093849)
          ·
            refine ⟨51262247389790762031820387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 68349663186387682709093849 51262247389790762031820387)
            ·
              refine ⟨76893371084686143047730581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51262247389790762031820387 76893371084686143047730581)
              ·
                refine ⟨3604376769594662955362371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 76893371084686143047730581 3604376769594662955362371)
                ·
                  refine ⟨5406565154391994433043557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3604376769594662955362371 5406565154391994433043557)
                  ·
                    refine ⟨1013730966448498956195667, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5406565154391994433043557 1013730966448498956195667)
                    ·
                      rfl

theorem cell22_2961351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 6, 1, 4].length) (baseStart_2961351 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2961351 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2961351 prefixEnd_2961351 := by exact prefixLift 2961351
  have htrace : WordTrace (prefixWord ++ tailWord_2961351) baseStart_2961351 baseEnd_2961351 := by
    simpa [prefixWord, tailWord_2961351, baseEnd_2961351] using wordTrace_append hprefix tailTrace_2961351
  have hstable : (prefixWord ++ tailWord_2961351).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2961351).length < 2 ^ (prefixWord ++ tailWord_2961351).sum := by decide
  have hdescent : baseEnd_2961351 < baseStart_2961351 := by decide
  rcases family_descends (prefixWord ++ tailWord_2961351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2961383 : List Nat := [1, 1, 5, 2, 3, 1, 2, 1, 6]
def baseStart_2961383 : Nat := 118140960795 + 2961383 * 2 ^ 59
def prefixEnd_2961383 : Nat := 4983230072969 + 3 ^ 40 * 2961383 * 2
def baseEnd_2961383 : Nat := 337913973567487179798523

theorem tailTrace_2961383 : CollatzResearch.WordTrace tailWord_2961383 prefixEnd_2961383 337913973567487179798523 := by
  unfold tailWord_2961383
  simp only [CollatzResearch.WordTrace]
  refine ⟨108010511430422629795584803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72007007620281753197056535 108010511430422629795584803)
  ·
    refine ⟨162015767145633944693377205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108010511430422629795584803 162015767145633944693377205)
    ·
      refine ⟨15188978169903182315004113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 162015767145633944693377205 15188978169903182315004113)
      ·
        refine ⟨11391733627427386736253085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15188978169903182315004113 11391733627427386736253085)
        ·
          refine ⟨4271900110285270026094907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11391733627427386736253085 4271900110285270026094907)
          ·
            refine ⟨6407850165427905039142361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4271900110285270026094907 6407850165427905039142361)
            ·
              refine ⟨4805887624070928779356771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6407850165427905039142361 4805887624070928779356771)
              ·
                refine ⟨7208831436106393169035157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4805887624070928779356771 7208831436106393169035157)
                ·
                  refine ⟨337913973567487179798523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7208831436106393169035157 337913973567487179798523)
                  ·
                    rfl

theorem cell22_2961383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 1, 2, 1, 6].length) (baseStart_2961383 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2961383 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2961383 prefixEnd_2961383 := by exact prefixLift 2961383
  have htrace : WordTrace (prefixWord ++ tailWord_2961383) baseStart_2961383 baseEnd_2961383 := by
    simpa [prefixWord, tailWord_2961383, baseEnd_2961383] using wordTrace_append hprefix tailTrace_2961383
  have hstable : (prefixWord ++ tailWord_2961383).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2961383).length < 2 ^ (prefixWord ++ tailWord_2961383).sum := by decide
  have hdescent : baseEnd_2961383 < baseStart_2961383 := by decide
  rcases family_descends (prefixWord ++ tailWord_2961383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2961490 : List Nat := [3, 2, 2, 1, 4, 1, 2, 2, 5]
def baseStart_2961490 : Nat := 118140960795 + 2961490 * 2 ^ 59
def prefixEnd_2961490 : Nat := 4983230072969 + 3 ^ 40 * 2961490 * 2
def baseEnd_2961490 : Nat := 337926182996382975656747

theorem tailTrace_2961490 : CollatzResearch.WordTrace tailWord_2961490 prefixEnd_2961490 337926182996382975656747 := by
  unfold tailWord_2961490
  simp only [CollatzResearch.WordTrace]
  refine ⟨27003603510258746767432481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72009609360689991379819949 27003603510258746767432481)
  ·
    refine ⟨20252702632694060075574361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27003603510258746767432481 20252702632694060075574361)
    ·
      refine ⟨15189526974520545056680771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20252702632694060075574361 15189526974520545056680771)
      ·
        refine ⟨22784290461780817585021157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15189526974520545056680771 22784290461780817585021157)
        ·
          refine ⟨4272054461583903297191467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22784290461780817585021157 4272054461583903297191467)
          ·
            refine ⟨6408081692375854945787201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4272054461583903297191467 6408081692375854945787201)
            ·
              refine ⟨4806061269281891209340401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6408081692375854945787201 4806061269281891209340401)
              ·
                refine ⟨3604545951961418407005301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4806061269281891209340401 3604545951961418407005301)
                ·
                  refine ⟨337926182996382975656747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3604545951961418407005301 337926182996382975656747)
                  ·
                    rfl

theorem cell22_2961490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 1, 2, 2, 5].length) (baseStart_2961490 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2961490 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2961490 prefixEnd_2961490 := by exact prefixLift 2961490
  have htrace : WordTrace (prefixWord ++ tailWord_2961490) baseStart_2961490 baseEnd_2961490 := by
    simpa [prefixWord, tailWord_2961490, baseEnd_2961490] using wordTrace_append hprefix tailTrace_2961490
  have hstable : (prefixWord ++ tailWord_2961490).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2961490).length < 2 ^ (prefixWord ++ tailWord_2961490).sum := by decide
  have hdescent : baseEnd_2961490 < baseStart_2961490 := by decide
  rcases family_descends (prefixWord ++ tailWord_2961490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2961518 : List Nat := [4, 1, 2, 2, 1, 1, 3, 2, 6]
def baseStart_2961518 : Nat := 118140960795 + 2961518 * 2 ^ 59
def prefixEnd_2961518 : Nat := 4983230072969 + 3 ^ 40 * 2961518 * 2
def baseEnd_2961518 : Nat := 337929377987122062423385

theorem tailTrace_2961518 : CollatzResearch.WordTrace tailWord_2961518 prefixEnd_2961518 337929377987122062423385 := by
  unfold tailWord_2961518
  simp only [CollatzResearch.WordTrace]
  refine ⟨13501929410616693481468651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 72010290189955698567832805 13501929410616693481468651)
  ·
    refine ⟨20252894115925040222202977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13501929410616693481468651 20252894115925040222202977)
    ·
      refine ⟨15189670586943780166652233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20252894115925040222202977 15189670586943780166652233)
      ·
        refine ⟨11392252940207835124989175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15189670586943780166652233 11392252940207835124989175)
        ·
          refine ⟨17088379410311752687483763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11392252940207835124989175 17088379410311752687483763)
          ·
            refine ⟨25632569115467629031225645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17088379410311752687483763 25632569115467629031225645)
            ·
              refine ⟨9612213418300360886709617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25632569115467629031225645 9612213418300360886709617)
              ·
                refine ⟨7209160063725270665032213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9612213418300360886709617 7209160063725270665032213)
                ·
                  refine ⟨337929377987122062423385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7209160063725270665032213 337929377987122062423385)
                  ·
                    rfl

theorem cell22_2961518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 3, 2, 6].length) (baseStart_2961518 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2961518 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2961518 prefixEnd_2961518 := by exact prefixLift 2961518
  have htrace : WordTrace (prefixWord ++ tailWord_2961518) baseStart_2961518 baseEnd_2961518 := by
    simpa [prefixWord, tailWord_2961518, baseEnd_2961518] using wordTrace_append hprefix tailTrace_2961518
  have hstable : (prefixWord ++ tailWord_2961518).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2961518).length < 2 ^ (prefixWord ++ tailWord_2961518).sum := by decide
  have hdescent : baseEnd_2961518 < baseStart_2961518 := by decide
  rcases family_descends (prefixWord ++ tailWord_2961518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2961533 : List Nat := [1, 4, 1, 1, 3, 2, 2, 2, 1, 5]
def baseStart_2961533 : Nat := 118140960795 + 2961533 * 2 ^ 59
def prefixEnd_2961533 : Nat := 4983230072969 + 3 ^ 40 * 2961533 * 2
def baseEnd_2961533 : Nat := 1013793268767911148145109

theorem tailTrace_2961533 : CollatzResearch.WordTrace tailWord_2961533 prefixEnd_2961533 1013793268767911148145109 := by
  unfold tailWord_2961533
  simp only [CollatzResearch.WordTrace]
  refine ⟨108015982379879205413545253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72010654919919470275696835 108015982379879205413545253)
  ·
    refine ⟨20252996696227351015039735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 108015982379879205413545253 20252996696227351015039735)
    ·
      refine ⟨30379495044341026522559603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20252996696227351015039735 30379495044341026522559603)
      ·
        refine ⟨45569242566511539783839405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30379495044341026522559603 45569242566511539783839405)
        ·
          refine ⟨17088465962441827418939777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45569242566511539783839405 17088465962441827418939777)
          ·
            refine ⟨12816349471831370564204833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17088465962441827418939777 12816349471831370564204833)
            ·
              refine ⟨9612262103873527923153625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12816349471831370564204833 9612262103873527923153625)
              ·
                refine ⟨7209196577905145942365219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9612262103873527923153625 7209196577905145942365219)
                ·
                  refine ⟨10813794866857718913547829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7209196577905145942365219 10813794866857718913547829)
                  ·
                    refine ⟨1013793268767911148145109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10813794866857718913547829 1013793268767911148145109)
                    ·
                      rfl

theorem cell22_2961533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 2, 2, 1, 5].length) (baseStart_2961533 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2961533 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2961533 prefixEnd_2961533 := by exact prefixLift 2961533
  have htrace : WordTrace (prefixWord ++ tailWord_2961533) baseStart_2961533 baseEnd_2961533 := by
    simpa [prefixWord, tailWord_2961533, baseEnd_2961533] using wordTrace_append hprefix tailTrace_2961533
  have hstable : (prefixWord ++ tailWord_2961533).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2961533).length < 2 ^ (prefixWord ++ tailWord_2961533).sum := by decide
  have hdescent : baseEnd_2961533 < baseStart_2961533 := by decide
  rcases family_descends (prefixWord ++ tailWord_2961533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2961558 : List Nat := [5, 3, 2, 1, 1, 1, 3, 1, 5]
def baseStart_2961558 : Nat := 118140960795 + 2961558 * 2 ^ 59
def prefixEnd_2961558 : Nat := 4983230072969 + 3 ^ 40 * 2961558 * 2
def baseEnd_2961558 : Nat := 337933942259606472090011

theorem tailTrace_2961558 : CollatzResearch.WordTrace tailWord_2961558 prefixEnd_2961558 337933942259606472090011 := by
  unfold tailWord_2961558
  simp only [CollatzResearch.WordTrace]
  refine ⟨6751055887799289667700333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 72011262803192423122136885 6751055887799289667700333)
  ·
    refine ⟨2531645957924733625387625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6751055887799289667700333 2531645957924733625387625)
    ·
      refine ⟨1898734468443550219040719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2531645957924733625387625 1898734468443550219040719)
      ·
        refine ⟨2848101702665325328561079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1898734468443550219040719 2848101702665325328561079)
        ·
          refine ⟨4272152553997987992841619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2848101702665325328561079 4272152553997987992841619)
          ·
            refine ⟨6408228830996981989262429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4272152553997987992841619 6408228830996981989262429)
            ·
              refine ⟨2403085811623868245973411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6408228830996981989262429 2403085811623868245973411)
              ·
                refine ⟨3604628717435802368960117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2403085811623868245973411 3604628717435802368960117)
                ·
                  refine ⟨337933942259606472090011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3604628717435802368960117 337933942259606472090011)
                  ·
                    rfl

theorem cell22_2961558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 1, 3, 1, 5].length) (baseStart_2961558 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2961558 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2961558 prefixEnd_2961558 := by exact prefixLift 2961558
  have htrace : WordTrace (prefixWord ++ tailWord_2961558) baseStart_2961558 baseEnd_2961558 := by
    simpa [prefixWord, tailWord_2961558, baseEnd_2961558] using wordTrace_append hprefix tailTrace_2961558
  have hstable : (prefixWord ++ tailWord_2961558).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2961558).length < 2 ^ (prefixWord ++ tailWord_2961558).sum := by decide
  have hdescent : baseEnd_2961558 < baseStart_2961558 := by decide
  rcases family_descends (prefixWord ++ tailWord_2961558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2961608 : List Nat := [2, 1, 3, 1, 2, 1, 1, 6, 5]
def baseStart_2961608 : Nat := 118140960795 + 2961608 * 2 ^ 59
def prefixEnd_2961608 : Nat := 4983230072969 + 3 ^ 40 * 2961608 * 2
def baseEnd_2961608 : Nat := 337939647600211984173293

theorem tailTrace_2961608 : CollatzResearch.WordTrace tailWord_2961608 prefixEnd_2961608 337939647600211984173293 := by
  unfold tailWord_2961608
  simp only [CollatzResearch.WordTrace]
  refine ⟨54009358927303746611262739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72012478569738328815016985 54009358927303746611262739)
  ·
    refine ⟨81014038390955619916894109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54009358927303746611262739 81014038390955619916894109)
    ·
      refine ⟨30380264396608357468835291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 81014038390955619916894109 30380264396608357468835291)
      ·
        refine ⟨45570396594912536203252937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30380264396608357468835291 45570396594912536203252937)
        ·
          refine ⟨34177797446184402152439703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45570396594912536203252937 34177797446184402152439703)
          ·
            refine ⟨51266696169276603228659555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34177797446184402152439703 51266696169276603228659555)
            ·
              refine ⟨76900044253914904842989333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51266696169276603228659555 76900044253914904842989333)
              ·
                refine ⟨3604689574402261164515125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 76900044253914904842989333 3604689574402261164515125)
                ·
                  refine ⟨337939647600211984173293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3604689574402261164515125 337939647600211984173293)
                  ·
                    rfl

theorem cell22_2961608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 6, 5].length) (baseStart_2961608 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2961608 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2961608 prefixEnd_2961608 := by exact prefixLift 2961608
  have htrace : WordTrace (prefixWord ++ tailWord_2961608) baseStart_2961608 baseEnd_2961608 := by
    simpa [prefixWord, tailWord_2961608, baseEnd_2961608] using wordTrace_append hprefix tailTrace_2961608
  have hstable : (prefixWord ++ tailWord_2961608).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2961608).length < 2 ^ (prefixWord ++ tailWord_2961608).sum := by decide
  have hdescent : baseEnd_2961608 < baseStart_2961608 := by decide
  rcases family_descends (prefixWord ++ tailWord_2961608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2961625 : List Nat := [1, 2, 1, 2, 3, 1, 6, 1, 5]
def baseStart_2961625 : Nat := 118140960795 + 2961625 * 2 ^ 59
def prefixEnd_2961625 : Nat := 4983230072969 + 3 ^ 40 * 2961625 * 2
def baseEnd_2961625 : Nat := 337941587416017858281609

theorem tailTrace_2961625 : CollatzResearch.WordTrace tailWord_2961625 prefixEnd_2961625 337941587416017858281609 := by
  unfold tailWord_2961625
  simp only [CollatzResearch.WordTrace]
  refine ⟨108019337895545905125894329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72012891930363936750596219 108019337895545905125894329)
  ·
    refine ⟨81014503421659428844420747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108019337895545905125894329 81014503421659428844420747)
    ·
      refine ⟨121521755132489143266631121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81014503421659428844420747 121521755132489143266631121)
      ·
        refine ⟨91141316349366857449973341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 121521755132489143266631121 91141316349366857449973341)
        ·
          refine ⟨34177993631012571543740003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 91141316349366857449973341 34177993631012571543740003)
          ·
            refine ⟨51266990446518857315610005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34177993631012571543740003 51266990446518857315610005)
            ·
              refine ⟨2403140177180571436669219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 51266990446518857315610005 2403140177180571436669219)
              ·
                refine ⟨3604710265770857155003829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2403140177180571436669219 3604710265770857155003829)
                ·
                  refine ⟨337941587416017858281609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3604710265770857155003829 337941587416017858281609)
                  ·
                    rfl

theorem cell22_2961625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 6, 1, 5].length) (baseStart_2961625 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2961625 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2961625 prefixEnd_2961625 := by exact prefixLift 2961625
  have htrace : WordTrace (prefixWord ++ tailWord_2961625) baseStart_2961625 baseEnd_2961625 := by
    simpa [prefixWord, tailWord_2961625, baseEnd_2961625] using wordTrace_append hprefix tailTrace_2961625
  have hstable : (prefixWord ++ tailWord_2961625).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2961625).length < 2 ^ (prefixWord ++ tailWord_2961625).sum := by decide
  have hdescent : baseEnd_2961625 < baseStart_2961625 := by decide
  rcases family_descends (prefixWord ++ tailWord_2961625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2961683 : List Nat := [1, 1, 1, 2, 1, 3, 1, 4, 4, 4]
def baseStart_2961683 : Nat := 118140960795 + 2961683 * 2 ^ 59
def prefixEnd_2961683 : Nat := 4983230072969 + 3 ^ 40 * 2961683 * 2
def baseEnd_2961683 : Nat := 1013844616833360756894649

theorem tailTrace_2961683 : CollatzResearch.WordTrace tailWord_2961683 prefixEnd_2961683 1013844616833360756894649 := by
  unfold tailWord_2961683
  simp only [CollatzResearch.WordTrace]
  refine ⟨108021453329335781031505703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72014302219557187354337135 108021453329335781031505703)
  ·
    refine ⟨162032179994003671547258555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108021453329335781031505703 162032179994003671547258555)
    ·
      refine ⟨243048269991005507320887833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 162032179994003671547258555 243048269991005507320887833)
      ·
        refine ⟨182286202493254130490665875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 243048269991005507320887833 182286202493254130490665875)
        ·
          refine ⟨273429303739881195735998813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 182286202493254130490665875 273429303739881195735998813)
          ·
            refine ⟨102535988902455448400999555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 273429303739881195735998813 102535988902455448400999555)
            ·
              refine ⟨153803983353683172601499333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 102535988902455448400999555 153803983353683172601499333)
              ·
                refine ⟨28838246878815594862781125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 153803983353683172601499333 28838246878815594862781125)
                ·
                  refine ⟨5407171289777924036771461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28838246878815594862781125 5407171289777924036771461)
                  ·
                    refine ⟨1013844616833360756894649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5407171289777924036771461 1013844616833360756894649)
                    ·
                      rfl

theorem cell22_2961683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 4, 4, 4].length) (baseStart_2961683 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2961683 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2961683 prefixEnd_2961683 := by exact prefixLift 2961683
  have htrace : WordTrace (prefixWord ++ tailWord_2961683) baseStart_2961683 baseEnd_2961683 := by
    simpa [prefixWord, tailWord_2961683, baseEnd_2961683] using wordTrace_append hprefix tailTrace_2961683
  have hstable : (prefixWord ++ tailWord_2961683).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2961683).length < 2 ^ (prefixWord ++ tailWord_2961683).sum := by decide
  have hdescent : baseEnd_2961683 < baseStart_2961683 := by decide
  rcases family_descends (prefixWord ++ tailWord_2961683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2961700 : List Nat := [2, 3, 1, 3, 1, 3, 1, 1, 1, 6]
def baseStart_2961700 : Nat := 118140960795 + 2961700 * 2 ^ 59
def prefixEnd_2961700 : Nat := 4983230072969 + 3 ^ 40 * 2961700 * 2
def baseEnd_2961700 : Nat := 1013850436280778379219597

theorem tailTrace_2961700 : CollatzResearch.WordTrace tailWord_2961700 prefixEnd_2961700 1013850436280778379219597 := by
  unfold tailWord_2961700
  simp only [CollatzResearch.WordTrace]
  refine ⟨54011036685137096467437277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72014715580182795289916369 54011036685137096467437277)
  ·
    refine ⟨20254138756926411175288979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54011036685137096467437277 20254138756926411175288979)
    ·
      refine ⟨30381208135389616762933469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20254138756926411175288979 30381208135389616762933469)
      ·
        refine ⟨11392953050771106286100051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30381208135389616762933469 11392953050771106286100051)
        ·
          refine ⟨17089429576156659429150077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11392953050771106286100051 17089429576156659429150077)
          ·
            refine ⟨6408536091058747285931279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17089429576156659429150077 6408536091058747285931279)
            ·
              refine ⟨9612804136588120928896919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6408536091058747285931279 9612804136588120928896919)
              ·
                refine ⟨14419206204882181393345379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9612804136588120928896919 14419206204882181393345379)
                ·
                  refine ⟨21628809307323272090018069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14419206204882181393345379 21628809307323272090018069)
                  ·
                    refine ⟨1013850436280778379219597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21628809307323272090018069 1013850436280778379219597)
                    ·
                      rfl

theorem cell22_2961700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 3, 1, 1, 1, 6].length) (baseStart_2961700 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2961700 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2961700 prefixEnd_2961700 := by exact prefixLift 2961700
  have htrace : WordTrace (prefixWord ++ tailWord_2961700) baseStart_2961700 baseEnd_2961700 := by
    simpa [prefixWord, tailWord_2961700, baseEnd_2961700] using wordTrace_append hprefix tailTrace_2961700
  have hstable : (prefixWord ++ tailWord_2961700).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2961700).length < 2 ^ (prefixWord ++ tailWord_2961700).sum := by decide
  have hdescent : baseEnd_2961700 < baseStart_2961700 := by decide
  rcases family_descends (prefixWord ++ tailWord_2961700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2961704 : List Nat := [2, 1, 5, 1, 3, 1, 2, 3, 4]
def baseStart_2961704 : Nat := 118140960795 + 2961704 * 2 ^ 59
def prefixEnd_2961704 : Nat := 4983230072969 + 3 ^ 40 * 2961704 * 2
def baseEnd_2961704 : Nat := 337950601854174567373195

theorem tailTrace_2961704 : CollatzResearch.WordTrace tailWord_2961704 prefixEnd_2961704 337950601854174567373195 := by
  unfold tailWord_2961704
  simp only [CollatzResearch.WordTrace]
  refine ⟨54011109631129850809010083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72014812841506467745346777 54011109631129850809010083)
  ·
    refine ⟨81016664446694776213515125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54011109631129850809010083 81016664446694776213515125)
    ·
      refine ⟨7595312291877635270017043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 81016664446694776213515125 7595312291877635270017043)
      ·
        refine ⟨11392968437816452905025565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7595312291877635270017043 11392968437816452905025565)
        ·
          refine ⟨4272363164181169839384587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11392968437816452905025565 4272363164181169839384587)
          ·
            refine ⟨6408544746271754759076881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4272363164181169839384587 6408544746271754759076881)
            ·
              refine ⟨4806408559703816069307661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6408544746271754759076881 4806408559703816069307661)
              ·
                refine ⟨1802403209888931025990373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4806408559703816069307661 1802403209888931025990373)
                ·
                  refine ⟨337950601854174567373195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1802403209888931025990373 337950601854174567373195)
                  ·
                    rfl

theorem cell22_2961704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 1, 2, 3, 4].length) (baseStart_2961704 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2961704 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2961704 prefixEnd_2961704 := by exact prefixLift 2961704
  have htrace : WordTrace (prefixWord ++ tailWord_2961704) baseStart_2961704 baseEnd_2961704 := by
    simpa [prefixWord, tailWord_2961704, baseEnd_2961704] using wordTrace_append hprefix tailTrace_2961704
  have hstable : (prefixWord ++ tailWord_2961704).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2961704).length < 2 ^ (prefixWord ++ tailWord_2961704).sum := by decide
  have hdescent : baseEnd_2961704 < baseStart_2961704 := by decide
  rcases family_descends (prefixWord ++ tailWord_2961704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2961706 : List Nat := [3, 1, 4, 2, 2, 2, 2, 1, 1, 4]
def baseStart_2961706 : Nat := 118140960795 + 2961706 * 2 ^ 59
def prefixEnd_2961706 : Nat := 4983230072969 + 3 ^ 40 * 2961706 * 2
def baseEnd_2961706 : Nat := 1013852490203396363569579

theorem tailTrace_2961706 : CollatzResearch.WordTrace tailWord_2961706 prefixEnd_2961706 1013852490203396363569579 := by
  unfold tailWord_2961706
  simp only [CollatzResearch.WordTrace]
  refine ⟨27005573052063113989898243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72014861472168303973061981 27005573052063113989898243)
  ·
    refine ⟨40508359578094670984847365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27005573052063113989898243 40508359578094670984847365)
    ·
      refine ⟨7595317420892750809658881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 40508359578094670984847365 7595317420892750809658881)
      ·
        refine ⟨5696488065669563107244161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7595317420892750809658881 5696488065669563107244161)
        ·
          refine ⟨4272366049252172330433121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5696488065669563107244161 4272366049252172330433121)
          ·
            refine ⟨3204274536939129247824841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4272366049252172330433121 3204274536939129247824841)
            ·
              refine ⟨2403205902704346935868631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3204274536939129247824841 2403205902704346935868631)
              ·
                refine ⟨3604808854056520403802947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2403205902704346935868631 3604808854056520403802947)
                ·
                  refine ⟨5407213281084780605704421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3604808854056520403802947 5407213281084780605704421)
                  ·
                    refine ⟨1013852490203396363569579, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5407213281084780605704421 1013852490203396363569579)
                    ·
                      rfl

theorem cell22_2961706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 2, 2, 1, 1, 4].length) (baseStart_2961706 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2961706 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2961706 prefixEnd_2961706 := by exact prefixLift 2961706
  have htrace : WordTrace (prefixWord ++ tailWord_2961706) baseStart_2961706 baseEnd_2961706 := by
    simpa [prefixWord, tailWord_2961706, baseEnd_2961706] using wordTrace_append hprefix tailTrace_2961706
  have hstable : (prefixWord ++ tailWord_2961706).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2961706).length < 2 ^ (prefixWord ++ tailWord_2961706).sum := by decide
  have hdescent : baseEnd_2961706 < baseStart_2961706 := by decide
  rcases family_descends (prefixWord ++ tailWord_2961706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2961728 : List Nat := [2, 1, 1, 2, 2, 1, 2, 3, 2, 6]
def baseStart_2961728 : Nat := 118140960795 + 2961728 * 2 ^ 59
def prefixEnd_2961728 : Nat := 4983230072969 + 3 ^ 40 * 2961728 * 2
def baseEnd_2961728 : Nat := 1013860021252995639519511

theorem tailTrace_2961728 : CollatzResearch.WordTrace tailWord_2961728 prefixEnd_2961728 1013860021252995639519511 := by
  unfold tailWord_2961728
  simp only [CollatzResearch.WordTrace]
  refine ⟨54011547307086376858446919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72015396409448502477929225 54011547307086376858446919)
  ·
    refine ⟨81017320960629565287670379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54011547307086376858446919 81017320960629565287670379)
    ·
      refine ⟨121525981440944347931505569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81017320960629565287670379 121525981440944347931505569)
      ·
        refine ⟨91144486080708260948629177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 121525981440944347931505569 91144486080708260948629177)
        ·
          refine ⟨68358364560531195711471883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 91144486080708260948629177 68358364560531195711471883)
          ·
            refine ⟨102537546840796793567207825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68358364560531195711471883 102537546840796793567207825)
            ·
              refine ⟨76903160130597595175405869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 102537546840796793567207825 76903160130597595175405869)
              ·
                refine ⟨28838685048974098190777201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 76903160130597595175405869 28838685048974098190777201)
                ·
                  refine ⟨21629013786730573643082901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28838685048974098190777201 21629013786730573643082901)
                  ·
                    refine ⟨1013860021252995639519511, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21629013786730573643082901 1013860021252995639519511)
                    ·
                      rfl

theorem cell22_2961728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 3, 2, 6].length) (baseStart_2961728 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2961728 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2961728 prefixEnd_2961728 := by exact prefixLift 2961728
  have htrace : WordTrace (prefixWord ++ tailWord_2961728) baseStart_2961728 baseEnd_2961728 := by
    simpa [prefixWord, tailWord_2961728, baseEnd_2961728] using wordTrace_append hprefix tailTrace_2961728
  have hstable : (prefixWord ++ tailWord_2961728).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2961728).length < 2 ^ (prefixWord ++ tailWord_2961728).sum := by decide
  have hdescent : baseEnd_2961728 < baseStart_2961728 := by decide
  rcases family_descends (prefixWord ++ tailWord_2961728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2961749 : List Nat := [1, 3, 2, 2, 5, 1, 2, 6]
def baseStart_2961749 : Nat := 118140960795 + 2961749 * 2 ^ 59
def prefixEnd_2961749 : Nat := 4983230072969 + 3 ^ 40 * 2961749 * 2
def baseEnd_2961749 : Nat := 112651912220239842749383

theorem tailTrace_2961749 : CollatzResearch.WordTrace tailWord_2961749 prefixEnd_2961749 112651912220239842749383 := by
  unfold tailWord_2961749
  simp only [CollatzResearch.WordTrace]
  refine ⟨108023860547096674303408301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72015907031397782868938867 108023860547096674303408301)
  ·
    refine ⟨40508947705161252863778113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 108023860547096674303408301 40508947705161252863778113)
    ·
      refine ⟨30381710778870939647833585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40508947705161252863778113 30381710778870939647833585)
      ·
        refine ⟨22786283084153204735875189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30381710778870939647833585 22786283084153204735875189)
        ·
          refine ⟨2136214039139362943988299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 22786283084153204735875189 2136214039139362943988299)
          ·
            refine ⟨3204321058709044415982449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2136214039139362943988299 3204321058709044415982449)
            ·
              refine ⟨2403240794031783311986837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3204321058709044415982449 2403240794031783311986837)
              ·
                refine ⟨112651912220239842749383, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2403240794031783311986837 112651912220239842749383)
                ·
                  rfl

theorem cell22_2961749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 5, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 5, 1, 2, 6].length) (baseStart_2961749 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2961749 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2961749 prefixEnd_2961749 := by exact prefixLift 2961749
  have htrace : WordTrace (prefixWord ++ tailWord_2961749) baseStart_2961749 baseEnd_2961749 := by
    simpa [prefixWord, tailWord_2961749, baseEnd_2961749] using wordTrace_append hprefix tailTrace_2961749
  have hstable : (prefixWord ++ tailWord_2961749).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2961749).length < 2 ^ (prefixWord ++ tailWord_2961749).sum := by decide
  have hdescent : baseEnd_2961749 < baseStart_2961749 := by decide
  rcases family_descends (prefixWord ++ tailWord_2961749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2961824 : List Nat := [2, 1, 1, 4, 1, 4, 3, 1, 1, 4]
def baseStart_2961824 : Nat := 118140960795 + 2961824 * 2 ^ 59
def prefixEnd_2961824 : Nat := 4983230072969 + 3 ^ 40 * 2961824 * 2
def baseEnd_2961824 : Nat := 1013892884014883389119217

theorem tailTrace_2961824 : CollatzResearch.WordTrace tailWord_2961824 prefixEnd_2961824 1013892884014883389119217 := by
  unfold tailWord_2961824
  simp only [CollatzResearch.WordTrace]
  refine ⟨54013298010912481056194263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72017730681216641408259017 54013298010912481056194263)
  ·
    refine ⟨81019947016368721584291395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54013298010912481056194263 81019947016368721584291395)
    ·
      refine ⟨121529920524553082376437093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81019947016368721584291395 121529920524553082376437093)
      ·
        refine ⟨22786860098353702945581955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 121529920524553082376437093 22786860098353702945581955)
        ·
          refine ⟨34180290147530554418372933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22786860098353702945581955 34180290147530554418372933)
          ·
            refine ⟨6408804402661978953444925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 34180290147530554418372933 6408804402661978953444925)
            ·
              refine ⟨2403301650998242107541847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6408804402661978953444925 2403301650998242107541847)
              ·
                refine ⟨3604952476497363161312771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2403301650998242107541847 3604952476497363161312771)
                ·
                  refine ⟨5407428714746044741969157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3604952476497363161312771 5407428714746044741969157)
                  ·
                    refine ⟨1013892884014883389119217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5407428714746044741969157 1013892884014883389119217)
                    ·
                      rfl

theorem cell22_2961824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 4, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 4, 3, 1, 1, 4].length) (baseStart_2961824 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2961824 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2961824 prefixEnd_2961824 := by exact prefixLift 2961824
  have htrace : WordTrace (prefixWord ++ tailWord_2961824) baseStart_2961824 baseEnd_2961824 := by
    simpa [prefixWord, tailWord_2961824, baseEnd_2961824] using wordTrace_append hprefix tailTrace_2961824
  have hstable : (prefixWord ++ tailWord_2961824).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2961824).length < 2 ^ (prefixWord ++ tailWord_2961824).sum := by decide
  have hdescent : baseEnd_2961824 < baseStart_2961824 := by decide
  rcases family_descends (prefixWord ++ tailWord_2961824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2961854 : List Nat := [4, 2, 1, 1, 1, 1, 4, 3, 2, 3]
def baseStart_2961854 : Nat := 118140960795 + 2961854 * 2 ^ 59
def prefixEnd_2961854 : Nat := 4983230072969 + 3 ^ 40 * 2961854 * 2
def baseEnd_2961854 : Nat := 1013903153627973310869125

theorem tailTrace_2961854 : CollatzResearch.WordTrace tailWord_2961854 prefixEnd_2961854 1013903153627973310869125 := by
  unfold tailWord_2961854
  simp only [CollatzResearch.WordTrace]
  refine ⟨13503461276464534654497577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 72018460141144184823987077 13503461276464534654497577)
  ·
    refine ⟨10127595957348400990873183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13503461276464534654497577 10127595957348400990873183)
    ·
      refine ⟨15191393936022601486309775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10127595957348400990873183 15191393936022601486309775)
      ·
        refine ⟨22787090904033902229464663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15191393936022601486309775 22787090904033902229464663)
        ·
          refine ⟨34180636356050853344196995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22787090904033902229464663 34180636356050853344196995)
          ·
            refine ⟨51270954534076280016295493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34180636356050853344196995 51270954534076280016295493)
            ·
              refine ⟨9613303975139302503055405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 51270954534076280016295493 9613303975139302503055405)
              ·
                refine ⟨3604988990677238438645777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9613303975139302503055405 3604988990677238438645777)
                ·
                  refine ⟨2703741743007928828984333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3604988990677238438645777 2703741743007928828984333)
                  ·
                    refine ⟨1013903153627973310869125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2703741743007928828984333 1013903153627973310869125)
                    ·
                      rfl

theorem cell22_2961854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 4, 3, 2, 3].length) (baseStart_2961854 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2961854 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2961854 prefixEnd_2961854 := by exact prefixLift 2961854
  have htrace : WordTrace (prefixWord ++ tailWord_2961854) baseStart_2961854 baseEnd_2961854 := by
    simpa [prefixWord, tailWord_2961854, baseEnd_2961854] using wordTrace_append hprefix tailTrace_2961854
  have hstable : (prefixWord ++ tailWord_2961854).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2961854).length < 2 ^ (prefixWord ++ tailWord_2961854).sum := by decide
  have hdescent : baseEnd_2961854 < baseStart_2961854 := by decide
  rcases family_descends (prefixWord ++ tailWord_2961854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2961882 : List Nat := [3, 1, 1, 2, 3, 1, 1, 2, 5, 3]
def baseStart_2961882 : Nat := 118140960795 + 2961882 * 2 ^ 59
def prefixEnd_2961882 : Nat := 4983230072969 + 3 ^ 40 * 2961882 * 2
def baseEnd_2961882 : Nat := 1013912738600190571169039

theorem tailTrace_2961882 : CollatzResearch.WordTrace tailWord_2961882 prefixEnd_2961882 1013912738600190571169039 := by
  unfold tailWord_2961882
  simp only [CollatzResearch.WordTrace]
  refine ⟨27007177863903709504499975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72019140970409892011999933 27007177863903709504499975)
  ·
    refine ⟨40510766795855564256749963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27007177863903709504499975 40510766795855564256749963)
    ·
      refine ⟨60766150193783346385124945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40510766795855564256749963 60766150193783346385124945)
      ·
        refine ⟨45574612645337509788843709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60766150193783346385124945 45574612645337509788843709)
        ·
          refine ⟨17090479742001566170816391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45574612645337509788843709 17090479742001566170816391)
          ·
            refine ⟨25635719613002349256224587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17090479742001566170816391 25635719613002349256224587)
            ·
              refine ⟨38453579419503523884336881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25635719613002349256224587 38453579419503523884336881)
              ·
                refine ⟨28840184564627642913252661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38453579419503523884336881 28840184564627642913252661)
                ·
                  refine ⟨2703767302933841523117437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 28840184564627642913252661 2703767302933841523117437)
                  ·
                    refine ⟨1013912738600190571169039, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2703767302933841523117437 1013912738600190571169039)
                    ·
                      rfl

theorem cell22_2961882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 1, 2, 5, 3].length) (baseStart_2961882 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2961882 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2961882 prefixEnd_2961882 := by exact prefixLift 2961882
  have htrace : WordTrace (prefixWord ++ tailWord_2961882) baseStart_2961882 baseEnd_2961882 := by
    simpa [prefixWord, tailWord_2961882, baseEnd_2961882] using wordTrace_append hprefix tailTrace_2961882
  have hstable : (prefixWord ++ tailWord_2961882).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2961882).length < 2 ^ (prefixWord ++ tailWord_2961882).sum := by decide
  have hdescent : baseEnd_2961882 < baseStart_2961882 := by decide
  rcases family_descends (prefixWord ++ tailWord_2961882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
